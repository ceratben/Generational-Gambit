// Replacement mem.c featuring a generational garbage collector.


/* Includes */
#define ___INCLUDED_FROM_MEM
#define ___VERSION 406006
#include "gambit.h"

#include "os_base.h"
#include "os_time.h"
#include "setup.h"
#include "mem.h"
#include "c_intf.h"

/* The following includes are needed for debugging. */

#include <stdlib.h>
#include <string.h>

/*---------------------------------------------------------------------------*/

/* Constants related to representation of permanent and still objects: */

#ifdef ___USE_HANDLES
#define ___PERM_HAND_OFS 0
#define ___PERM_BODY_OFS 2
#else
#define ___PERM_HAND_OFS ___PERM_BODY_OFS
#define ___PERM_BODY_OFS 1
#endif

#define ___STILL_LINK_OFS 0
#define ___STILL_REFCOUNT_OFS 1
#define ___STILL_LENGTH_OFS 2
#define ___STILL_MARK_OFS 3
#ifdef ___USE_HANDLES
#define ___STILL_HAND_OFS 4
#define ___STILL_BODY_OFS 6
#else
#define ___STILL_HAND_OFS ___STILL_BODY_OFS
#define ___STILL_BODY_OFS (5+1)/************/
#endif


___HIDDEN long words_nonmovable;
___HIDDEN long overflow_reserve;
___HIDDEN long normal_overflow_reserve;
___HIDDEN long heap_size;
___HIDDEN long stack_size;

/**********************************/
/* Macros useful to the GC */

#define ___POINTER_MASK (~0 - 3)
#define ___UNTAG_POINTER(x) (x & ___POINTER_MASK)
#define ___POINTER_TAG(x) (x & 0x3)
#define ___TAG_POINTER(p, tag) (((___WORD) p)|tag)
#define ___IS_POINTER(x) (x & 0x1)

#define ___GET_GEN(hd) ___HD_TYP(hd)
#define ___PROMOTE(hd) (hd + 1)
#define ___HEAD(x) x[-1]
#define ___TAGBIT 4 // 9th bit in header.
#define ___IS_MARKED(hd) (hd & ___TAGBIT)
#define ___MARKP(p) (p | ___TAGBIT)
#define ___SCMOBJ_SIZE(hd) ___HD_WORDS(hd)//(hd>>9)
#define ___TAGMOVABLE(p) p[-1]|=___TAGBIT;
#define ___LIVE(ptr, g) ((ptr >= g->fromspace && ptr <= g->alloc) || \
                         (ptr <= g->fromspace && ptr >= g->alloc))

#define ___TOTAL_SIZE(g) (g->mem->nb_sections*___MSECTION_SIZE/2)
#define ___OLD_SIZE(g) g->old_size
#define ___USED_MEM(g) ___used_mem(g)
#define ___YOUNG_SIZE(g) (___USED_MEM(g) - ___OLD_SIZE(g))
#define ___FREE_MEM(g) (___TOTAL_SIZE(g) - ___USED_MEM(g))
#define WORDS_MOVABLE (___USED_MEM(gen0) + ___USED_MEM(gen1))
#define WORDS_OCCUPIED (WORDS_MOVABLE + words_nonmovable)
/**********************************/

/*
 * Movable Scheme objects are allocated in an area of memory
 * distributed in multiple noncontiguous sections (collectively
 * called the "msections").  All sections are of the same size and are
 * allocated through the '___alloc_mem' function.  The number of
 * sections can expand and contract to accommodate the needs of the
 * program.
 */

typedef struct msect
  {
    int index;          /* index in list of sections */
    int pos;            /* position in msections's 'sections' array */
    ___WORD *alloc;     /* heap allocation pointer, grows towards high addr. */
    struct msect *prev; /* previous section in list of sections */
    struct msect *next; /* next section in list of sections */
    ___WORD base[1];    /* content of section */
  } msection;

#define sizeof_msection(n) (sizeof (msection) + ((n)-1) * ___WS)

typedef struct
  {
    int max_nb_sections;   /* actual size of 'sections' array */
    int nb_sections;       /* number of sections */
    int used;         /* Pointer to the next object ot scan */
    msection *head;        /* head of doubly-linked list of sections */
    msection *tail;        /* tail of doubly-linked list of sections */
    msection *sections[1]; /* each section ordered by address */
                           /* (increasing order if ___ALLOC_MEM_UP */
                           /* is defined otherwise decreasing order) */
  } msections;

#define sizeof_msections(n) (sizeof (msections) + ((n)-1) * sizeof (msection*))

/**********************************/

typedef struct rset {

  ___WORD ** rs;                   // List of address in the remembered set.
  ___WORD ** current;
  ___WORD ** end;
  ___WORD count;
  
} remset;

typedef struct gen {

  struct gen * next, * previous;

  int index;
  long old_size;
  int start;
  ___WORD * tospace;
  ___WORD * fromspace;
  ___WORD * scan;
  ___WORD * old;
  ___WORD * alloc;

  remset * rs;
  int current_index;
  msection * current;
  msections * mem;

} generation;

#define ssb_size 1024

typedef struct {
  ___WORD ** end, ** last;
  ___WORD * buffer[ssb_size];
} SSB_struct;

/**********************************/

/* list of still objects */
___HIDDEN ___WORD still_objs;

/* still objects remaining to scan */
___HIDDEN ___WORD still_objs_to_scan;

/* last msection allocated */
___HIDDEN msection *alloc_msection;

/* msection where continuation frames are currently being allocated */
___HIDDEN msection *stack_msection;

/* List of all allocated msections */
___HIDDEN msections *the_msections;

/* number of msections used */
___HIDDEN int nb_msections_used;

/* start of allocation of continuation frames in stack_msection */
___HIDDEN ___WORD *alloc_stack_start;

/* allocation pointer for continuation frames in stack_msection */
___HIDDEN ___WORD *alloc_stack_ptr;

/* allocation limit for continuation frames in stack_msection */
___HIDDEN ___WORD *alloc_stack_limit;

/* allocation pointer for movable objects in heap_msection */
___HIDDEN ___WORD *alloc_heap_ptr;

/* allocation limit for movable objects in heap_msection */
___HIDDEN ___WORD *alloc_heap_limit;

/* indicates if weak references must be traversed */
___HIDDEN ___BOOL traverse_weak_refs;

/* GC hash tables reached by GC */
___HIDDEN ___WORD reached_gc_hash_tables;

/**********************************/

generation *gen0 = NULL, *gen1 = NULL;
SSB_struct * SSB = NULL;
msections * stack = 0;
int full_collect_flag = 0;


long ___used_mem(generation * g) {
  //printf("Begin used_mem\n");
  long t = 0;
  int pos = g->start;
  msection * start = g->mem->sections[pos];
  while(pos++ < g->current_index) {
    t += start->alloc - start->base;
    start = g->mem->sections[pos];
  }
  t += g->alloc - g->current->base;

  if(g == gen0) {
    /* Include stack */
    t += alloc_stack_start - alloc_stack_ptr;
  }

  return t;
}


/*********************************/

/*---------------------------------------------------------------------------*/

/* Allocation and reclamation of aligned blocks of memory.  */


/*
 * 'alloc_mem_aligned (words, multiplier, modulus)' allocates an
 * aligned block of memory through the '___alloc_mem' function.
 * 'words' is the size of the block in words and 'multiplier' and
 * 'modulus' specify its alignment in words.  'multiplier' must be a
 * power of two and 0<=modulus<multiplier.  The pointer returned
 * corresponds to an address that is equal to
 * (i*multiplier+modulus)*sizeof (___WORD) for some 'i'.
 */

___HIDDEN void *alloc_mem_aligned
   ___P((long words,
         unsigned int multiplier,
         unsigned int modulus),
        (words,
         multiplier,
         modulus)
long words;
unsigned int multiplier;
unsigned int modulus;)
{
  void *container; /* pointer to block returned by ___alloc_mem */
  unsigned int extra; /* space for alignment to multiplier */

  /* Make sure alignment is sufficient for pointers */

  if (multiplier < sizeof (void*) / ___WS)
    multiplier = sizeof (void*) / ___WS;

  /* How many extra bytes are needed for padding */

  extra = (multiplier * ___WS) - 1;
  if (modulus < sizeof (void*) / ___WS)
    extra += sizeof (void*);

  container = ___alloc_mem (extra + (words+modulus) * ___WS);

  if (container == 0)
    return 0;
  else
    {
      void *ptr = ___CAST(void*,
                          (((___CAST(___WORD,container) + extra) &
                            -___CAST(___WORD,multiplier * ___WS)) +
                           modulus * ___WS));
      void **cptr = ___CAST(void**,
                            (___CAST(___WORD,ptr) - ___CAST(___WORD,sizeof (void*))) &
                            -___CAST(___WORD,sizeof (void*)));

      *cptr = container;
      return ptr;
    }
}


/*
 * 'free_mem_aligned (ptr)' reclaims the aligned block of memory 'ptr'
 * that was allocated using 'alloc_mem_aligned'.
 */

___HIDDEN void free_mem_aligned
   ___P((void *ptr),
        (ptr)
void *ptr;)
{
  void **cptr = ___CAST(void**,
                        (___CAST(___WORD,ptr) - ___CAST(___WORD,sizeof (void*))) &
                        -___CAST(___WORD,sizeof (void*)));
  ___free_mem (*cptr);
}

/* Allocation of reference counted blocks of memory. */

typedef struct rc_header_struct
  {
    struct rc_header_struct *prev;
    struct rc_header_struct *next;
    ___SCMOBJ refcount; /* integer but declared ___SCMOBJ for alignment */
    ___SCMOBJ data; /* needed for C closures */
  } rc_header;


___HIDDEN rc_header rc_head;


___HIDDEN void setup_rc ___PVOID
{
  rc_head.prev = &rc_head;
  rc_head.next = &rc_head;
  rc_head.refcount = 1;
  rc_head.data = ___FAL;
}

___HIDDEN void cleanup_rc ___PVOID
{
  rc_header *h = rc_head.next;

  rc_head.prev = &rc_head;
  rc_head.next = &rc_head;

  while (h != &rc_head)
    {
      rc_header *next = h->next;
      ___free_mem (h);
      h = next;
    }
}


___EXP_FUNC(void*,___alloc_rc)
   ___P((unsigned long bytes),
        (bytes)
unsigned long bytes;)
{
  rc_header *h = ___CAST(rc_header*,
                         ___alloc_mem (bytes + sizeof (rc_header)));

  if (h != 0)
    {
      rc_header *head = &rc_head;
      rc_header *tail = head->prev;

      h->prev = tail;
      h->next = head;
      head->prev = h;
      tail->next = h;

      h->refcount = 1;
      h->data = ___FAL;

      return ___CAST(void*,h+1);
    }

  return 0;
}


___EXP_FUNC(void,___release_rc)
   ___P((void *ptr),
        (ptr)
void *ptr;)
{
  if (ptr != 0)
    {
      rc_header *h = ___CAST(rc_header*,ptr) - 1;

      if (--h->refcount == 0)
        {
          rc_header *prev = h->prev;
          rc_header *next = h->next;

          next->prev = prev;
          prev->next = next;

          ___free_mem (h);
        }
    }
}


___EXP_FUNC(void,___addref_rc)
   ___P((void *ptr),
        (ptr)
void *ptr;)
{
  if (ptr != 0)
    {
      rc_header *h = ___CAST(rc_header*,ptr) - 1;
      h->refcount++;
    }
}


___EXP_FUNC(___SCMOBJ,___data_rc)
   ___P((void *ptr),
        (ptr)
void *ptr;)
{
  rc_header *h = ___CAST(rc_header*,ptr) - 1;
  return h->data;
}


___EXP_FUNC(void,___set_data_rc)
   ___P((void *ptr,
         ___SCMOBJ val),
        (ptr,
         val)
void *ptr;
___SCMOBJ val;)
{
  rc_header *h = ___CAST(rc_header*,ptr) - 1;
  h->data = val;
}



/*********************************/

/*---------------------------------------------------------------------------*/

/* Allocation of permanent objects.  */

/*
 * Permanent objects are allocated in sections called "psections".
 * Each section contains multiple objects.  The sections are kept in a
 * list so that the storage they occupy can be reclaimed when the
 * program terminates.
 */

___HIDDEN void *psections;       /* list of psections */
___HIDDEN ___WORD *palloc_ptr;   /* allocation pointer in current psection */
___HIDDEN ___WORD *palloc_limit; /* allocation limit in current psection */


/*
 * 'alloc_mem_aligned_psection (words, multiplier, modulus)' allocates
 * an aligned block of memory inside a new psection.  'words' is the
 * size of the block in words and 'multiplier' and 'modulus' specify
 * its alignment in words.  'multiplier' must be a power of two and
 * 0<=modulus<multiplier.  The pointer returned corresponds to an
 * address that is equal to (i*multiplier+modulus)*sizeof (___WORD) for
 * some 'i'.
 */

___HIDDEN void *alloc_mem_aligned_psection
   ___P((long words,
         unsigned int multiplier,
         unsigned int modulus),
        (words,
         multiplier,
         modulus)
long words;
unsigned int multiplier;
unsigned int modulus;)
{
  void *container;

  /* Make sure alignment is sufficient for pointers */

  if (multiplier < sizeof (void*) / ___WS)
    multiplier = sizeof (void*) / ___WS;

  /* Make space for psection link and modulus */

  if (modulus < (sizeof (void*) + ___WS - 1) / ___WS)
    modulus += ((sizeof (void*) + multiplier * ___WS - 1) / ___WS) &
               -multiplier;

  /* Allocate container */

  container = (void *) alloc_mem_aligned (words+modulus, multiplier, 0);

  if (container == 0)
    return 0;

  *___CAST(void**,container) = psections;
  psections = container;
  return ___CAST(void*,___CAST(___WORD*,container) + modulus);
}


/*
 * 'alloc_mem_aligned_perm (words, multiplier, modulus)' allocates an
 * aligned block of memory inside a psection.  If there is enough free
 * space in a previously allocated psection that psection is used,
 * otherwise a new psection is allocated.  'words' is the size of the
 * block in words and 'multiplier' and 'modulus' specify its alignment
 * in words.  'multiplier' must be a power of two and
 * 0<=modulus<multiplier.  The pointer returned corresponds to an
 * address that is equal to (i*multiplier+modulus)*sizeof (___WORD) for
 * some 'i'.
 */

___HIDDEN void *alloc_mem_aligned_perm
   ___P((long words,
         int multiplier,
         int modulus),
        (words,
         multiplier,
         modulus)
long words;
int multiplier;
int modulus;)
{
  long waste;
  ___WORD *base;

  /*
   * Try to satisfy request in current psection.
   */

  if (palloc_ptr != 0)
    {
      ___WORD *new_palloc_ptr;

      base = ___CAST(___WORD*,
                     ___CAST(___WORD,palloc_ptr+multiplier-1-modulus) &
                     (multiplier * -___WS)) +
             modulus;

      new_palloc_ptr = base + words;

      if (new_palloc_ptr <= palloc_limit) /* did it fit in the psection? */
        {
          palloc_ptr = new_palloc_ptr;
          return base;
        }

      waste = palloc_limit - palloc_ptr;
    }
  else
    waste = 0;

  /*
   * Request can't be satisfied in current psection so we must
   * allocate a new psection.
   */

  if (waste > ___PSECTION_WASTE || words > ___PSECTION_SIZE)
    return alloc_mem_aligned_psection (words, multiplier, modulus);

  base = ___CAST(___WORD*,
                 alloc_mem_aligned_psection
                   (___PSECTION_SIZE,
                    multiplier,
                    modulus));

  if (base != 0)
    {
      palloc_ptr = base + words;
      palloc_limit = base + ___PSECTION_SIZE;
    }

  return base;
}


___HIDDEN void free_psections ___PVOID
{
  void *base = psections;

  psections = 0;

  while (base != 0)
    {
      void *link = *___CAST(void**,base);
      free_mem_aligned (base);
      base = link;
    }
}


___SCMOBJ ___alloc_global_var
   ___P((___glo_struct **glo),
        (glo)
___glo_struct **glo;)
{
  ___glo_struct *p = ___CAST(___glo_struct*,
                             alloc_mem_aligned_perm
                               (___WORDS(sizeof (___glo_struct)),
                                1,
                                0));
  if (p == 0)
    return ___FIX(___HEAP_OVERFLOW_ERR);
  *glo = p;
  return ___FIX(___NO_ERR);
}

/*********************************/

/*---------------------------------------------------------------------------*/

/*
 * '___still_obj_refcount_inc (obj)' increments the reference count of
 * the still object 'obj'.
 */

___EXP_FUNC(void,___still_obj_refcount_inc)
   ___P((___WORD obj),
        (obj)
___WORD obj;)
{
  ___UNTAG(obj)[___BODY_OFS - ___STILL_BODY_OFS + ___STILL_REFCOUNT_OFS]++;
}


/*
 * '___still_obj_refcount_dec (obj)' decrements the reference count of
 * the still object 'obj'.
 */

___EXP_FUNC(void,___still_obj_refcount_dec)
   ___P((___WORD obj),
        (obj)
___WORD obj;)
{
  ___UNTAG(obj)[___BODY_OFS - ___STILL_BODY_OFS + ___STILL_REFCOUNT_OFS]--;
}


/*---------------------------------------------------------------------------*/

/*
 * '___alloc_scmobj (subtype, bytes, kind)' allocates a permanent or
 * still Scheme object (depending on 'kind') of subtype 'subtype' with
 * a body containing 'bytes' bytes, and returns it as an encoded
 * Scheme object.  A permanent object is allocated when 'kind' =
 * ___PERM and a still object is allocated when 'kind' = ___STILL.
 * The initialization of the object's body must be done by the caller.
 * In the case of still objects this initialization must be done
 * before the next allocation is requested.  The 'refcount' field of
 * still objects is initially 1.  A fixnum error code is returned when
 * there is an error.
 */

___SCMOBJ ___alloc_scmobj(int subtype, long bytes, int kind) {

  //printf("begin alloc_scmobj\n");
  void *ptr;
  ___processor_state ___ps = ___PSTATE;
  long words = (kind==___PERM ? ___PERM_BODY_OFS : ___STILL_BODY_OFS)
               + ___WORDS(bytes);

  alloc_stack_ptr = ___ps->fp; /* needed by 'WORDS_OCCUPIED' */
  alloc_heap_ptr  = ___ps->hp; /* needed by 'WORDS_OCCUPIED' */

  words_nonmovable += words;

  if(WORDS_OCCUPIED > heap_size) {
    ___BOOL overflow;

    words_nonmovable -= words;
    printf("Before collection\n");
    overflow = ___garbage_collect (words);
    words_nonmovable += words;

    alloc_stack_ptr = ___ps->fp; /* needed by 'WORDS_OCCUPIED' */
    alloc_heap_ptr  = ___ps->hp; /* needed by 'WORDS_OCCUPIED' */

    if (overflow) { //|| WORDS_OCCUPIED > heap_size) {
      words_nonmovable -= words;
      //      printf("WORDS_OCCUPIED: %ld, heap_size: %ld\n", WORDS_OCCUPIED, heap_size);
      //printf("___HEAP_OVERFLOW_ERR\n");
      return ___FIX(___HEAP_OVERFLOW_ERR);
    }
  }

  /*
   * Some objects, such as ___sFOREIGN, ___sS64VECTOR, ___sU64VECTOR,
   * ___sF64VECTOR, ___sFLONUM and ___sBIGNUM, must have a body that
   * is aligned on a multiple of 8 on some machines.  Here, we force
   * alignment to a multiple of 8 even if not necessary in all cases
   * because it is typically more efficient due to a better
   * utilization of the cache.
   */

  if (kind == ___PERM)
    ptr = alloc_mem_aligned_perm (words,
                                  8>>___LWS,
                                  (-___PERM_BODY_OFS)&((8>>___LWS)-1));
  else
    ptr = alloc_mem_aligned (words,
                             8>>___LWS,
                             (-___STILL_BODY_OFS)&((8>>___LWS)-1));

  if (ptr == 0)
    {
      words_nonmovable -= words;
      return ___FIX(___HEAP_OVERFLOW_ERR);
    }
  else if (kind == ___PERM)
    {
      ___WORD *base = ___CAST(___WORD*,ptr);

#ifdef ___USE_HANDLES
      base[___PERM_HAND_OFS] = ___CAST(___WORD,base+___PERM_BODY_OFS-___BODY_OFS);
#endif
      base[___PERM_BODY_OFS-1] = ___MAKE_HD(bytes, subtype, ___PERM);

      return ___TAG((base + ___PERM_HAND_OFS - ___BODY_OFS),
                    (subtype == ___sPAIR ? ___tPAIR : ___tSUBTYPED));
    }
  else
    {
      ___WORD *base = ___CAST(___WORD*,ptr);

      base[___STILL_LINK_OFS] = still_objs;
      still_objs = ___CAST(___WORD,base);
      base[___STILL_REFCOUNT_OFS] = 1;
      base[___STILL_LENGTH_OFS] = words;
#ifdef ___USE_HANDLES
      base[___STILL_HAND_OFS] = ___CAST(___WORD,base+___STILL_BODY_OFS-___BODY_OFS);
#endif
      base[___STILL_BODY_OFS-1] = ___MAKE_HD(bytes, subtype, ___STILL);

      return ___TAG((base + ___STILL_HAND_OFS - ___BODY_OFS),
                    (subtype == ___sPAIR ? ___tPAIR : ___tSUBTYPED));
    }
  //printf("end alloc_scmobj\n");

}

___EXP_FUNC(void,___release_scmobj)
   ___P((___WORD obj),
        (obj)
___WORD obj;)
{
  if (___MEM_ALLOCATED(obj) &&
      ___HD_TYP(___BODY(obj)[-1]) == ___STILL)
    ___still_obj_refcount_dec (obj);
}


/*
 * '___make_pair (car, cdr, kind)' creates a Scheme pair having the
 * values 'car' and 'cdr' in its CAR and CDR fields.  The 'car' and
 * 'cdr' arguments must not be movable objects and any still object
 * must be reachable some other way or have a nonzero refcount.  A
 * permanent or still object is allocated, depending on 'kind'
 * (___PERM for permanent object, ___STILL for still object).  A
 * fixnum error code is returned when there is an error.
 */

___EXP_FUNC(___WORD,___make_pair)
   ___P((___WORD car,
         ___WORD cdr,
         int kind),
        (car,
         cdr,
         kind)
___WORD car;
___WORD cdr;
int kind;)
{
  ___WORD obj = ___alloc_scmobj (___sPAIR, ___PAIR_SIZE<<___LWS, kind);

  if (!___FIXNUMP(obj))
    {
      ___PAIR_CAR(obj) = car;
      ___PAIR_CDR(obj) = cdr;
    }

  return obj;
}


/*
 * '___make_vector (length, init, kind)' creates a Scheme vector of
 * length 'length' and initialized with the value 'init'.  The 'init'
 * argument must not be a movable object and if it is a still object
 * it must be reachable some other way or have a nonzero refcount.  A
 * permanent or still object is allocated, depending on 'kind'
 * (___PERM for permanent object, ___STILL for still object).  A
 * fixnum error code is returned when there is an error.
 */

___EXP_FUNC(___WORD,___make_vector)
   ___P((long length,
         ___WORD init,
         int kind),
        (length,
         init,
         kind)
long length;
___WORD init;
int kind;)
{
  if (length > ___CAST(___WORD,___LMASK >> (___LF+___LWS)))
    return ___FIX(___HEAP_OVERFLOW_ERR);
  else
    {
      ___WORD obj = ___alloc_scmobj (___sVECTOR, length<<___LWS, kind);

      if (!___FIXNUMP(obj))
        {
          int i;
          for (i=0; i<length; i++)
            ___FIELD(obj, i) = init;
        }

      return obj;
    }
}





/*********************************/

/* Allocation of movable objects.  */

generation * find_gen(int i) {
  switch(i) {
  case 0: return gen0;
  case 1: return gen1;
  default: return NULL;
  }
}

int ptr_in_msection(___WORD * ptr, msection * m){
  if(ptr >= m->base && ptr <= m->base+___MSECTION_SIZE) return 1;
  return 0;
}

// TODO: Test coherence
int find_msection(void * ptr, msections * ms) {
  // Binary search in g
  msection **m = ms->sections;
  int ns = ms->nb_sections;
  if(ns == 0 || ptr < ___CAST(void*, m[ns-1])) return ns;
  
  int lo = 0, hi = ns-1;
  while(lo < hi) {
    int mid = (lo+hi)/2;
    if (ptr < ___CAST(void*,m[mid])) lo = mid+1; else hi = mid;
  }
  return lo;
}
/*
 * 'adjust_msections (msp, n)' contracts or expands the msections
 * pointed to by 'msp' so that it contains 'n' sections.  When the
 * msections is contracted, the last sections allocated (i.e. those at
 * the end of the doubly-linked list of sections) will be reclaimed.
 * When expanding the msections there may not be enough memory to
 * allocate new sections so the operation may fail.  However
 * 'adjust_msections' will always leave the msections in a consistent
 * state and there will be at least as many sections as when the
 * expansion was started.  Failure can be detected by checking the
 * 'nb_sections' field.
 */

___HIDDEN void adjust_msections
   ___P((msections **msp,
         int n),
        (msp,
         n)
msections **msp;
int n;)
{
  int max_ns, ns, us;
  msections *ms = *msp;
  msection *hd;
  msection *tl;
  printf("Begin adjust_msections\n");
  if (ms == 0)
    {
      max_ns = 0;
      ns = 0;
      hd = 0;
      tl = 0;
      us = 0;
    }
  else
    {
      max_ns = ms->max_nb_sections;
      ns = ms->nb_sections;
      hd = ms->head;
      tl = ms->tail;
      us = ms->used;
    }

  if (ms == 0 || n > max_ns)
    {      /* must allocate a new msections structure */

      msections *new_ms;
      int i;

      while (n > max_ns) /* grow max_nb_sections until big enough */
        max_ns = 2*max_ns + 1;

      new_ms = ___CAST(msections*,
                       alloc_mem_aligned
                         (___WORDS(sizeof_msections(max_ns)),
                          1,
                          0));

      if (new_ms == 0)
        return;

      new_ms->max_nb_sections = max_ns;
      new_ms->nb_sections = ns;
      new_ms->head = hd;
      new_ms->tail = tl;
      new_ms->used = us;

      for (i=ns-1; i>=0; i--)
        new_ms->sections[i] = ms->sections[i];

      if (ms != 0)
        free_mem_aligned (ms);

      ms = new_ms;

      *msp = ms;
    }

  if (n < ns)
    {
      /* contraction of the msections */
      int j;

      while (ns > n)
        {
          msection *s = tl;

          tl = tl->prev;

          if (tl == 0)
            hd = 0;
          else
            tl->next = 0;

          for (j=s->pos; j<ns-1; j++)
            {
              ms->sections[j] = ms->sections[j+1];
              ms->sections[j]->pos = j;
            }

          free_mem_aligned (s);

          ns--;
        }

      ms->nb_sections = ns;
      ms->head = hd;
      ms->tail = tl;

      /*
       * Contraction of the msections structure is not performed
       * because there is typically very little memory to be
       * reclaimed.
       */
    }
  else
    {
      /* expansion of the msections */

      int i, j;

      while (ns < n)
        {
          msection *s = ___CAST(msection*,
                                alloc_mem_aligned
                                  (___WORDS(sizeof_msection(___MSECTION_SIZE)),
                                   1,
                                   0));

          if (s == 0)
            return;

          i = find_msection (ms, ___CAST(void*,s));
	    
#ifdef ___ALLOC_MEM_UP
          i++;
#endif

          for (j=ns; j>i; j--)
            {
              ms->sections[j] = ms->sections[j-1];
              ms->sections[j]->pos = j;
            }

          ms->sections[i] = s;

          if (tl == 0)
            {
              hd = s;
              s->index = 0;
            }
          else
            {
              tl->next = s;
              s->index = tl->index + 1;
            }

          s->pos = i;
          s->prev = tl;
          s->next = 0;

          tl = s;

          ms->nb_sections = ++ns;
          ms->head = hd;
          ms->tail = tl;
        }

    }
  printf("End adjust_msections\n");
}
void free_msections(msections ** msp) {
 msections *ms = *msp;

  if(ms != 0) {
      int i;
      for(i=ms->nb_sections-1; i>=0; i--)
        free_mem_aligned(ms->sections[i]);

      free_mem_aligned(ms);
      *msp = 0;
  }
}

/*************************/
/* Gestion du Rem_Set */

/*
 * The remembered set is a fixed size points-to buffer that tag object already in it.
 */

void add_remset(generation *g, ___WORD * p) {
  printf("Begin add_remset, p = %p\n", p);
  if(g != gen0) return;
  ___WORD * ptr = (___WORD *) ___UNTAG((___WORD)p);
  *(g->rs->current++) = ptr;
  ++g->rs->count;
  /* Mark the object as present */
  ___TAGMOVABLE(ptr);
  printf("End add_remset\n");
}

void remove_remset(generation *g, ___WORD *p) {
  printf("Begin remove_remset\n");
  if(g != gen0) return;
  ___WORD * ptr = (___WORD *) ___UNTAG((___WORD)p);
  /* Copy the last element in p's place. */
  remset * rs = g->rs;
  int c = rs->count;
  if(c > 1) {
    *p = (___WORD)*(rs->current);
  }
  if(c != 0) rs->count-=1;
  printf("End remove_remset\n");
}

#define ___REMSET_SIZE(r) (r->end - r->rs) 

void adjust_remset(generation *g, long size) {
  printf("Begin adjust_remset\n");
  if(size <= ___REMSET_SIZE(g->rs)) return;
  printf("size: %i\n", size);
  remset * t = (remset *) malloc(sizeof(remset));

  t->rs = (___WORD **) malloc(size*sizeof(___WORD));
  t->current = t->rs;
  t->end = t->rs+size;
  t->count = 0;
  
  /* Copy the old remset */
  ___WORD ** current = g->rs->rs;
  while(current < g->rs->current) {
    *(t->current++) = *(current++);
  }

  /* Free the old remset */
  free(g->rs->rs);
  free(g->rs);
  
  /* and change it. */
  g->rs = t;
  printf("End adjust_remset\n");
}

/* Gestion du SSB */

void add_SSB(___WORD * p) {
  printf("In add_SSB\n");
  p = (___WORD *)___UNTAG((___WORD)p);
  *(SSB->last++) = p;
}

void manage_SSB(___WORD * p) {
  printf("Begin manage_SSB\n");
  ___WORD head = p[-1], tag = 0, l = ___SCMOBJ_SIZE(head);
  int gen = ___GET_GEN(head), i;

  for(i = l-1; i >= 0; --i) {
    ___WORD this = p[i];

    if(___IS_POINTER(this)) {
      this = (___WORD)___UNTAG(this);
      if(this == 0) continue;
      int this_gen = ___GET_GEN(___HEAD(((___WORD *) this)));
      if(this_gen < gen && !(tag & this_gen+1)) {
	add_remset(find_gen(this_gen), p);
	tag |= this_gen+1;
      }
    }    
  }
  printf("End manage_SSB\n");
}

void clear_SSB() {
  printf("In clear SSB:\n");
  // Iterate on the SSB to treat all buffered store.

  // Remove Marks
  ___WORD ** current = SSB->buffer;

  while(current < SSB->last){
    ___WORD * ptr = *current; 
    ___WORD head = (___WORD)___HEAD(ptr);
    //___HEAD(ptr) = ___UNMARK(head);
    manage_SSB(ptr);
    current++;
  }

  SSB->last = SSB->buffer;

  printf("End clear SSB:\n");

}
void clean_SSB() {

  printf("Begin clean_SSB\n");
  // Remove repeated pointers.
  printf("SSB: %p\n", SSB->buffer);
  ___WORD ** current = SSB->buffer;
  ___WORD ** limit = SSB->last;
  SSB->last = current;

  while(SSB->last < limit){

    ___WORD * ptr = *(SSB->last); 
    ___WORD head = (___WORD)___HEAD(ptr);

    if(!___IS_MARKED(head)){
      ___HEAD(ptr) = ___MARKP(head);
      *current++ = ptr;
    }
    SSB->last++;
  }
  
  printf("End clean SSB:\n");
  // If still full: clear.
  if(SSB->last == SSB->end) clear_SSB();
  

}

/* Iterating through msections */
// TODO: Need works.

___HIDDEN void fatal_heap_overflow ___PVOID
{
  char *msgs[2];
  msgs[0] = "Heap overflow";
  msgs[1] = 0;
  ___fatal_error (msgs);
}

msection * next_msection() {
  if(the_msections->nb_sections < the_msections->used) fatal_heap_overflow();
  return the_msections->sections[the_msections->used++];
}

msection * next_stack_msection() {
  printf("In next_stack_msection\n");
  stack_msection = gen0->mem->sections[gen0->current_index+1];
  alloc_stack_limit = stack_msection->base;
  alloc_stack_start = alloc_stack_limit + (___MSECTION_SIZE);
  alloc_stack_ptr = alloc_stack_start;
  printf("End next_stack_msection\n");
  return stack_msection;
}

msection * next_heap_msection(generation * g) {
  printf("In next_heap_msection\n");
  if (g->current != 0) {
      g->current->alloc = g->alloc;
  }

  g->current = g->mem->sections[g->current_index++];
  if(g == gen0) {
    alloc_heap_limit = g->current->base + (___MSECTION_SIZE);
    alloc_heap_ptr = g->current->base;
  }

  return g->current;

}

/* Mark Array */

___WORD * move(___WORD *, ___WORD, generation *);
void mark_array(___WORD * start, ___WORD n) {

  //___WORD *alloc = alloc_heap_ptr; // Need to change.
  //___WORD *limit = alloc_heap_limit;

  //printf("Begin mark_array\n");
  
  while (n > 0) {
    //printf("n: %i, start: %p\n", n, start);
    ___WORD obj = *start;
    //printf("obj: %p\n", obj);

    if (___MEM_ALLOCATED(obj)) {
      //printf("___MEM_ALLOCATED\n");
      ___WORD *body = ___UNTAG(obj) + ___BODY_OFS;
      ___WORD head = body[-1];
      int head_typ = ___HD_TYP(head);
      int subtype = ___HD_SUBTYPE(head);


      if (head_typ == ___MOVABLE0 || (head_typ == ___MOVABLE1 && full_collect_flag)) {
	//printf("Movable\n");
	___WORD words = ___SCMOBJ_SIZE(head);
	generation * g = find_gen(head_typ);
	if(___LIVE(body, g)) {
	  //printf("Live object\n");
	  ++start;
	  --n;
	  continue;
	}
	//printf("head: %p\n", head);
	*start = ___TAG_POINTER((___WORD) move(body, words, g), (*start & 0x3));
      }
      else if (head_typ == ___STILL && full_collect_flag) {
	//printf("Still\n");
	if (body[___STILL_MARK_OFS - ___STILL_BODY_OFS] == -1) {
	    body[___STILL_MARK_OFS - ___STILL_BODY_OFS]
	      = ___CAST(___WORD,still_objs_to_scan);
	    still_objs_to_scan
	      = ___CAST(___WORD,body - ___STILL_BODY_OFS);
	}
      }
      else if (___TYP(head_typ) == ___FORW) {
	//printf("Forward\n");
	  ___WORD *copy_body = ___UNTAG_AS(head, ___FORW) + ___BODY_OFS;
	  *start = ___TAG((copy_body - ___BODY_OFS), ___TYP(obj));
      }
    }
    start++;
    n--;
  }

  //printf("End mark_array\n");
}

___HIDDEN void mark_captured_continuation(___WORD * orig_ptr) {

  ___processor_state ___ps = ___PSTATE;
  ___WORD *ptr = orig_ptr;
  int fs, link, i;
  ___WORD *fp;
  ___WORD ra1;
  ___WORD ra2;
  ___WORD cf;

  cf = *ptr;

  if (___TYP(cf) == ___tFIXNUM && cf != ___FIX(0)) {
    /* continuation frame is in the stack */
    
    ___WORD *alloc = alloc_heap_ptr;
    //___WORD *limit = alloc_heap_limit;

  next_frame:

    fp = ___CAST(___WORD*,cf);
    ra1 = ___FP_STK(fp,-___FRAME_STACK_RA);

    if (ra1 == ___GSTATE->internal_return) {
      ___WORD actual_ra = ___FP_STK(fp,___RETI_RA);
      ___RETI_GET_FS_LINK(actual_ra,fs,link)
	___COVER_MARK_CAPTURED_CONTINUATION_RETI;
    }
    else {
      ___RETN_GET_FS_LINK(ra1,fs,link)
	___COVER_MARK_CAPTURED_CONTINUATION_RETN;
    }

    ___FP_ADJFP(fp,-___FRAME_SPACE(fs)); /* get base of frame */
    ra2 = ___FP_STK(fp,link+1);

    if (___TYP(ra2) == ___tFIXNUM) {
      ___COVER_MARK_CAPTURED_CONTINUATION_ALREADY_COPIED;
      *ptr = ra2; /* already copied, replace by forwarding pointer */
    }
    else {
      ___WORD forw;
      long words;

      ___COVER_MARK_CAPTURED_CONTINUATION_COPY;
      words = fs + ___FRAME_EXTRA_SLOTS;

      /*
      while (alloc + words + ___SUBTYPED_OVERHEAD > limit) {
	alloc_heap_ptr = alloc;
	next_heap_msection (the_msections);
	alloc = alloc_heap_ptr;
	limit = alloc_heap_limit;
      }
      */
      // always copy to gen0
      alloc = gen0->alloc;
      gen0->alloc += words + ___SUBTYPED_OVERHEAD;

      *alloc++ = ___MAKE_HD_WORDS(words, ___sFRAME);
#if ___SUBTYPED_OVERHEAD != 1
          #error "___SUBTYPED_OVERHEAD != 1"
#endif
      forw = ___TAG((alloc - ___BODY_OFS), ___tFIXNUM);
      *alloc++ = ra1;
#if ___FRAME_EXTRA_SLOTS != 1
          #error "___FRAME_EXTRA_SLOTS != 1"
#endif

      for (i=fs; i>0; i--)
	*alloc++ = ___FP_STK(fp,i);

      if (ra2 == ___GSTATE->handler_break) {
	/* first frame of that section */

	___COVER_MARK_CAPTURED_CONTINUATION_FIRST_FRAME;

	cf = ___FP_STK(fp,-___BREAK_FRAME_NEXT);
      }
      else {
	/* not the first frame of that section */

	___COVER_MARK_CAPTURED_CONTINUATION_NOT_FIRST_FRAME;
	___FP_SET_STK(fp,-___FRAME_STACK_RA,ra2)
	  cf = ___CAST(___WORD,fp);
      }

      ___FP_SET_STK(alloc,link+1,cf)
	___FP_SET_STK(fp,link+1,forw) /* leave a forwarding pointer */

      *ptr = forw;
      ptr = &___FP_STK(alloc,link+1);

      if (___TYP(cf) == ___tFIXNUM && cf != ___FIX(0))
	goto next_frame;
    }

    *orig_ptr = ___TAG(___UNTAG_AS(*orig_ptr, ___tFIXNUM), ___tSUBTYPED);

    alloc_heap_ptr = alloc;
  }
  else mark_array (orig_ptr, 1);
}

void mark_frame(___WORD *fp, int fs, ___WORD gcmap, ___WORD *nextgcmap) {
  int i = 1;

  for (;;) {
    if (gcmap & 1) {
      int j = i;
      do {
	if (i == fs) {
	  mark_array (&___FP_STK(fp,i), i-j+1);
	  return;
	}
	if ((i & (___WORD_WIDTH-1)) == 0)
	  gcmap = *nextgcmap++;
	else
	  gcmap >>= 1;
	i++;
      } while (gcmap & 1);
      mark_array (&___FP_STK(fp,i-1), i-j);
    }
    if (i == fs) return;
    if ((i & (___WORD_WIDTH-1)) == 0) gcmap = *nextgcmap++;
    else gcmap >>= 1;
    i++;
  }
}

void mark_continuation() {

  ___processor_state ___ps = ___PSTATE;
  int fs, link;
  ___WORD *fp;
  ___WORD ra1;
  ___WORD ra2;
  ___WORD gcmap;
  ___WORD *nextgcmap = 0;

  fp = ___ps->fp;

  if (fp != ___ps->stack_break) {
    for (;;) {
      ra1 = ___FP_STK(fp,-___FRAME_STACK_RA);

      if (ra1 == ___GSTATE->internal_return) {
	___WORD actual_ra = ___FP_STK(fp,___RETI_RA);
	___RETI_GET_FS_LINK_GCMAP(actual_ra,fs,link,gcmap,nextgcmap)
	  ___COVER_MARK_CONTINUATION_RETI;
      }
      else {
	___RETN_GET_FS_LINK_GCMAP(ra1,fs,link,gcmap,nextgcmap)
	  ___COVER_MARK_CONTINUATION_RETN;
      }

      ___FP_ADJFP(fp,-___FRAME_SPACE(fs)); /* get base of frame */
      ra2 = ___FP_STK(fp,link+1);

      mark_frame (fp, fs, gcmap, nextgcmap);

      if (fp == ___ps->stack_break) break;
      
      ___FP_SET_STK(fp,-___FRAME_STACK_RA,ra2)
    }
  }
  mark_captured_continuation (&___FP_STK(fp,-___BREAK_FRAME_NEXT));
}

void mark_rc() {
  printf("Begin mark_rc\n");
  rc_header *h = rc_head.next;

  while (h != &rc_head) {
    rc_header *next = h->next;
    mark_array (&h->data, 1);
    h = next;
  }

  printf("End mark_rc\n");
}

/* Scan */
#define ___IS_FORW(x) ((x & ___FORW) == 3)
#define ___FORWP(x) (x | ___FORW)
#define ___UNFORW(x) (x ^ ___FORW)
#define ___MOV_ALLOCATED(ptr, g) (find_msection(ptr,g->mem) < -1)

___WORD * copy(___WORD * start, ___WORD n, generation * dest){
  // Copy to new dest: determine dest wether start is old.
  
  ___WORD * d = dest->alloc;

  memcpy(d++ , start, n*sizeof(___WORD));

  // Tag as forwarded with new add.
  start[0] = ___FORWP((___WORD)(d));
  dest->alloc += n; 
  return d;
}

___WORD * move(___WORD * this,___WORD l, generation * g) {

  //printf("Begin move: this = %p, l = %ld\n", this, l);
  generation * dest, * current;
  ___WORD h = this[-1];
  //printf("h: %p\n", h);
  int gen = ___GET_GEN(h);
  current = find_gen(gen);
  ___WORD * addr;

  /* Find destination */
  if(l == 0) return this;
  if(gen > 1) return this;              // Still object
  if(this < current->old) dest = current->next; // Old object
  else dest = current;
  
  /* Copy */

  if(dest != NULL) addr = copy(this-1, l+1, dest);
  else {
    // TODO
    // Move to still.
    //___WORD *s = still_allocate(this);
    //addr = (s->base)+1;
  }

  //printf("dest: %i, current: %i\n", dest->index, current->index);
  /* Promotion */

  int i = 2;
  if(dest != NULL) i = dest->index;

  if(i > current->index) {           // Promote
    addr[-1] = ___PROMOTE(addr[-1]);
    manage_SSB(addr);
  }
  //printf("End move\n");
  return addr;
}


long scan(___WORD * body){
  ___WORD head = body[-1];
  long words = ___HD_WORDS(head);
  int subtype = ___HD_SUBTYPE(head);

#ifdef ENABLE_CONSISTENCY_CHECKS
  reference_location = IN_OBJECT;
  container_body = body;
#endif

  switch (subtype) {
    case ___sFOREIGN:
    case ___sSTRING:
    case ___sS8VECTOR:
    case ___sU8VECTOR:
    case ___sS16VECTOR:
    case ___sU16VECTOR:
    case ___sS32VECTOR:
    case ___sU32VECTOR:
    case ___sS64VECTOR:
    case ___sU64VECTOR:
    case ___sF32VECTOR:
    case ___sF64VECTOR:
    case ___sFLONUM:
    case ___sBIGNUM:
      break;

    case ___sWEAK:
      if (words == ___WILL_SIZE) {
          /* Object is a will */

          /*
           * The will contains a weak reference to its testator object
           * and a strong reference to the action procedure.
           * Consequently, the action procedure must be marked and,
           * only if traverse_weak_refs is true, the testator object
           * is also marked.  The link field is never scanned.
           */

          if (traverse_weak_refs) mark_array (body+1, 2); /* scan action and testator */
          else {
              mark_array (body+2, 1); /* scan action only */
              /*
               * Remember that this will's testator object remains to
               * be marked by the process_wills function.
               */
              body[0] = body[0] | ___UNMARKED_TESTATOR_WILL;
	  }
      }
      else {
          /* Object is a GC hash table */

          int flags = ___INT(body[___GCHASHTABLE_FLAGS]);
          int i;

          if ((flags & ___GCHASHTABLE_FLAG_WEAK_KEYS) == 0 &&
              (flags & ___GCHASHTABLE_FLAG_MEM_ALLOC_KEYS)) {
              for (i=words-2; i>=___GCHASHTABLE_KEY0; i-=2)
                mark_array(body+i, 1); /* mark objects in key fields */
	  }

          if ((flags & ___GCHASHTABLE_FLAG_WEAK_VALS) == 0) {
              for (i=words-1; i>=___GCHASHTABLE_VAL0; i-=2)
                mark_array (body+i, 1); /* mark objects in value fields */
	  }

          body[0] = reached_gc_hash_tables;
          reached_gc_hash_tables = ___TAG((body-1),0);
      }
      break;

    case ___sSYMBOL:
    case ___sKEYWORD:
      mark_array (body, 1); /* only scan name of symbols & keywords */
      break;

    case ___sCONTINUATION:
      mark_captured_continuation (&body[___CONTINUATION_FRAME]);
      mark_array (body+1, words-1); /* skip the frame pointer */
      break;

    case ___sFRAME:
      {
        int fs, link;
        ___WORD *fp = body + ___FRAME_EXTRA_SLOTS;
        ___WORD ra = body[0];
        ___WORD gcmap;
        ___WORD *nextgcmap = 0;
        ___WORD frame;

        if (ra == ___GSTATE->internal_return) {
            ___WORD actual_ra = body[___FRAME_RETI_RA];
            ___RETI_GET_FS_LINK_GCMAP(actual_ra,fs,link,gcmap,nextgcmap)
            ___COVER_SCAN_FRAME_RETI;
	}
        else {
            ___RETN_GET_FS_LINK_GCMAP(ra,fs,link,gcmap,nextgcmap)
            ___COVER_SCAN_FRAME_RETN;
	}

        fp += fs;
        frame = ___FP_STK(fp,link+1);
        if (___TYP(frame) == ___tFIXNUM && frame != ___FIX(0)) ___FP_SET_STK(fp,link+1,___FAL)
        mark_frame (fp, fs, gcmap, nextgcmap);

        if (___TYP(frame) == ___tFIXNUM && frame != ___FIX(0))
          ___FP_SET_STK(fp,link+1,___TAG(___UNTAG_AS(frame, ___tFIXNUM), ___tSUBTYPED))

        mark_array (&body[0], 1);
      }
      break;

    case ___sPROCEDURE:
      if (___HD_TYP(head) != ___PERM) /* only scan closures */
        mark_array (body+1, words-1); /* only scan free variables */
      break;

    default:
      mark_array (body, words);
      break;
    }

  return words;
}


void scan1(___WORD * body, int length) {
  printf("Begin scan\n");
  int i = ___GET_GEN(___HEAD(body));
  printf("i: %ld, body: %p, length: %ld\n", i, body, length);
  
  // TODO: Not sure if correct
  if(i>1) return;

  generation * g = find_gen(i);
  //printf("g: %p\n", g);

  for(i = 0; i < length ; i++) {
    ___WORD * this = (___WORD *) body[i];
    printf("This: %p, body+i: %p\n", this, body+i);

    if(___IS_POINTER(((___WORD)this))) {
      //printf("Is pointer\n");
      ___WORD tag = ___POINTER_TAG((___WORD) this);
      this = (___WORD *) ___UNTAG((___WORD)this);
      if(this == 0) continue;

      ___WORD h = ___HEAD(this);
      //printf("this: %p, head: %p\n", this, h);

      if(!___MOV_ALLOCATED(this, g)) {
      
	if(___IS_FORW(h)){
	  body[i] = (___WORD)___UNFORW(h);
	}
	else {
	  // Is object
	  int gen = ___GET_GEN(h);
	  
	  if((full_collect_flag && gen == 1)|| gen == 0) {
	    ___WORD l = ___SCMOBJ_SIZE(h);
	    //printf("Calling move\n");
	    body[i] = ___TAG_POINTER((___WORD) move(this, l, g), tag);
	    //printf("Body[i] = %p\n", body[i]);
	  }
	}
      }
    }
  }
  printf("End scan\n");
}

/* GC helper functions */

void flip(generation * g) {

  ___WORD * temp = g->fromspace;
  g->fromspace = g->tospace;
  g->tospace = temp;
  g->alloc = g->fromspace;
  g->scan = g->fromspace;

  g->current->alloc = g->alloc;

  if(g->fromspace == g->mem->sections[0]->base) {
    /* Goes at bottom */
    g->current = g->mem->sections[0];
    g->current_index = 0;
  }
  else {
    /* Goes in middle */
    g->current_index = g->mem->nb_sections/2;
    g->current = g->mem->sections[g->current_index];
  }
  g->start = g->current_index;

}
void scanner(generation *g) {
  printf("Begin scanner: %ld\n", g->index);

  int i = g->start;
  msection * m = g->mem->sections[i];
  ___WORD * eos = m->alloc;
  g->scan = m->base;

  //printf("Eos: %p, g->scan: %p, g->alloc: %p\n", eos, g->scan, g->alloc);

  while(g->scan < g->alloc || m != g->current){
    //printf("In if: g->scan: %p, eos: %p, alloc: %p\n", g->scan, eos, g->alloc);
    //printf("m0: %p, m1: %p\n", m->base, m->base+___MSECTION_SIZE);
    // Check if scan reached end-of msection.
    if(g->scan >= eos && m != g->current){
      m = g->mem->sections[++i];
      eos = m->alloc;
      g->scan = m->base;
    }

    // On extrait le header du mot.
    ___WORD header = *(g->scan);
    //printf("header: %p\n", header);
    ___WORD length = ___SCMOBJ_SIZE(header);
    //printf("Before scan\n");
    scan(++(g->scan));    
    //printf("After scan\n");        
    g->scan+=length; 
  }
  printf("After while\n");
  // Set old pointer
  g->old = g->scan; 
  printf("End scanner\n");
}
//long adjust_heap(long avail, long live) {return 0;}

void copy_remset(generation * g) {

  /* Iterate over the remset.
   * For each pointer, test if it is a forwarding pointer.
   * Update it if it is, copy it otherwise.
   */
  printf("Begin copy_remset\n");
  long i;
  ___WORD ** iter = g->rs->rs;
  printf("count: %ld\n", g->rs->count);
  for(i = 0; i<g->rs->count; ++i){
    printf("iter: %p\n", iter[0]);
    ___WORD head = ___HEAD(iter[i]);
    printf("head: %i\n", head);
    if(___IS_FORW(head)){
      printf("forw\n");
      iter[i] = (___WORD *)___UNFORW(head);
    }
    else {
      printf("obj\n");
      iter[i] = move(iter[i], ___SCMOBJ_SIZE(head), g);
    }
    /* If it left the gen, remove it */
    head = ___HEAD(iter[i]);
    int gen = ___GET_GEN(head);
    if(gen != g->index){
      // TODO
      remove_remset(g, iter+i);
    }
  }
  printf("End copy_remset\n");
}


/**************************/

/* Heap properties */

#define UNMARKED_MOVABLE(obj) \
((unmarked_typ = ___HD_TYP((unmarked_body=___BODY(obj))[-1])) <= ___MOVABLE1)

#define UNMARKED_STILL(obj) \
(unmarked_typ == ___STILL && \
 unmarked_body[___STILL_MARK_OFS - ___STILL_BODY_OFS] == -1)

#define UNMARKED(obj) \
(UNMARKED_MOVABLE(obj) || UNMARKED_STILL(obj))

/* Scanning Stills. */

void init_still_objs_to_scan() {

  ___WORD *base = ___CAST(___WORD*,still_objs);
  ___WORD *to_scan = 0;

  while (base != 0)
    {
      if (base[___STILL_REFCOUNT_OFS] == 0)
        base[___STILL_MARK_OFS] = -1;
      else
        {
          base[___STILL_MARK_OFS] = ___CAST(___WORD,to_scan);
          to_scan = base;
        }
      base = ___CAST(___WORD*,base[___STILL_LINK_OFS]);
    }

  still_objs_to_scan = ___CAST(___WORD,to_scan);
}


void scan_still_objs_to_scan() {
  ___WORD *base;

  while ((base = ___CAST(___WORD*,still_objs_to_scan)) != 0) {
    still_objs_to_scan = base[___STILL_MARK_OFS];
    scan(base + ___STILL_BODY_OFS);
  }
}

void free_unmarked_still_objs() {
  ___WORD *last = &still_objs;
  ___WORD *base = ___CAST(___WORD*,*last);

  while (base != 0)
    {
      ___WORD link = base[___STILL_LINK_OFS];
      if (base[___STILL_MARK_OFS] == -1)
        {
          ___WORD head = base[___STILL_BODY_OFS-1];
          if (___HD_SUBTYPE(head) == ___sFOREIGN)
            ___release_foreign
              (___TAG((base + ___STILL_BODY_OFS - ___BODY_OFS), ___tSUBTYPED));
          words_nonmovable -= base[___STILL_LENGTH_OFS];
          free_mem_aligned (base);
        }
      else
        {
          *last = ___CAST(___WORD,base);
          last = base + ___STILL_LINK_OFS;
        }
      base = ___CAST(___WORD*,link);
    }

  *last = 0;
}

void free_still_objs() {
  ___WORD *base = ___CAST(___WORD*,still_objs);

  still_objs = 0;

  while (base != 0)
    {
      ___WORD link = base[___STILL_LINK_OFS];
      ___WORD head = base[___STILL_BODY_OFS-1];
      if (___HD_SUBTYPE(head) == ___sFOREIGN)
        ___release_foreign
          (___TAG((base + ___STILL_BODY_OFS - ___BODY_OFS), ___tSUBTYPED));
      free_mem_aligned (base);
      base = ___CAST(___WORD*,link);
    }
}

/***************************/

/* Initialise memory */

___HIDDEN void setup_pstate ___PVOID {
  ___processor_state ___ps = ___PSTATE;
  long stack_avail;
  long stack_left_before_fudge;
  long heap_avail;
  long heap_left_before_fudge;

  stack_avail = ___MSECTION_SIZE;
  stack_left_before_fudge = (alloc_stack_ptr - alloc_stack_limit) - ___MSECTION_FUDGE;

  ___ps->fp = alloc_stack_ptr;
  ___ps->stack_limit = alloc_stack_ptr
                       - ((stack_avail < stack_left_before_fudge)
                          ? stack_avail
                          : stack_left_before_fudge);

  heap_avail = ___MSECTION_SIZE;
  heap_left_before_fudge = (alloc_heap_limit - alloc_heap_ptr)
                           - ___MSECTION_FUDGE;

  ___ps->hp = alloc_heap_ptr;
  ___ps->heap_limit = alloc_heap_ptr
                      + ((heap_avail < heap_left_before_fudge)
                         ? heap_avail
                         : heap_left_before_fudge);

  ___begin_interrupt_service ();
  ___end_interrupt_service (0);

}

___F64 ___bytes_allocated ___PVOID
{
  ___processor_state ___ps = ___PSTATE;

  alloc_stack_ptr = ___ps->fp; /* needed by 'WORDS_OCCUPIED' */
  alloc_heap_ptr  = ___ps->hp; /* needed by 'WORDS_OCCUPIED' */

  return ___GSTATE->bytes_allocated_minus_occupied +
         ___CAST(___F64,WORDS_OCCUPIED) * ___WS;
}

void setup_gen(generation ** g, int index) {

  *g = (generation*) malloc(sizeof(generation));
  (*g)->index = index;
  (*g)->tospace = 0;
  (*g)->fromspace = 0;
  (*g)->scan = 0;
  (*g)->old = 0;
  (*g)->alloc = 0;
  (*g)->current = 0;
  (*g)->current_index = 0;
  (*g)->start = 0;
  (*g)->mem = 0;

  /* Initialize remset */

  (*g)->rs = (remset *) malloc(sizeof(remset));
  (*g)->rs->rs = 0;
  (*g)->rs->current = 0;
  (*g)->rs->end = 0;
  (*g)->rs->count = 0;

}

void adjust_generation(generation * g, int ns) {
  int i;
  if(g->current == 0) {
    /* Allocate the msections of g */

    /* Test if there are enough msections */
    /* Add msections to mem */
    g->mem = (msections *) malloc(sizeof_msections(ns));
    
    for(i = 0; i<ns ; ++i) {
      g->mem->sections[i] = next_msection();
    }

    g->mem->nb_sections = ns;
    g->current = g->mem->sections[0];
    g->tospace = g->mem->sections[ns/2]->base;
    g->fromspace = g->current->base;
    g->scan = 0;
    g->alloc = g->fromspace;
    g->start = g->current_index;
    
  }
  else {

  }
}


void setup_SSB() {
  printf("Begin setup_SSB\n");
  SSB = (SSB_struct *) malloc(sizeof(SSB_struct));
  SSB->last = SSB->buffer;
  SSB->end = SSB->buffer+ssb_size;
  printf("End setup_SSB\n");
}


void print_msections(msections * m) {
  printf("\n    mem: %p\n", m);
  printf("    max_nb_sections: %i\n", m->max_nb_sections);
  printf("    nb_sections: %i\n", m->nb_sections);
  printf("    max_nb_sections: %i\n", m->max_nb_sections);
  int i;
  printf("    sections:\n");
  for(i = 0; i < m->nb_sections; ++i) printf("    %i: %p\n", i, m->sections[i]);

}

void print_gen(generation * g) {

  /* Print remembered set */
  remset * r = g->rs;
  printf("Printing generation %i\n", g->index);
  printf("    remset:\n");
  printf("    rs: %p\n", r->rs);
  printf("    current: %p\n", r->current);
  printf("    end: %p\n", r->end);
  printf("    count: %i\n", r->count);

  print_msections(g->mem);
  
}



___SCMOBJ ___setup_mem() {
  ___processor_state ___ps = ___PSTATE;
  int init_nb_sections;
  printf("begin setup_mem\n");
  /*
   * It is important to initialize the following pointers first so
   * that if the program terminates early the procedure ___cleanup_mem
   * will not access dangling pointers.
   */

  psections     = 0;
  still_objs    = 0;

  setup_rc ();
  /* Build each generation */

  setup_gen(&gen0, 0);
  setup_gen(&gen1, 1);
  
  gen0->previous = 0;
  gen0->next = gen1;
  gen1->previous = gen0;
  gen1->next = 0;

  /* Build the remembered set */
  setup_SSB();

  /*
   * Set the overflow reserve so that the rest parameter handler can
   * construct the rest parameter list without having to call the
   * garbage collector.
   */

  normal_overflow_reserve = 2*((___MAX_NB_PARMS+___SUBTYPED_OVERHEAD) +
                               ___MAX_NB_ARGS*(___PAIR_SIZE+___PAIR_OVERHEAD));
  overflow_reserve = normal_overflow_reserve;

  /* Allocate heap */

  init_nb_sections = ((___setup_params.min_heap >> ___LWS) +
                      overflow_reserve + 2*___MSECTION_FUDGE +
                      2*((___MSECTION_SIZE>>1)-___MSECTION_FUDGE+1) - 1) /
                     (2*((___MSECTION_SIZE>>1)-___MSECTION_FUDGE+1));
  if(init_nb_sections < ___MIN_NB_MSECTIONS) init_nb_sections = ___MIN_NB_MSECTIONS;
  if(init_nb_sections < 4) init_nb_sections = 4;

  //printf("After SSB\n");
  //printf("init_nb_sections: %i\n", init_nb_sections);
  adjust_msections(&the_msections, 2*init_nb_sections+1);
  next_msection();
  print_msections(the_msections);

  //printf("the_msections->nb_sections: %i\n", the_msections->nb_sections);

  adjust_generation(gen0, 4);
  adjust_remset(gen0, ___MSECTION_SIZE);
  adjust_generation(gen1, init_nb_sections);

  // Setup the generation's info:
  gen0->mem->nb_sections = 4;
  gen1->mem->nb_sections = init_nb_sections;

  next_heap_msection(gen0);
  next_heap_msection(gen1);
  next_stack_msection();

  printf("gen0 null: %i\n", gen0->mem == NULL);
  printf("gen1 null: %i\n", gen1->mem == NULL);
  printf("gen0->mem->nb_sections: %i\n", gen0->mem->nb_sections);
  printf("gen1->mem->nb_sections: %i\n", gen1->mem->nb_sections);

  if(gen0->mem == NULL || gen1->mem == NULL || 
     gen0->mem->nb_sections != 4 ||
     gen1->mem->nb_sections != init_nb_sections) {
    printf("Heap Overflow\n");
    return ___FIX(___HEAP_OVERFLOW_ERR);
  }
  printf("Here\n");
  /*
   * Create "break frame" of initial top section.
   */

  print_gen(gen0);
  heap_size = ___MSECTION_SIZE;

  ___ps->stack_start = alloc_stack_start;
  alloc_stack_ptr = alloc_stack_start;

  ___FP_ADJFP(alloc_stack_ptr,___BREAK_FRAME_SPACE)
  ___FP_SET_STK(alloc_stack_ptr,-___BREAK_FRAME_NEXT,0)

  ___ps->stack_break = alloc_stack_ptr;

  /*
   * Setup will lists.
   */

  ___ps->executable_wills = ___TAG(0,___EXECUTABLE_WILL); /* tagged empty list */
  ___ps->nonexecutable_wills = ___TAG(0,0); /* tagged empty list */

  printf("___ps->stack_break: %p, alloc_stack_ptr: %p, alloc_stack_start: %p\n", ___ps->stack_break, alloc_stack_ptr, alloc_stack_start);

  setup_pstate ();
printf("___ps->stack_break: %p, alloc_stack_ptr: %p, alloc_stack_start: %p\n", ___ps->stack_break, alloc_stack_ptr, alloc_stack_start);
  /* Setup global state */

  ___GSTATE->nb_gcs = 0.0;
  ___GSTATE->gc_user_time = 0.0;
  ___GSTATE->gc_sys_time = 0.0;
  ___GSTATE->gc_real_time = 0.0;
  ___GSTATE->bytes_allocated_minus_occupied = 0.0;

  ___GSTATE->last_gc_real_time = 0.0;
  ___GSTATE->last_gc_heap_size = ___CAST(___F64,heap_size) * ___WS;
  ___GSTATE->last_gc_live = 0.0;
  ___GSTATE->last_gc_movable = 0.0;
  ___GSTATE->last_gc_nonmovable = 0.0;

  printf("end setup_mem\n");
  return ___FIX(___NO_ERR);
}

// TODO
void ___cleanup_mem()
{
  //free_msections (&the_msections);
  //free_msections (&the_olds);
  free_psections ();
  free_still_objs ();
  cleanup_rc ();
}

/* Wills */

void determine_will_executability(___WORD list) {

  while (___UNTAG(list) != 0) {
    ___WORD* will_body = ___BODY(list);
    ___WORD will_head = will_body[-1];
    ___WORD testator;
    ___WORD *unmarked_body; /* used by the UNMARKED macro */
    int unmarked_typ;

    if (___TYP(will_head) == ___FORW) /* was will forwarded? */
      will_body = ___BODY_AS(will_head,___FORW);
    
    list = will_body[0];
    testator = will_body[1];

    if (___MEM_ALLOCATED(testator) &&
	UNMARKED(testator)) /* testator was not marked? */
    {
      /*
       * All paths to testator object from roots pass through
       * weak references, so mark will as executable.
       */

      will_body[0] = list | ___EXECUTABLE_WILL;
    }
  }
}


void process_wills() {

  ___processor_state ___ps = ___PSTATE;
  ___WORD* tail_exec;
  ___WORD* tail_nonexec;
  ___WORD curr;

  determine_will_executability (___ps->nonexecutable_wills);

  /*
   * Finish scanning the wills whose testator object remains to be
   * marked.
   *
   * The wills that have become executable are also transferred from
   * the nonexecutable wills list to the executable wills list.
   */

  tail_exec = &___ps->executable_wills;
  curr = *tail_exec;

  while (___UNTAG(curr) != 0) {
    ___WORD will = ___TAG(___UNTAG(curr),___tSUBTYPED);
    
    mark_array (&will, 1);

    *tail_exec = ___TAG(___UNTAG(will),___EXECUTABLE_WILL);
    tail_exec = &___BODY_AS(will,___tSUBTYPED)[0];
    curr = *tail_exec;
    if (curr & ___UNMARKED_TESTATOR_WILL)
      mark_array (tail_exec+1, 1); /* mark testator object */
  }

  tail_nonexec = &___ps->nonexecutable_wills;
  curr = *tail_nonexec;

  while (___UNTAG(curr) != 0) {
    ___WORD will = ___TAG(___UNTAG(curr),___tSUBTYPED);

    mark_array (&will, 1);

    if (___BODY_AS(will,___tSUBTYPED)[0] & ___EXECUTABLE_WILL) {
      /* move will to executable will list */

      *tail_exec = ___TAG(___UNTAG(will),___EXECUTABLE_WILL);
      tail_exec = &___BODY_AS(will,___tSUBTYPED)[0];
      curr = *tail_exec;
      if (curr & ___UNMARKED_TESTATOR_WILL)
	mark_array (tail_exec+1, 1); /* mark testator object */
    }
    else {
      /* leave will in nonexecutable will list */

      *tail_nonexec = ___TAG(___UNTAG(will),0);
      tail_nonexec = &___BODY_AS(will,___tSUBTYPED)[0];
      curr = *tail_nonexec;
      if (curr & ___UNMARKED_TESTATOR_WILL)
	mark_array (tail_nonexec+1, 1); /* mark testator object */
    }
  }

  *tail_exec = ___TAG(0,___EXECUTABLE_WILL);
  *tail_nonexec = ___TAG(0,0);
}


/* GC_hash_tables */

___HIDDEN void process_gc_hash_tables ___PVOID
{
  ___WORD curr = reached_gc_hash_tables;

  while (curr != ___TAG(0,0))
    {
      ___WORD* body = ___BODY(curr);
      ___WORD words = ___SCMOBJ_SIZE(body[-1]);
      int flags = ___INT(body[___GCHASHTABLE_FLAGS]);
      int i;

      curr = body[0];

      body[0] = ___FIX(0);

      if (((___GCHASHTABLE_FLAG_WEAK_KEYS | ___GCHASHTABLE_FLAG_MEM_ALLOC_KEYS)
           & flags) ==
          (___GCHASHTABLE_FLAG_WEAK_KEYS | ___GCHASHTABLE_FLAG_MEM_ALLOC_KEYS))
        {
          if (flags & ___GCHASHTABLE_FLAG_WEAK_VALS)
            {
              /*
               * GC hash table is weak on keys and on values.
               */

              /*
               * Eliminate GC hash table entries with an unmarked key
               * or an unmarked value.
               */

              for (i=words-2; i>=___GCHASHTABLE_KEY0; i-=2)
                {
                  ___WORD *unmarked_body; /* used by the UNMARKED macro */
                  int unmarked_typ;

                  ___WORD key = body[i];
                  ___WORD val = body[i+1];

                  if (___MEM_ALLOCATED(key))
                    {
                      ___WORD key_head = ___BODY(key)[-1];

                      if (___TYP(key_head) == ___FORW)
                        {
                          /*
                           * The key is movable and has been
                           * forwarded.
                           */

                          if (___MEM_ALLOCATED(val))
                            {
                              ___WORD val_head = ___BODY(val)[-1];

                              if (___TYP(val_head) == ___FORW)
                                {
                                  /*
                                   * The key is movable and has been
                                   * forwarded and the value is
                                   * movable and has been forwarded,
                                   * so update key field and value
                                   * field and remember to rehash next
                                   * time the GC hash table is
                                   * accessed.
                                   */

                                  body[i] =
                                    ___TAG(___UNTAG_AS(key_head, ___FORW),
                                           ___TYP(key));
                                  body[i+1] =
                                    ___TAG(___UNTAG_AS(val_head, ___FORW),
                                           ___TYP(val));
                                  flags |= ___GCHASHTABLE_FLAG_KEY_MOVED;
                                }
                              else if (UNMARKED(val))
                                {
                                  /*
                                   * Change the entry to indicate it
                                   * has been deleted.
                                   */

                                  body[i] = ___DELETED;
                                  body[i+1] = ___UNUSED;
                                  body[___GCHASHTABLE_COUNT] =
                                    ___FIXSUB(body[___GCHASHTABLE_COUNT],
                                              ___FIX(1));
                                  flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                                }
                              else
                                {
                                  /*
                                   * The key is movable and has been
                                   * forwarded and the value is not
                                   * movable and is reachable, so
                                   * update key field and remember to
                                   * rehash next time the GC hash
                                   * table is accessed.
                                   */

                                  body[i] =
                                    ___TAG(___UNTAG_AS(key_head, ___FORW),
                                           ___TYP(key));
                                  flags |= ___GCHASHTABLE_FLAG_KEY_MOVED;
                                }
                            }
                          else
                            {
                              /*
                               * The key is movable and has been
                               * forwarded, and the value is not
                               * memory allocated, so update key field
                               * and remember to rehash next time the
                               * GC hash table is accessed.
                               */

                              body[i] =
                                ___TAG(___UNTAG_AS(key_head, ___FORW),
                                       ___TYP(key));
                              flags |= ___GCHASHTABLE_FLAG_KEY_MOVED;
                            }
                        }
                      else if (UNMARKED(key))
                        {
                          /*
                           * Change the entry to indicate it has been
                           * deleted.
                           */

                          body[i] = ___DELETED;
                          body[i+1] = ___UNUSED;
                          body[___GCHASHTABLE_COUNT] =
                            ___FIXSUB(body[___GCHASHTABLE_COUNT],___FIX(1));
                          flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                        }
                      else
                        {
                          /*
                           * The key is not movable and is reachable.
                           */

                          if (___MEM_ALLOCATED(val))
                            {
                              ___WORD val_head = ___BODY(val)[-1];

                              if (___TYP(val_head) == ___FORW)
                                {
                                  /*
                                   * The key is not movable and is
                                   * reachable and the value is
                                   * movable and has been forwarded,
                                   * so update value field.
                                   */

                                  body[i+1] =
                                    ___TAG(___UNTAG_AS(val_head, ___FORW),
                                           ___TYP(val));
                                }
                              else if (UNMARKED(val))
                                {
                                  /*
                                   * Change the entry to indicate it
                                   * has been deleted.
                                   */

                                  body[i] = ___DELETED;
                                  body[i+1] = ___UNUSED;
                                  body[___GCHASHTABLE_COUNT] =
                                    ___FIXSUB(body[___GCHASHTABLE_COUNT],
                                              ___FIX(1));
                                  flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                                }
                              else
                                {
                                  /*
                                   * The key is not movable and is
                                   * reachable and the value is not
                                   * movable and is reachable, so
                                   * leave fields untouched.
                                   */
                                }
                            }
                          else
                            {
                              /*
                               * The key is not movable and is
                               * reachable and the value is not memory
                               * allocated, so leave fields untouched.
                               */
                            }
                        }
                    }
                  else
                    {
                      /*
                       * The key is not memory allocated.
                       */

                      if (___MEM_ALLOCATED(val))
                        {
                          ___WORD val_head = ___BODY(val)[-1];

                          if (___TYP(val_head) == ___FORW)
                            {
                              /*
                               * The key is not memory allocated and
                               * the value is movable and has been
                               * forwarded, so update value field.
                               */

                              body[i+1] =
                                ___TAG(___UNTAG_AS(val_head, ___FORW),
                                       ___TYP(val));
                            }
                          else if (UNMARKED(val))
                            {
                              /*
                               * Change the entry to indicate it
                               * has been deleted.
                               */

                              body[i] = ___DELETED;
                              body[i+1] = ___UNUSED;
                              body[___GCHASHTABLE_COUNT] =
                                ___FIXSUB(body[___GCHASHTABLE_COUNT],
                                          ___FIX(1));
                              flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                            }
                          else
                            {
                              /*
                               * The key is not memory allocated and
                               * the value is not movable and is
                               * reachable, so leave fields untouched.
                               */
                            }
                        }
                      else
                        {
                          /*
                           * The key is not memory allocated and the
                           * value is not memory allocated, so leave
                           * fields untouched.
                           */
                        }
                    }
                }
            }
          else
            {
              /*
               * GC hash table is weak on keys only.
               */

              /*
               * Eliminate GC hash table entries with an unmarked key.
               */

              for (i=words-2; i>=___GCHASHTABLE_KEY0; i-=2)
                {
                  ___WORD *unmarked_body; /* used by the UNMARKED macro */
                  int unmarked_typ;

                  ___WORD key = body[i];

                  if (___MEM_ALLOCATED(key))
                    {
                      ___WORD head = ___BODY(key)[-1];

                      if (___TYP(head) == ___FORW)
                        {
                          /*
                           * The key is movable and has been
                           * forwarded, so update key field and
                           * remember to rehash next time the
                           * GC hash table is accessed.
                           */

                          body[i] = ___TAG(___UNTAG_AS(head, ___FORW),
                                           ___TYP(key));
                          flags |= ___GCHASHTABLE_FLAG_KEY_MOVED;
                        }
                      else if (UNMARKED(key))
                        {
                          /*
                           * Change the entry to indicate it has been
                           * deleted.
                           */

                          body[i] = ___DELETED;
                          body[i+1] = ___UNUSED;
                          body[___GCHASHTABLE_COUNT] =
                            ___FIXSUB(body[___GCHASHTABLE_COUNT],___FIX(1));
                          flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                        }
                    }
                }
            }
        }
      else
        {
          if (flags & ___GCHASHTABLE_FLAG_WEAK_VALS)
            {
              /*
               * GC hash table is weak on values only.
               */

              /*
               * Eliminate GC hash table entries with an unmarked value.
               */

              for (i=words-2; i>=___GCHASHTABLE_KEY0; i-=2)
                {
                  ___WORD *unmarked_body; /* used by the UNMARKED macro */
                  int unmarked_typ;

                  ___WORD val = body[i+1];

                  if (___MEM_ALLOCATED(val))
                    {
                      ___WORD head = ___BODY(val)[-1];

                      if (___TYP(head) == ___FORW)
                        {
                          /*
                           * The value is movable and has been
                           * forwarded, so update value field.
                           */

                          body[i+1] = ___TAG(___UNTAG_AS(head, ___FORW),
                                             ___TYP(val));
                        }
                      else if (UNMARKED(val))
                        {
                          /*
                           * Change the entry to indicate it has been
                           * deleted.
                           */

                          body[i] = ___DELETED;
                          body[i+1] = ___UNUSED;
                          body[___GCHASHTABLE_COUNT] =
                            ___FIXSUB(body[___GCHASHTABLE_COUNT],___FIX(1));
                          flags |= ___GCHASHTABLE_FLAG_ENTRY_DELETED;
                        }
                    }
                }
            }

          if (flags & ___GCHASHTABLE_FLAG_MEM_ALLOC_KEYS)
            flags |= ___GCHASHTABLE_FLAG_KEY_MOVED; /* assume worst case */
        }

      body[___GCHASHTABLE_FLAGS] = ___FIX(flags);
    }
}


void ___gc_hash_table_rehash_in_situ
   ___P((___SCMOBJ ht),
        (ht)
___SCMOBJ ht;)
{
  ___WORD* body = ___BODY_AS(ht,___tSUBTYPED);
  long words = ___SCMOBJ_SIZE(body[-1]);
  int size2 = ___INT(___VECTORLENGTH(ht)) - ___GCHASHTABLE_KEY0;
  int i;

  ___FIELD(ht, ___GCHASHTABLE_FLAGS) =
    ___FIXAND(___FIELD(ht, ___GCHASHTABLE_FLAGS),
              ___FIXNOT(___FIX(___GCHASHTABLE_FLAG_KEY_MOVED)));

  if (___FIXZEROP(___FIXAND(body[___GCHASHTABLE_FLAGS],
                            ___FIX(___GCHASHTABLE_FLAG_MEM_ALLOC_KEYS))))
    {
      /*
       * Free deleted entries and mark key field of all active
       * entries.
       */

      for (i=___GCHASHTABLE_KEY0; i<words; i+=2)
        {
          ___WORD key = body[i];
          if (key == ___DELETED)
            {
              body[i] = ___UNUSED;
              body[___GCHASHTABLE_FREE] =
                ___FIXADD(body[___GCHASHTABLE_FREE], ___FIX(1));
            }
          else if (key != ___UNUSED)
            body[i] = ___MEM_ALLOCATED_SET(key);
        }

      /*
       * Move the active entries.
       */

      for (i=___GCHASHTABLE_KEY0; i<words; i+=2)
        {
          ___WORD key = body[i];

          if (___MEM_ALLOCATED(key))
            {
              /* this is an active entry that has not been moved yet */

              ___SCMOBJ val = body[i+1];
              ___SCMOBJ obj;
              int probe2;
              int step2;

              body[i] = ___UNUSED;
              body[i+1] = ___UNUSED;

            chain_non_mem_alloc:
              key = ___MEM_ALLOCATED_CLEAR(key); /* recover true encoding */
              probe2 = ___GCHASHTABLE_HASH1(key,size2>>1) << 1;
              step2 = ___GCHASHTABLE_HASH2(key,size2>>1) << 1;

            next_non_mem_alloc:
              obj = body[probe2+___GCHASHTABLE_KEY0];

              if (obj == ___UNUSED)
                {
                  /* storing into an unused entry */

                  body[probe2+___GCHASHTABLE_KEY0] = key;
                  body[probe2+___GCHASHTABLE_VAL0] = val;
                }
              else if (___MEM_ALLOCATED(obj))
                {
                  /* storing into an active entry */

                  body[probe2+___GCHASHTABLE_KEY0] = key;
                  key = obj;
                  obj = body[probe2+___GCHASHTABLE_VAL0];
                  body[probe2+___GCHASHTABLE_VAL0] = val;
                  val = obj;
                  goto chain_non_mem_alloc; /* now move overwritten entry */
                }
              else
                {
                  /* an entry has been moved here, so keep looking */

                  probe2 -= step2;
                  if (probe2 < 0)
                    probe2 += size2;
                  goto next_non_mem_alloc;
                }
            }
        }
    }
  else
    {
      /*
       * Free deleted entries and mark key field of all active
       * entries.
       */

      for (i=___GCHASHTABLE_KEY0; i<words; i+=2)
        {
          ___WORD key = body[i];
          if (key == ___DELETED)
            {
              body[i] = ___UNUSED;
              body[___GCHASHTABLE_FREE] =
                ___FIXADD(body[___GCHASHTABLE_FREE], ___FIX(1));
            }
          else
            body[i] = ___MEM_ALLOCATED_CLEAR(key);
        }

      /*
       * Move the active entries.
       */

      for (i=___GCHASHTABLE_KEY0; i<words; i+=2)
        {
          ___WORD key = body[i];

          if (key != ___UNUSED && !___MEM_ALLOCATED(key))
            {
              /* this is an active entry that has not been moved yet */

              ___SCMOBJ val = body[i+1];
              ___SCMOBJ obj;
              int probe2;
              int step2;

              body[i] = ___UNUSED;
              body[i+1] = ___UNUSED;

            chain_mem_alloc:
              key = ___MEM_ALLOCATED_SET(key); /* recover true encoding */
              probe2 = ___GCHASHTABLE_HASH1(key,size2>>1) << 1;
              step2 = ___GCHASHTABLE_HASH2(key,size2>>1) << 1;

            next_mem_alloc:
              obj = body[probe2+___GCHASHTABLE_KEY0];

              if (obj == ___UNUSED)
                {
                  /* storing into an unused entry */

                  body[probe2+___GCHASHTABLE_KEY0] = key;
                  body[probe2+___GCHASHTABLE_VAL0] = val;
                }
              else if (!___MEM_ALLOCATED(obj))
                {
                  /* storing into an active entry */

                  body[probe2+___GCHASHTABLE_KEY0] = key;
                  key = obj;
                  obj = body[probe2+___GCHASHTABLE_VAL0];
                  body[probe2+___GCHASHTABLE_VAL0] = val;
                  val = obj;
                  goto chain_mem_alloc; /* now move overwritten entry */
                }
              else
                {
                  /* an entry has been moved here, so keep looking */

                  probe2 -= step2;
                  if (probe2 < 0)
                    probe2 += size2;
                  goto next_mem_alloc;
                }
            }
        }
    }
}

___SCMOBJ ___gc_hash_table_ref
   ___P((___SCMOBJ ht,
         ___SCMOBJ key),
        (ht,
         key)
___SCMOBJ ht;
___SCMOBJ key;)
{
  int size2;
  int probe2;
  ___SCMOBJ obj;

  if (!___FIXZEROP(___FIXAND(___FIELD(ht, ___GCHASHTABLE_FLAGS),
                             ___FIX(___GCHASHTABLE_FLAG_KEY_MOVED))))
    ___gc_hash_table_rehash_in_situ (ht);

  size2 = ___INT(___VECTORLENGTH(ht)) - ___GCHASHTABLE_KEY0;
  probe2 = ___GCHASHTABLE_HASH1(key,size2>>1) << 1;
  obj = ___FIELD(ht, probe2+___GCHASHTABLE_KEY0);

  if (___EQP(obj,key))
    return ___FIELD(ht, probe2+___GCHASHTABLE_VAL0);
  else if (!___EQP(obj,___UNUSED))
    {
      int step2 = ___GCHASHTABLE_HASH2(key,size2>>1) << 1;

      for (;;)
        {
          probe2 -= step2;
          if (probe2 < 0)
            probe2 += size2;
          obj = ___FIELD(ht, probe2+___GCHASHTABLE_KEY0);

          if (___EQP(obj,key))
            return ___FIELD(ht, probe2+___GCHASHTABLE_VAL0);
          else if (___EQP(obj,___UNUSED))
            break;
        }
    }

  return ___UNUSED; /* key was not found */
}

___SCMOBJ ___gc_hash_table_set
   ___P((___SCMOBJ ht,
         ___SCMOBJ key,
         ___SCMOBJ val),
        (ht,
         key,
         val)
___SCMOBJ ht;
___SCMOBJ key;
___SCMOBJ val;)
{
  int size2;
  int probe2;
  ___SCMOBJ obj;

  if (!___FIXZEROP(___FIXAND(___FIELD(ht, ___GCHASHTABLE_FLAGS),
                             ___FIX(___GCHASHTABLE_FLAG_KEY_MOVED))))
    ___gc_hash_table_rehash_in_situ (ht);

  size2 = ___INT(___VECTORLENGTH(ht)) - ___GCHASHTABLE_KEY0;
  probe2 = ___GCHASHTABLE_HASH1(key,size2>>1) << 1;
  obj = ___FIELD(ht, probe2+___GCHASHTABLE_KEY0);

  if (!___EQP(val,___ABSENT))
    {
      /* trying to add or replace an entry */

      if (___EQP(obj,key))
        {
        replace_entry:
          ___FIELD(ht, probe2+___GCHASHTABLE_VAL0) = val;
        }
      else if (___EQP(obj,___UNUSED))
        {
        add_entry:
          ___FIELD(ht, probe2+___GCHASHTABLE_KEY0) = key;
          ___FIELD(ht, probe2+___GCHASHTABLE_VAL0) = val;
          ___FIELD(ht, ___GCHASHTABLE_COUNT) =
            ___FIXADD(___FIELD(ht, ___GCHASHTABLE_COUNT), ___FIX(1));
          if (___FIXNEGATIVEP(___FIELD(ht, ___GCHASHTABLE_FREE) =
                                ___FIXSUB(___FIELD(ht, ___GCHASHTABLE_FREE),
                                          ___FIX(1))))
            return ___TRU;
        }
      else
        {
          int step2 = ___GCHASHTABLE_HASH2(key,size2>>1) << 1;
          int deleted2 = -1;

          for (;;)
            {
              if (deleted2 < 0 && ___EQP(obj,___DELETED))
                deleted2 = probe2;

              probe2 -= step2;
              if (probe2 < 0)
                probe2 += size2;
              obj = ___FIELD(ht, probe2+___GCHASHTABLE_KEY0);

              if (___EQP(obj,key))
                goto replace_entry;

              if (___EQP(obj,___UNUSED))
                {
                  if (deleted2 < 0)
                    goto add_entry;

                  ___FIELD(ht, deleted2+___GCHASHTABLE_KEY0) = key;
                  ___FIELD(ht, deleted2+___GCHASHTABLE_VAL0) = val;
                  ___FIELD(ht, ___GCHASHTABLE_COUNT) =
                    ___FIXADD(___FIELD(ht, ___GCHASHTABLE_COUNT), ___FIX(1));

                  break;
                }
            }
        }
    }
  else
    {
      /* trying to delete an entry */

      if (___EQP(obj,key))
        {
        delete_entry:
          ___FIELD(ht, probe2+___GCHASHTABLE_KEY0) = ___DELETED;
          ___FIELD(ht, probe2+___GCHASHTABLE_VAL0) = ___UNUSED;
          ___FIELD(ht, ___GCHASHTABLE_COUNT) =
            ___FIXSUB(___FIELD(ht, ___GCHASHTABLE_COUNT),
                      ___FIX(1));
          if (___FIXLT(___FIELD(ht, ___GCHASHTABLE_COUNT),
                       ___FIELD(ht, ___GCHASHTABLE_MIN_COUNT)))
            return ___TRU;
        }
      else if (!___EQP(obj,___UNUSED))
        {
          int step2 = ___GCHASHTABLE_HASH2(key,size2>>1) << 1;

          for (;;)
            {
              probe2 -= step2;
              if (probe2 < 0)
                probe2 += size2;
              obj = ___FIELD(ht, probe2+___GCHASHTABLE_KEY0);

              if (___EQP(obj,key))
                goto delete_entry;

              if (___EQP(obj,___UNUSED))
                break;
            }
        }
    }

 /*
  * Hash table does not need to be resized.
  */

  return ___FAL;
}

___SCMOBJ ___gc_hash_table_rehash
   ___P((___SCMOBJ ht_src,
         ___SCMOBJ ht_dst),
        (ht_src,
         ht_dst)
___SCMOBJ ht_src;
___SCMOBJ ht_dst;)
{
  ___WORD* body_src = ___BODY_AS(ht_src,___tSUBTYPED);
  long words = ___SCMOBJ_SIZE(body_src[-1]);
  int i;

  for (i=___GCHASHTABLE_KEY0; i<words; i+=2)
    {
      ___WORD key = body_src[i];

      if (key != ___UNUSED &&
          key != ___DELETED)
        ___gc_hash_table_set (ht_dst, key, body_src[i+1]);
    }

  return ht_dst;
}

/* Garbage Collection */

void copy_roots(){
  ___processor_state ___ps = ___PSTATE;
 /* trace registers */
  printf("Trace registers\n");
  mark_array (&___ps->current_thread, 1);
printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  mark_array (&___ps->run_queue, 1);
printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  mark_array (___ps->r, ___NB_GVM_REGS);
printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  mark_array (&___GSTATE->symbol_table, 1);
printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  mark_array (&___GSTATE->keyword_table, 1);
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  /* trace global variables */
  {
    printf("trace global vars\n");
    ___WORD p = ___ps->glo_list_head;

    while (p != 0) {
        mark_array (&___CAST(___glo_struct*,p)->val, 1);
        p = ___CAST(___glo_struct*,p)->next;
    }
    printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  }
  /* trace continuation */
  printf("trace continuation\n");
  mark_continuation ();
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  /* trace reference counted objects */
  printf("trace rc\n");
  mark_rc ();
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  copy_remset(gen0);
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  printf("End copy_roots\n");
}

void partial_collection() {


  printf("Begin partial_collect\n");
  // Flip
  flip(gen0);
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  printf("After Flip\n");

  // Copy roots
  copy_roots();
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  printf("After Roots\n");
  // Scan
  traverse_weak_refs = 0; /* don't traverse weak references in first pass */
 again:
  scanner(gen0);
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  if (!traverse_weak_refs) {
      traverse_weak_refs = 1;
      process_wills ();
      printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
      printf("After wills\n");
      goto again;
  }

  printf("End partial_collect\n");


}
void full_collection() {
  printf("Begin full_collection\n");
  print_gen(gen0);
  full_collect_flag = 1;

  // Tester la taille de la section jeune de gen1 et vieille de gen0.
  long diff = (___YOUNG_SIZE(gen1) + ___OLD_SIZE(gen0)) - ___TOTAL_SIZE(gen1);
  if(diff > 0) {
    // Move old pointer to end. A améliorer.
    gen1->old = gen1->alloc;
  } 

  flip(gen0);
  flip(gen1);

  // Collect here.
  copy_roots();
 
  if (___CAST(___WORD*,still_objs_to_scan) != 0)
    scan_still_objs_to_scan ();

  do {
    scanner(gen0);
    scanner(gen1);
  } while(gen0->scan != gen0->alloc || gen1->scan != gen1->alloc);

  next_heap_msection(gen0);
  next_heap_msection(gen1);

  full_collect_flag = 0;
  printf("End full_collection\n");
}

void print_stack(___WORD * start, ___WORD length) {
  printf("Printing stack: \n");
  int i;
  for(i=0; i<length; i++) {
    printf("%p: %p\n", start, *start);
    ++start;
  }
  printf("End print_stack\n");
}

void remake_stack(___WORD * start) {
  printf("Begin remake_stack\n");
  ___WORD length;
  ___WORD *p1;
  ___WORD *p2;
  ___processor_state ___ps = ___PSTATE;

  length = (___ps->stack_break + ___BREAK_FRAME_SPACE) - start;
  print_stack(___ps->fp, length);
  next_stack_msection();
  
  printf("ps->stack_break: %p, BFS: %p\n", ___ps->stack_break, ___BREAK_FRAME_SPACE);
  //printf("term1: %p, start: %p\n", (___ps->stack_break + ___BREAK_FRAME_SPACE), start);  
  
  p1 = start + length;
  p2 = alloc_stack_ptr;
  
  ___ps->stack_start = alloc_stack_start;
  ___ps->stack_break = p2 - ___BREAK_FRAME_SPACE;

  printf("start: %p, length: %ld\n", start, length);
  printf("p1: %p, p2: %p\n", p1, p2);
  
  while (p1 != start)
    *--p2 = *--p1;
  
  alloc_stack_ptr = p2;  
  ___ps->fp = alloc_stack_ptr;
  print_stack(___ps->fp, length);
  printf("End remake_stack\n");
}


___BOOL ___garbage_collect(long nonmovable_words_needed) {

  printf("\nBegin garbage_collect\n");
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  printf("ps->stack_break: %p, alloc_stack_ptr: %p\n", ___PSTATE->stack_break, alloc_stack_ptr);
  print_stack(___PSTATE->fp, (___PSTATE->stack_break + ___BREAK_FRAME_SPACE) - ___PSTATE->fp);
  long avail;
  int target_nb_sections;
  int stack_msection_index;
  ___BOOL overflow = 0;
  ___F64 user_time_start, sys_time_start, real_time_start;
  ___F64 user_time_end, sys_time_end, real_time_end;
  ___F64 gc_user_time, gc_sys_time, gc_real_time;
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  ___process_times (&user_time_start, &sys_time_start, &real_time_start);

  stack_msection_index = stack_msection->index;
  reached_gc_hash_tables = ___TAG(0,0);
  stack_msection = 0;

  clean_SSB();
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  clear_SSB();
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  /* Determine if partial or full collection */

  printf("___USED_MEM(gen0): %i\n", ___USED_MEM(gen0));
  printf("___FREE_MEM(gen1): %i\n", ___FREE_MEM(gen1));
  printf("___OLD_SIZE(gen0): %i\n", ___OLD_SIZE(gen0));

  if(0){//___FREE_MEM(gen1) >= ___OLD_SIZE(gen0)){ // nursery old fit in movable1
    partial_collection();
  }
  else {
    full_collection();
  }
  printf("gen0->current->base[0]: %p\n", gen0->current->base[0]);
  /* Restore to coherent state */
  process_gc_hash_tables ();
  /* New number of msections */
  /* Move stack */
  /* Adjust msections */
  remake_stack(___PSTATE->fp);

  /* Reset heap msection and alloc_heap_ptr */
  setup_pstate ();

  ___process_times (&user_time_end, &sys_time_end, &real_time_end);

  gc_user_time = user_time_end - user_time_start;
  gc_sys_time = sys_time_end - sys_time_start;
  gc_real_time = real_time_end - real_time_start;

  ___GSTATE->nb_gcs = ___GSTATE->nb_gcs + 1.0;
  ___GSTATE->gc_user_time += gc_user_time;
  ___GSTATE->gc_sys_time += gc_sys_time;
  ___GSTATE->gc_real_time += gc_real_time;

  ___GSTATE->last_gc_user_time = gc_user_time;
  ___GSTATE->last_gc_sys_time = gc_sys_time;
  ___GSTATE->last_gc_real_time = gc_real_time;
  ___GSTATE->last_gc_heap_size = ___CAST(___F64,heap_size) * ___WS;
  ___GSTATE->last_gc_alloc =
    ___GSTATE->bytes_allocated_minus_occupied +
    ___CAST(___F64,WORDS_OCCUPIED) * ___WS;
  ___GSTATE->last_gc_live = ___CAST(___F64,WORDS_OCCUPIED) * ___WS;
  ___GSTATE->last_gc_movable = ___CAST(___F64,WORDS_MOVABLE) * ___WS;
  ___GSTATE->last_gc_nonmovable = ___CAST(___F64,words_nonmovable) * ___WS;

  ___raise_interrupt (___INTR_GC); /* raise gc interrupt */

  printf("End garbage_collect, overflow = %ld\n", overflow);
  return overflow;
}

#ifdef ___DEBUG_HEAP_LIMIT

___BOOL ___heap_limit_debug
   ___P((int line,
         char *file),
        (line,
         file)
int line;
char *file;)

#else

___BOOL ___heap_limit ___PVOID

#endif
{
  ___processor_state ___ps = ___PSTATE;
  long avail;

#ifdef ___DEBUG_HEAP_LIMIT
  ___ps->heap_limit_line = line;
  ___ps->heap_limit_file = file;
#endif

#ifdef ENABLE_CONSISTENCY_CHECKS
  if (___DEBUG_SETTINGS_LEVEL(___setup_params.debug_settings) >= 1)
    check_fudge_used ();
#endif

  alloc_stack_ptr = ___ps->fp; /* needed by 'WORDS_OCCUPIED' */
  alloc_heap_ptr  = ___ps->hp; /* needed by 'WORDS_OCCUPIED' */

  avail = (heap_size - WORDS_OCCUPIED) / 2;

  if (avail > ___MSECTION_WASTE
#ifdef CALL_GC_FREQUENTLY
      && --___gc_calls_to_punt >= 0
#endif
     )
    {
      if (alloc_heap_ptr > alloc_heap_limit - ___MSECTION_FUDGE)
        next_heap_msection (gen0);

      setup_pstate ();

      return 0;
    }

  return 1;
}

#ifdef ___DEBUG_STACK_LIMIT

___BOOL ___stack_limit_debug
   ___P((int line,
         char *file),
        (line,
         file)
int line;
char *file;)

#else

___BOOL ___stack_limit ___PVOID

#endif
{
  ___processor_state ___ps = ___PSTATE;
  long avail;

#ifdef ___DEBUG_STACK_LIMIT
  ___ps->stack_limit_line = line;
  ___ps->stack_limit_file = file;
  ___printf ("___POLL caused ___stack_limit call at %s:%d\n",
             ___ps->poll_file,
             ___ps->poll_line);
#endif

#ifdef ENABLE_CONSISTENCY_CHECKS
  if (___DEBUG_SETTINGS_LEVEL(___setup_params.debug_settings) >= 1)
    check_fudge_used ();
#endif

  alloc_stack_ptr = ___ps->fp; /* needed by 'WORDS_OCCUPIED' */
  alloc_heap_ptr  = ___ps->hp; /* needed by 'WORDS_OCCUPIED' */

  avail = (heap_size - WORDS_OCCUPIED) / 2;

  if (avail > ___MSECTION_WASTE
#ifdef CALL_GC_FREQUENTLY
      && --___gc_calls_to_punt >= 0
#endif
     )
    {
      if (alloc_stack_ptr < alloc_stack_limit + ___MSECTION_FUDGE)
        {
          ___WORD frame;

          if (alloc_stack_ptr != ___ps->stack_break)
            frame = ___CAST(___WORD,alloc_stack_ptr);
          else
            frame = ___FP_STK(alloc_stack_ptr,-___BREAK_FRAME_NEXT);

          next_stack_msection ();

          /*
           * Create a "break frame" in the new stack msection.
           */

          ___ps->stack_start = alloc_stack_start;
          alloc_stack_ptr = alloc_stack_start;

          ___FP_ADJFP(alloc_stack_ptr,___BREAK_FRAME_SPACE)
          ___FP_SET_STK(alloc_stack_ptr,-___BREAK_FRAME_NEXT,frame)

          ___ps->stack_break = alloc_stack_ptr;
        }

      setup_pstate ();

      return 0;
    }

  return 1;
}

