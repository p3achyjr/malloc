/*
 * mm.c
 * 
 * Anatol Liu, axl
 * 15-213 F15
 * 
 * This is a memory allocator based on segregated lists
 *
 * Each list (bin) is a doubly linked list, with the dummy node corresponding
 * to heap_start
 *
 * For block sizes smaller than 64, there are single bins for each list
 * For block sizes greater than or equal to 64, there are bins for each 
 * power of 2, up to 8192. Any block with size greater than 8192 goes into 
 * one list.
 * 
 * On a call to malloc, size is adjusted to account for padding and overhead.
 * This is done by rounding up to the nearest multiple of 8 and adding an
 * additional 8 bytes for header/footer. find_fit is called on the adjusted 
 * size (asize). find_fit is a best-fit search that works as follows:
 *   - Scan each bin starting from the correct bin for a block of at least
 *     asize bytes
 *   - if we find a perfect fit, return immediately
 *   - Otherwise, return the best fit in the first non-empty bin.
 * 
 * place is then called on the best-fit block. This decides whether to split,
 * or simply to return. When we split, we remove the current block from its
 * corresponding bin, and place the new free block in its corresponding bin.
 *
 * 
 * On a call to free, we reset the header and footer, then call coalesce
 * Coalesce inserts the new free block into the root of the corresponding 
 * bin.
 *
 * Coalesce is called immedately and not deferred
 *
 * 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

// #define checkheap(lineno) mm_checkheap(lineno)
#define checkheap(lineno) 

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */
#define NEXT_FITx

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define MINSIZE     16     /* Min block size: 8 for hdr/ftr, 16 for prev/next*/
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */ 
#define END         heap_start 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* GETPTR AND PUTPTR store an offset from heap_start, which will always be
 * <= 2^32. We are interpreting heap_start to be a dummy address */

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define GETPPTR(p)      ((char *)((unsigned long)\
                                (*(unsigned int *)((char *)(p) + WSIZE)) + \
                                  (unsigned long)(END)))
#define GETNPTR(p)      ((char *)((unsigned long)(*(unsigned int *)(p)) + \
                                                   (unsigned long)(END)))         
#define PUT(p, val)     (*(unsigned int *)(p) = (val))
#define PUTPPTR(p, val) (*(unsigned int *)((char *)(p) + WSIZE) = \
                          (unsigned int)((unsigned long)(val) - \
                                         (unsigned long)(END)))
#define PUTNPTR(p, val) (*(unsigned int *)(p) = \
                          (unsigned int)((unsigned long)(val) - \
                                         (unsigned long)(END)))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *heap_listp = 0;    /* Pointer to first block */
static char *heap_start = 0;    /* Start of heap, where there is nothing */
static char *bin_end = 0; /* End of prologue block */
// #ifdef NEXT_FIT
// static char *rover;           /* Next fit rover */
// #endif

/* Function prototypes for internal helper routines */
// void checkheap(int lineno, unsigned long p);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static inline char *getBin(size_t size);
static inline void splitBlk(void *oldptr, size_t asize, size_t csize);

/*
 * set up the header section
 */
void prologue_init(void) {
  unsigned int hdrSize = 30*WSIZE;
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(hdrSize, 1)); /* Prologue header */
  for (int i = 2; i < 29; i+=2) {
    // pointer to next(epilogue) block
    PUTNPTR(heap_listp + (i*WSIZE), END);
    // pointer to prev block
    PUTPPTR(heap_listp + (i*WSIZE), END);
  }
  PUT(heap_listp + (30*WSIZE), PACK(hdrSize, 1)); /* Prologue footer */
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(32*WSIZE)) == (void *)-1) 
      return -1;

  heap_start = heap_listp;
  prologue_init();
  PUT(heap_listp + (31*WSIZE), PACK(0, 1)); // size 0 to signify end
  bin_end = heap_listp + (30*WSIZE);
  heap_listp += (2*WSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  checkheap(__LINE__);
  return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;      

  if (heap_listp == 0){
    mm_init();
  }
  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)                                      
    asize = MINSIZE;                                     
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {  
    place(bp, asize);                  
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);                 
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
    return NULL;                                  
  place(bp, asize); 
  checkheap(__LINE__);                                
  return bp;
}

/*
 * free
 */
void free (void *ptr) {
  if (ptr == 0) 
      return;

  size_t size = GET_SIZE(HDRP(ptr));
  if (heap_listp == 0){
    mm_init();
  }

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
  void *newptr;
  size_t asize;
  size_t oldsize;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    mm_free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return mm_malloc(size);
  }

  oldsize = GET_SIZE(HDRP(oldptr));

  // do a similar thing as place
  if (size <= DSIZE)                                      
    asize = MINSIZE;                                     
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

  
  if (asize <= oldsize) {
    // this means we can simply split the current block or return old block
    splitBlk(oldptr, asize, oldsize);
    return oldptr;
  }

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
      return 0;
  }

  /* Copy the old data. */
  // oldsize = GET_SIZE(HDRP(oldptr));
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  mm_free(oldptr);
  checkheap(__LINE__);
  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *ptr = malloc(bytes);
  memset(ptr, 0, bytes);

  checkheap(__LINE__);
  return ptr;
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
  if ((long)(bp = mem_sbrk(size)) == -1)  
    return NULL;                                        

  /* Initialize free block header/footer and the epilogue header */
  // bp will point to old end of heap

  // fix pointer
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  char *ep_ptr = (char *)NEXT_BLKP(bp);
  PUT(HDRP(ep_ptr), PACK(0, 1));        /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * getBin - get pointer to proper size list
 */
static inline char *getBin(size_t size) {
  if (size < 64) {
    // list for every size
    return (heap_listp + (size - 2*DSIZE));
  } else if (size >= 8192) {
    // one list for blocks of size >= 8192
    // 14 bins, so last one is at DSIZE*13
    return (heap_listp + (DSIZE*13));
  }

  // powers of 2
  int offset = 0;
  while (size >>= 1) offset ++;
  return (heap_listp + (DSIZE*offset));
}

/*
 * coalesceNext - coalesce for case 2
 */
static inline void coalesceNext(void *bp, size_t size) {
  char *next;
  char *first_blk;
  char *bin;
  char *next_next = END;
  char *next_prev = END;
  next = NEXT_BLKP(bp);
  size += GET_SIZE(HDRP(next));
  bin = getBin(size);
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));

  // if next is not epilogue, get next and prev
  if (next != NULL && (unsigned long)HDRP(next) != 1) {
    next_next = GETNPTR(next);
    next_prev = GETPPTR(next);
  }

  // reset pointers
  if (next_next != END) {
    PUTPPTR(next_next, next_prev);
  }
  if (next_prev != END) {
    PUTNPTR(next_prev, next_next);
  }

  // get first block (we do it here to avoid nasty edge cases)
  first_blk = GETNPTR(bin);

  // insert bp into root of list
  PUTNPTR(bp, first_blk);
  PUTPPTR(bp, bin);
  PUTNPTR(bin, bp);
  if (first_blk != END) {
    PUTPPTR(first_blk, bp);
  }
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * I'm not entirely sure why the modularity of code is so poor, but I went
 * with the 4 case model presented in the lecture slides.
 */
static void *coalesce(void *bp) 
{
  char *next;
  char *first_blk;
  char *bin;
  char *prev_bin;
  char *next_next = END;
  char *next_prev = END;
  char *prev_next = END;
  char *prev_prev = END;
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  bp = (char *)bp;

  if (prev_alloc && next_alloc) {            /* Case 1 */
    // get bin to put block
    bin = getBin(size);
    // get first block of bin
    first_blk = GETNPTR(bin);
    PUTNPTR(bp, first_blk); // next is first block
    PUTPPTR(bp, bin); // prev is start of list
    if (first_blk != END) {
      PUTPPTR(first_blk, bp); // first_blk prev is bp
    }
    PUTNPTR(bin, bp); // heap_listp next is bp
    return bp;
  }

  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    coalesceNext(bp, size);
  }

  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bin = getBin(size);
    // prev_bin is bin that previous block is currently in
    prev_bin = getBin(GET_SIZE(HDRP(PREV_BLKP(bp))));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);

    first_blk = GETNPTR(bin);
    // if bp == first_blk and bp is the proper size, return bp
    if (((unsigned long)first_blk == (unsigned long)bp) && prev_bin == bin) 
      return bp;

    // get next and prev for bp, which is the original prev block
    prev_prev = GETPPTR(bp);
    prev_next = GETNPTR(bp);

    // reset pointers
    if (prev_prev != END) {
      PUTNPTR(prev_prev, prev_next);
    }
    if (prev_next != END) {
      PUTPPTR(prev_next, prev_prev);
    }

    // insert bp into root of bin
    PUTNPTR(bp, first_blk);
    PUTPPTR(bp, bin);
    PUTNPTR(bin, bp);
    if (first_blk != END) {
      PUTPPTR(first_blk, bp);
    }
  }

  else {                                     /* Case 4 */
    next = NEXT_BLKP(bp);
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
        GET_SIZE(FTRP(next));
    bin = getBin(size);
    prev_bin = getBin(GET_SIZE(HDRP(PREV_BLKP(bp))));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);

    // if next is not epilogue, get next and prev
    if (next != NULL && (unsigned long)HDRP(next) != 1) {
      next_next = GETNPTR(next);
      next_prev = GETPPTR(next);
    }

    // reset pointers
    if (next_next != END) {
      PUTPPTR(next_next, next_prev);
    }
    if (next_prev != END) {
      PUTNPTR(next_prev, next_next);
    }

    // get first block (we do it here to avoid nasty edge cases)
    first_blk = GETNPTR(bin);
    if (((unsigned long)first_blk == (unsigned long)bp) && prev_bin == bin) 
      return bp;

    // get next and prev for bp, which is the original prev block
    prev_prev = GETPPTR(bp);
    prev_next = GETNPTR(bp);

    // reset pointers
    if (prev_prev != END) {
      PUTNPTR(prev_prev, prev_next);
    }
    if (prev_next != END) {
      PUTPPTR(prev_next, prev_prev);
    }

    // insert bp into root of list
    PUTNPTR(bp, first_blk);
    PUTPPTR(bp, bin);
    PUTNPTR(bin, bp);
    if (first_blk != END) {
      PUTPPTR(first_blk, bp);
    }
  }
  checkheap(__LINE__);
  return (void*)bp;
}

/* 
 * splitBlk - Split a block that is allocated. When realloc is called and
 *            asize <= csize
 */
static inline void splitBlk(void *oldptr, size_t asize, size_t csize) {
  if (csize - asize < MINSIZE) {
    // do nothing
    return;
  }

  // otherwise, split and add new free block to beginning of bin
  PUT(HDRP(oldptr), PACK(asize, 1));
  PUT(FTRP(oldptr), PACK(asize, 1));

  size_t newsize = csize - asize;
  char *nextptr = NEXT_BLKP(oldptr);
  // char *bin = getBin(newsize);
  // char *first_blk = GETNPTR(bin);

  PUT(HDRP(nextptr), PACK(newsize, 0));
  PUT(FTRP(nextptr), PACK(newsize, 0));
  coalesce(nextptr);

  // insert new free block into bin
  // PUTNPTR(nextptr, first_blk);
  // PUTPPTR(nextptr, bin);
  // PUTNPTR(bin, nextptr);
  // if (first_blk != END) {
  //   PUTPPTR(first_blk, nextptr);
  // }
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
  char *bin;
  char *first_blk;
  size_t csize = GET_SIZE(HDRP(bp));
  char *next = GETNPTR(bp);
  char *prev = GETPPTR(bp);

  if ((csize - asize) >= MINSIZE) {
    // allocate the block
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    
    bp = NEXT_BLKP(bp);
    // new header and footer
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    bin = getBin(csize - asize);

    // fix pointers of next and prev blocks
    if (prev != END) {
      PUTNPTR(prev, next);
    }
    if (next != END) {
      PUTPPTR(next, prev);
    }
    // insert new free block into root of correct bin
    first_blk = GETNPTR(bin);
    PUTNPTR(bp, first_blk);
    PUTPPTR(bp, bin);
    PUTNPTR(bin, bp);
    if (first_blk != END) {
      PUTPPTR(first_blk, bp);
    }
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    // fix pointers of bin
    if (prev != END) {
      PUTNPTR(prev, next);
    }
    if (next != END) {
      PUTPPTR(next, prev);
    }
  }
}

/* 
 * find_fit - Find a fit for a block with asize bytes
 * Best fit find
 */
static void *find_fit(size_t asize)
{
  /* First-fit search */
  void *bp;
  void *best_fit;
  size_t currBlkSize;
  size_t diff = 0x80000000; // largest possible difference in heap
  char *bin = getBin(asize);

  for (; bin != bin_end; bin += DSIZE) {
    best_fit = bin;
    for (bp = bin; bp != END; bp = (void*)GETNPTR(bp)) {
      currBlkSize = GET_SIZE(HDRP(bp));
      if (!GET_ALLOC(HDRP(bp)) && (asize == currBlkSize)) {
        // perfect fit
        return bp;
      } else if (!GET_ALLOC(HDRP(bp)) && (asize < currBlkSize)) {
        // if this is true, we have found a better fit
        if (currBlkSize - asize < diff) {
          diff = currBlkSize - asize;
          best_fit = bp;
        }
      }
    }
    // only case in which best_fit == bin is if list is empty
    if (best_fit != bin)
      return best_fit;
  }
  return NULL; /* No fit */
// #endif
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
  return (size_t)ALIGN(p) == (size_t)p;
}

void check_prev_next(char *bp, int lineno) {
  char *next = (char*)GETNPTR(bp);
  char *prev = (char*)GETPPTR(bp);

  // check freeness
  if (next != END && GET_ALLOC(HDRP(next))) {
    fprintf(stderr, "Error, next block (%lx) not free (%d)\n", 
            (unsigned long)next, lineno);
    exit(-1);
  }
  if (next != END) {
    if (!in_heap(next)) {
      fprintf(stderr, "Error: next block (%lx) not in heap (%d)\n", 
              (unsigned long)next, lineno);
      exit(-1);
    }
    if (GETPPTR(next) != bp) {
      fprintf(stderr, "Error: next block (%lx) prev pointer is wrong (%d)\n", 
             (unsigned long)next, lineno);
      exit(-1);
    }
  }
  if (prev != END && prev != heap_listp && GET_ALLOC(HDRP(prev))) {
    fprintf(stderr, "Error, previous block (%lx) not free (%d)\n", 
           (unsigned long)prev, lineno);
    exit(-1);
  }
  if (prev != END && prev != heap_listp) {
    if (!in_heap(prev)) {
      fprintf(stderr, "Error: previous block (%lx) not in heap (%d)\n",
             (unsigned long)prev, lineno);
      exit(-1);
    }
    if (GETNPTR(prev) != bp) {
      fprintf(stderr, "Error: prev block (%lx) next pointer is wrong (%d)\n",
             (unsigned long)prev, lineno);
      exit(-1);
    }
  }
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
  int alloc;

  int free_blks = 0;
  int free_list_blks = 0;
  char *bp = heap_listp;
  int lastAlloc = 1;
  // iterate through heap and check consistency
  for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {

    // check block alignment
    if (!aligned(bp)) {
      fprintf(stderr, "Error: block %lx is not aligned (%d)\n", 
             (unsigned long)bp, lineno);
      exit(-1);
    }

    // check in heap
    if (!in_heap(bp)) {
      fprintf(stderr, "Error: block %lx is not aligned (%d)\n", 
             (unsigned long)bp, lineno);
      exit(-1);
    }

    // check header/footer consistency
    if (!(GET(HDRP(bp)) == GET(FTRP(bp)))) {
      fprintf(stderr, "Error: block %lx header/footer do not agree (%d)\n", 
             (unsigned long)bp, lineno);
      exit(-1);
    }

    // check allocation state
    alloc = GET_ALLOC(HDRP(bp));
    if (!lastAlloc && !alloc) {
      fprintf(stderr, 
             "Error, two consecutive free blocks at addresses %lx, %lx (%d)\n",
             (unsigned long)PREV_BLKP(bp), (unsigned long)(bp), lineno);
      exit(-1);
    }
    lastAlloc = alloc;

    // check previous and next in list
    if (!alloc) {
      free_blks++;
    }
  }

  // check free list
  char *currBin;
  for (char *bin = getBin(16); bin != bin_end; bin += DSIZE) {
    for (bp = bin; bp != END; bp = (char*)GETNPTR(bp)) {
      // check consistency of prev/next pointers
      check_prev_next(bp, lineno);
      // check that current block is free
      if (bp != heap_listp && GET_ALLOC(HDRP(bp))) {
        fprintf(stderr, "Error: block not free, but in free list (%lx) (%d)\n",
               (unsigned long)bp, lineno);
        exit(-1);
      }

      if (bp != bin) {
        currBin = getBin(GET_SIZE(HDRP(bp)));
        if (currBin != bin) {
          fprintf(stderr, "Error: block (%lx) not in correct bin (%d)\n",
                 (unsigned long)bp, lineno);
          exit(-1);
        }
      }

      if (!in_heap(bp)) {
        fprintf(stderr, "Error: free block not in heap (%lx) (%d)\n",
               (unsigned long)bp, lineno);
        exit(-1);
      }

      if (bp != bin)
        free_list_blks++;
    }
  }

  if (free_blks != free_list_blks) {
    fprintf(stderr, 
            "Error: free_blks (%d) and free_list_blks (%d) do not match (%d)\n",
            free_blks, free_list_blks, lineno);
    exit(-1);
  }
  printf("ALL CLEAR(%d)\n", lineno);
}


// tests
// int main() {
//   mm_init();
//   printf("%lx", (unsigned long)heap_listp);
//   return 0;
// }






















