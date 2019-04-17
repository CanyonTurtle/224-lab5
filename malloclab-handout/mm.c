/* 
 * Cannon Tuttle - tutt07
 * Ethan Williams - ewilli24
 *
 * This allocator uses segregated free-lists in order to store all the free blocks.
 * We first implemented an explicit free-lists, then split it into two parts, and added conditions
 * to have these parts become small and large sized free-lists independent of each other.
 *
 * The free-lists store next and previous pointers in the first two words of the payload which are
 * accessed and manipulated by various functions in this code.
 *
 * Our freelists have the format:
 *
 * +----------------------+--------+------+-----------+---------------------------------+---------+------------------+
 * |         Word         |  Word  | Word |   Word    | free_list_(small|large)_pointer |  Word   |       Word       |
 * +----------------------+--------+------+-----------+---------------------------------+---------+------------------+
 * | (...Previous Footer) | Header | Next | Previous  | Data....                        | Footer  | (Next header...) |
 * +----------------------+--------+------+-----------+---------------------------------+---------+------------------+
 *
 * See the function headers and bodies for more detailed information about the workings of the program.
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/* Team structure */
team_t team = {
    "tutt07+ewilli24",
    "Cannon Tuttle", "tutt07",
    "Ethan Williams", "ewilli24"
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<14)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// gets the next or previous free block from the free list of bp
#define GET_NEXT_FREE(bp) (size_t) GET(bp)
#define GET_PREV_FREE(bp) (size_t) GET(bp + WSIZE)

// sets the next or previous free block of bp
#define SET_NEXT_FREE(bp, prevp) PUT(bp, (size_t)prevp)
#define SET_PREV_FREE(bp, nextp) PUT(bp + WSIZE, (size_t)nextp)

// sets this next to the next block and next's prev to this block
#define CREATE_2WAY_LINK(thisbp, nextbp) SET_NEXT_FREE(thisbp, nextbp); SET_PREV_FREE(nextbp, thisbp)

// checks size for segregated free-lists
#define IS_SMALL(size) (size <= 192)

// checks address to determine which free-list a block is in
#define IS_IN_SMALL_REGION(ptr) ((char*)ptr < interlude_p)

// prints error-checking code
#define DEBUG_HEAPS(msg) \
	condprintf("\tfree_list_small_root_p: " msg "\n");\
	mm_checkheap(1)

/* $end mallocmacros */

/* Global variables */
char *free_list_small_root_p; // the segregated list pointer for small items: size <= 192
char *free_list_large_root_p; // the segregated list pointer for the big items: size > 192
char hasFinishedInit; // used for a special case of coalescing in the beginning.
char* interlude_p; // used to delineate the two lists
char *heap_listp;  /* pointer to first block */  

// determines whether conditional prints run
int DEBUG_MODE = 1;
#define condprintf(str, ...) { \
  if(DEBUG_MODE) { \
    printf(str, ##__VA_ARGS__); \
  } \
}

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void checkblock(void *bp);

// more helpers that we made 
static void dissociateBlockFromList(void* bp);
static void insertFreeBlockAtBeginning(void* bp);
static void condPrintblockExtra(void *bp);

// forward dec of the checker
void mm_checkheap(int verbose);

/* 
 * Initializes two free-lists by allocating space for smaller blocks in the first part of
 * the heap. Keeps large and small blocks separate using a small allocated block in between
 * the main sections of the heap. Initializes root pointers to the first two free blocks.
 */
/* $begin mminit */
int mm_init(void) {

    // handles a special case of coalescing. 
    hasFinishedInit = 0;

    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */

    heap_listp += DSIZE;

    // 25 % of the heap storage initially is for the small list.
    if ((free_list_small_root_p = extend_heap(CHUNKSIZE/WSIZE/4)) == NULL)
	return -1;

    // initialize the links in the new small linked list
    SET_NEXT_FREE(free_list_small_root_p, 0);
    SET_PREV_FREE(free_list_small_root_p, 0);

    // this "interlude_p" is used to delineate the two lists, just like a prologue header/footer.
    interlude_p = NEXT_BLKP(free_list_small_root_p) - WSIZE - DSIZE;
    PUT(interlude_p, PACK(OVERHEAD, 1)); /* interlude header */
    PUT(interlude_p + WSIZE, PACK(OVERHEAD, 1)); /* interlude footer */

    // resize the small list to put an interim separator, so that the lists cannot enter eachother.
    size_t newSmallSize = (size_t)GET_SIZE(HDRP(free_list_small_root_p)) - (size_t)DSIZE;
    char smallAlloc = GET_ALLOC(HDRP(free_list_small_root_p));
    PUT(HDRP(free_list_small_root_p), PACK(newSmallSize, smallAlloc));
    PUT(FTRP(free_list_small_root_p), PACK(newSmallSize, smallAlloc));

    // 75 % of the heap storage initially is for the large lists.
    if ((free_list_large_root_p = extend_heap(CHUNKSIZE/WSIZE/4 * 3)) == NULL)
	return -1;

    // initialize the links in the large list.
    SET_NEXT_FREE(free_list_large_root_p, 0);
    SET_PREV_FREE(free_list_large_root_p, 0);

    // handles a special case of coalescing.
    hasFinishedInit = 1;

    // mm_checkheap(1);
    return 0;
}
/* $end mminit */

/* 
 * Allocates a DWORD-aligned block with a payload of at least the specified size.
 * First adjusts the size to ensure it is DWORD-aligned. Then searches free-lists for
 * a fit. If it doesn't find a fit it extends the heap and finally allocates that
 * space.
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
	return NULL;
    }
    place(bp, asize);

    return bp;
} 
/* $end mmmalloc */

/* 
 * Removes a block from memory. Sets header and footer to free to show block is free
 * and attempts to coalesce the newly freed blocks with surrounding free blocks if
 * any.
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - uses 2 possible cases.
 * 	case 1: if the new size will fit in what's availible already,
 * 	it simply stays in place.
 *      case 2: if there's a next free block and the combined storage
 *      is enough to store this block too, then coalesce with that block
 *      and store it here.
 *      default: finds a different free block, copy the memory over,
 *      and free the current block
 */
void *mm_realloc(void *ptr, size_t size)
{
    // special case: if null, simply perform a malloc.
    if(ptr == NULL) {
      void* newp;
      if ((newp = mm_malloc(size)) == NULL) {
	  printf("ERROR: mm_malloc failed in mm_realloc\n");
	  exit(1);
      }
      return newp;
    }

    // special case: if size is 0, simply free the memory.
    if(size == 0) {
      mm_free(ptr);
      return 0;
    }

    // adjusted size value which is 8-byte aligned and stores the overhead.
    size_t asize;

    // we need to keep track of these two spots, because we re-use some 
    // functionality from coalescing, which assumes these spots are 
    // free to modify. So, these get saved and restored later.
    size_t firstWord = GET_NEXT_FREE(ptr);
    size_t secondWord = GET_PREV_FREE(ptr);

    // some information necessary for the various conditions.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t thisBlockSize = GET_SIZE(HDRP(ptr));
    size_t nextBlockSize =  GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    // case 1: just use the in-place memory.
    if(thisBlockSize >= asize + OVERHEAD) {

	// mark the memory as free so it can be managed by the place() function
	size_t duringCoalesceSize = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(duringCoalesceSize, 0));
	PUT(FTRP(ptr), PACK(duringCoalesceSize, 0));

	// re-used from coalesce, this will get the memory split if necessary.
	insertFreeBlockAtBeginning(ptr);
	place(ptr, asize + OVERHEAD);

	// re-substitute the memory that was at the next and prev locations.
	SET_NEXT_FREE(ptr, firstWord);
	SET_PREV_FREE(ptr, secondWord);

	return ptr;
    }
    else if (!next_alloc && (thisBlockSize + nextBlockSize >= asize)) {            /* Case 2 */

	// mark the memory as free so it can be managed by the place() function
	size_t duringCoalesceSize = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(duringCoalesceSize, 0));
	PUT(FTRP(ptr), PACK(duringCoalesceSize, 0));

	thisBlockSize += nextBlockSize;

	// re-used from coalesce, this will get the memory coalesced and split.
	dissociateBlockFromList(NEXT_BLKP(ptr));
	insertFreeBlockAtBeginning(ptr);

	// update the size of the block and set it to free.
	PUT(HDRP(ptr), PACK(thisBlockSize, 0));
	PUT(FTRP(ptr), PACK(thisBlockSize, 0));

	place(ptr, asize);

	// re-substitute the memory that was at the next and prev locations.
	SET_NEXT_FREE(ptr, firstWord);
	SET_PREV_FREE(ptr, secondWord);

	return ptr;
    }


    // default case: the naive realloc implementation.
    void *newp;
    size_t copySize;

    // allocate new memory spot.
    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }

    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize) {
	copySize = size;
    }

    // move the memory over
    memcpy(newp, ptr, copySize);

    mm_free(ptr);
    return newp;
}

/* 
 * Checks the heap to determine if headers and footers are consistent
 * and to see if blocks overlap. runs through both free-lists. Also 
 * checks prologue header and footer as well as the epilogue header.
 */
void mm_checkheap(int verbose) 
{

    printf("\n\n\nprinting the heap:\n");

    // SMALL LIST
    // ------
    //
    char *bp = free_list_small_root_p;

    // print the head information.
    if (verbose)
	condprintf("\tfree_list_small_root_p (%p):\n", free_list_small_root_p);

    // Iterate across the list and verify that each block is valid.
    for (bp = free_list_small_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp)) {
	if (verbose) 
	    condPrintblockExtra(bp);
	checkblock(bp);
    }

    // LARGE LIST
    // ------
    //
    bp = free_list_large_root_p;


    // print the head information.
    if (verbose)
	condprintf("\tfree_list_large_root_p (%p):\n", free_list_large_root_p);

    // Iterate across the list and verify that each block is valid.
    for (bp = free_list_large_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp)) {
	if (verbose) 
	    condPrintblockExtra(bp);
	checkblock(bp);
    }

    // ENTIRE THING
    bp = (char*) heap_listp;

    // print the head information.
    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    // verify that the header works.
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    // iterate over every block in the heap until the end, check the blocks.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    condPrintblockExtra(bp);
	checkblock(bp);
    }
     
    // check the epilogue header
    if (verbose)
	condPrintblockExtra(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");

}

/* The remaining routines are internal helper routines */

/* 
 * Extends the heap with a new free block, coalesces it with the heap if possible
 * and returns its block pointer.
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * Allocates a block at the specified free block. If there is a remainder
 * it pushes the free block pointers to what is still free. Otherwise just
 * dissociates the free block from the list.
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    // can we fit this block here WITH leftover free space?
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 

	// information about the block.
	char* prevThing = (char*)GET_PREV_FREE(bp);
	char* nextThing = (char*)GET_NEXT_FREE(bp);

	// the new location of the free block after what's being placed.
	void* adjustedBp = (void*)(bp + asize);

	// case 1
	// (root)Y - Z? -> shifted (root)Y - Z?
	// case 2
	// X - Y - Z? -> X - shifted Y - Z?
	
	// case 1 specific
	if(!prevThing) {
	    if(IS_IN_SMALL_REGION(bp)) {
	      free_list_small_root_p = adjustedBp;
	    } else {
	      free_list_large_root_p = adjustedBp;
	    }
	}

	// case 2 specific
	if(prevThing) {
	    SET_NEXT_FREE(prevThing, adjustedBp);
	}

	// both case 1 and 2, setting the list links and handling if there's a next (Z)
	SET_NEXT_FREE(adjustedBp, nextThing);
	SET_PREV_FREE(adjustedBp, prevThing);
	if(nextThing) {
	    SET_PREV_FREE(nextThing, adjustedBp);
	}

	// adjusting the size/alloc flags of the blocks.
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 

	// link the things on the left and right.
	dissociateBlockFromList(bp);

	// set the new alloc flags of this block.
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * Finds a fit for a new block. If it is small, first checks the small list. Then both
 * small and large blocks check the large list. If there are no free blocks large enough,
 * returns NULL to show need for extending the heap.
 */
void *find_fit(size_t asize)
{
    char *bp;

    // iterate across the free list, find a spot that is big enough, and use this.
    if(IS_SMALL(asize)) {
      for(bp = free_list_small_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp)) {
	  if(asize <= GET_SIZE(HDRP(bp))) {
	      return bp;
	  }
      }
    }

    // fallthrough to the larger freelist.
    for(bp = free_list_large_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp)) {
	if(asize <= GET_SIZE(HDRP(bp))) {
	    return bp;
	}
    }
    return NULL; // no fit found
}

/*
 * Inserts a free block at the beginning of the appropriate free-list. If it is in
 * the small region, places at beginning of the small free-list, otherwise in the 
 * large free-list.
*/
static void insertFreeBlockAtBeginning(void* bp) {

    // case 1
    // (root)null -> (root)X, X.prev = 0, X.next = 0
    if(IS_IN_SMALL_REGION(bp)) {
      if(!free_list_small_root_p) {
	free_list_small_root_p = bp;
	SET_PREV_FREE(bp, 0);
	SET_NEXT_FREE(bp, 0);
      }

      // case 2
      // (root)Y -> (root)X, X <=> Y, X.prev = 0, 
      else {
	SET_PREV_FREE(bp, 0);
	CREATE_2WAY_LINK(bp, free_list_small_root_p);
	free_list_small_root_p = bp;
      }

    } else {

      if(!free_list_large_root_p) {
	free_list_large_root_p = bp;
	SET_PREV_FREE(bp, 0);
	SET_NEXT_FREE(bp, 0);
      }

      // case 2
      // (root)Y -> (root)X, X <=> Y, X.prev = 0, 
      else {
	SET_PREV_FREE(bp, 0);
	CREATE_2WAY_LINK(bp, free_list_large_root_p);
	free_list_large_root_p = bp;
      }

    }
}

/*
 * Removes a free block from the appropriate free-list, again using the region to
 * determine which free-list to remove from. Special cases included for if there is
 * no previous and/or next block.
*/
static void dissociateBlockFromList(void* bp) {

    // get refs to the links surrounding this block.
    char* prevThing = (char*)GET_PREV_FREE(bp);
    char* nextThing = (char*)GET_NEXT_FREE(bp);

    // Case 1
    //  (root)Y - Z -> (root)Z
    if(!prevThing && nextThing) {
	SET_PREV_FREE(nextThing, 0);
	if(IS_IN_SMALL_REGION(bp)) {
	  free_list_small_root_p = nextThing;
	} else {
	  free_list_large_root_p = nextThing;
	}
    }

    // case 2
    // X - Y - O -> X
    else if(prevThing && !nextThing) {
	SET_NEXT_FREE(prevThing, 0);
    }

    // case 3
    // X - Y - Z -> X ---- Z
    else if(prevThing && nextThing) {
	CREATE_2WAY_LINK(prevThing, nextThing);
    }

    // case 4
    // (root)Y -> (root is null)
    else {
	if(IS_IN_SMALL_REGION(bp)) {
	  free_list_small_root_p = 0;
	} else {
	  free_list_large_root_p = 0;
	}
    }
}


/*
 * Attempts to combine a newly freed block with surrounding free blocks. Four
 * cases based on whether the previous and next blocks are allocated or free.
 * Includes modifying boundary tags based on size and which blocks were combined.
 */
static void *coalesce(void *bp) 
{

    // information about the surrounding blocks.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(!hasFinishedInit) { // Case 0 
	return bp;
    }
    else if (prev_alloc && next_alloc) {            /* Case 1 */
	insertFreeBlockAtBeginning(bp);
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */

	// break links off of the next thing
	dissociateBlockFromList(NEXT_BLKP(bp));

	// insert this block into a freelist.
	insertFreeBlockAtBeginning(bp);

	// expand the size of the block.
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */

	// break links off of the next thing
	dissociateBlockFromList(PREV_BLKP(bp));

	// expand this block and move the starting index.
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

	// insert into a freelist.
	insertFreeBlockAtBeginning(bp);
    }
    else {                                     /* Case 4 */

	// break BOTH side's links.
	dissociateBlockFromList(PREV_BLKP(bp));
	dissociateBlockFromList(NEXT_BLKP(bp));

	// expand the block and move the starting index.
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

	// insert into freelist.
	insertFreeBlockAtBeginning(bp);
    }

    return bp;
}

/*
 * Prints helpful information about given block. Used for debugging.
*/
static void condPrintblockExtra(void *bp) 
{
    size_t hsize, halloc, fsize, falloc, next, prev;

    // a bunch of facts about this block.
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    next = GET_NEXT_FREE(bp);
    prev = GET_PREV_FREE(bp);  
    
    // don't print null blocks.
    if (hsize == 0) {
	printf("\t%p: EOL\n", bp);
	return;
    }

    // print all the facts.
    printf("\t\t> bp: %p, *bp: %x, header: [%d:%c] footer: [%d:%c] next:%x prev: %x\n",
 	   bp, 
 	   *(size_t*)bp,
 	   hsize, (halloc ? 'a' : 'f'), 
 	   fsize, (falloc ? 'a' : 'f'),
 	   next, prev); 
}

/*
 * Checks if given block is DWORD-aligned and if header and footer match.
 * Used for debugging.
*/
void checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
	printf("Error: %p is not doubleword aligned\n", bp);
	exit(1);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
	printf("Error: header does not match footer\n");
	exit(1);
    }
}

