/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
// #define NEXT_FIT 1

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

#define GET_NEXT_FREE(bp) (size_t) GET(bp)
#define GET_PREV_FREE(bp) (size_t) GET(bp + WSIZE)

#define SET_NEXT_FREE(bp, prevp) PUT(bp, (size_t)prevp)
#define SET_PREV_FREE(bp, nextp) PUT(bp + WSIZE, (size_t)nextp)

#define SET_PREV_FREES_PREV(bp, prevp) SET_PREV_FREE(GET_PREV_FREE(bp), (size_t)prevp)
#define SET_PREV_FREES_NEXT(bp, nextp) SET_NEXT_FREE(GET_PREV_FREE(bp), (size_t)nextp)

#define SET_NEXT_FREES_PREV(bp, prevp) SET_PREV_FREE(GET_NEXT_FREE(bp), (size_t)prevp)
#define SET_NEXT_FREES_NEXT(bp, nextp) SET_NEXT_FREE(GET_NEXT_FREE(bp), (size_t)nextp)

#define CREATE_2WAY_LINK(thisbp, nextbp) SET_NEXT_FREE(thisbp, nextbp); SET_PREV_FREE(nextbp, thisbp);

/* $end mallocmacros */

/* Global variables */
static char *free_list_root_p;
static char *heap_listp;  /* pointer to first block */  

int DEBUG_MODE = 0;
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
static void printblock(void *bp); 
static void checkblock(void *bp);

// more helpers that we made 
static void dissociateBlockFromList(void* bp);
static void printFreelist(void);
static void printblockExtra(void *bp);

char hasFinishedInit;

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) {
    // TODO this global jank 
    hasFinishedInit = 0;
    // condprintf("<MM_INIT>\n");

    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */

    heap_listp += DSIZE;
    // The free list will refer to the first free memory block.
    free_list_root_p = heap_listp + DSIZE;


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;

    // UNUSED
    
    // PUT(heap_listp+WSIZE,heap_listp+DSIZE); // next pointer to first free block
    // PUT(heap_listp,heap_listp-WSIZE); // next pointer from first free block to end of list
    // PUT(heap_listp+WSIZE,heap_listp-DSIZE); // prev pointer from first free block to beginning of list
    // set up the first free memory block with null refs to next and prev.

    // TODO this global jank 
    hasFinishedInit = 1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    // condprintf("<MALLOC>\n");
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
	//TODO prints
	// condprintf("at the end of malloc where we found a fit...\n");
	//printFreelist();
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
	//TODO prints
	// condprintf("at the end of malloc after failing extending heap...\n");
	//printFreelist();
	return NULL;
    }
    place(bp, asize);
    // TODO now let's put the rover in the next spot.
    // rover = NEXT_BLKP(bp);
    //
    // TODO printing the freelist here.
    // condprintf("at the end of malloc after succeeding extending heap...\n");
    //printFreelist();
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    // condprintf("<FREE>\n");
    // // condprintf("freeing...\n");
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    // condprintf("<REALLOC>\n");
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    // condprintf("<EXTEND_HEAP\n");
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
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    // condprintf("<PLACE>\n");
    size_t csize = GET_SIZE(HDRP(bp));   

    // TODO we changed this conditional to gurantee that places will have space for next and prev.
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 

	// condprintf("place case 1: splitting the block.\n");

	
	char* prevThing = (char*)GET_PREV_FREE(bp);
	char* nextThing = (char*)GET_NEXT_FREE(bp);

	char* adjustedBp = (char*)(bp + asize);

	// case 1
	// (root)Y - Z? -> shifted (root)Y - Z?
	// case 2
	// X - Y - Z? -> X - shifted Y - Z?
	
	// case 1 specific
	if(!prevThing) {
	    free_list_root_p = adjustedBp;
	}

	// case 2 specific
	if(prevThing) {
	    SET_NEXT_FREE(prevThing, adjustedBp);
	}

	// both case 1 and 2 handling if there's a next (Z)
	SET_NEXT_FREE(adjustedBp, nextThing);
	SET_PREV_FREE(adjustedBp, prevThing);

	if(nextThing) {
	    SET_PREV_FREE(nextThing, adjustedBp);
	}

	// old, already existed
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
	// condprintf("place case 2: using the entire block.\n");

	//printFreelist();
	// new, link the things on the left and right.
	dissociateBlockFromList(bp);

	// condprintf("root p:%p\n", free_list_root_p);
	//printFreelist();
	// old
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{

    // EXPLICIT FREE LIST SEARCH
    // condprintf("<FIND_FIT>\n");
    
    char *bp;

    // iterate across the free  list, find a spot  that is big enough, and use this.
    // for(bp = free_list_root_p; GET_NEXT_FREE(bp) != 0; bp = GET_NEXT_FREE(bp))
    for(bp = free_list_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp))
    {
	// condprintf("\t iterating in find_fit... bp = %p\n", bp);
	// // condprintf("spinning");
	if(asize <= GET_SIZE(HDRP(bp)))
	{
	    // condprintf("\tfound the fit!\n");
	    return bp;
	}
    }
    return NULL; // no fit found
}

static void insertFreeBlockAtBeginning(void* bp) {
    // case 1
    // (root)null -> (root)X, X.prev = 0, X.next = 0
    if(!free_list_root_p) {
      free_list_root_p = bp;
      SET_PREV_FREE(bp, 0);
      SET_NEXT_FREE(bp, 0);
    }

    // case 2
    // (root)Y -> (root)X, X <=> Y, X.prev = 0, 
    else {
      SET_PREV_FREE(bp, 0);
      CREATE_2WAY_LINK(bp, free_list_root_p);
      free_list_root_p = bp;
    }
}

static void dissociateBlockFromList(void* bp) {

    // // condprintf("dissociating a block...\n");

    char* prevThing = (char*)GET_PREV_FREE(bp);
    char* nextThing = (char*)GET_NEXT_FREE(bp);

    // Case 1
    //  (root)Y - Z -> (root)Z
    if(!prevThing && nextThing) {
	SET_PREV_FREE(nextThing, 0);
	free_list_root_p = nextThing;
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
	// // condprintf("hitting the zero case\n");
	free_list_root_p = 0;
    }
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    // // condprintf("prealesce...\n");
    // //printFreelist();
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(!hasFinishedInit) { /* Case 0 */
	// condprintf("-coalesce case 0\n");
	//printFreelist();
	return bp;
    }
    else if (prev_alloc && next_alloc) {            /* Case 1 */
	// condprintf("-coalesce case 1\n");
	// new
	insertFreeBlockAtBeginning(bp);
	//printFreelist();
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	// condprintf("-coalesce case 2\n");

	dissociateBlockFromList(NEXT_BLKP(bp));

	insertFreeBlockAtBeginning(bp);

	// old
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	// condprintf("-coalesce case 3\n");

	dissociateBlockFromList(PREV_BLKP(bp));

	// old
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

	// NOTE: this comes after because it needs to operate on the prev location.
	insertFreeBlockAtBeginning(bp);
    }

    else {                                     /* Case 4 */
	// condprintf("-coalesce case 4\n");

	dissociateBlockFromList(PREV_BLKP(bp));
	dissociateBlockFromList(NEXT_BLKP(bp));

	// old
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

	insertFreeBlockAtBeginning(bp);
    }

    //printFreelist();
    return bp;
}



static void printFreelist(void) {
    // condprintf("\tthe current list:\n");

    if(free_list_root_p) {
      // condprintf("\tfree_list_root_p: %p, *free_list_root_p: %x\n", free_list_root_p, *(size_t*)free_list_root_p);
    } else {
      // condprintf("\tfree_list_root_p = 0!!\n");
    }
    // iterate across the free list and print the blocks.
    char *bp;

    // iterate across the free  list, find a spot  that is big enough, and use this.
    // for(bp = free_list_root_p; GET_NEXT_FREE(bp) != 0; bp = GET_NEXT_FREE(bp))
    for(bp = free_list_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp))
    {
	// // condprintf("(next bp is %p)\n", bp);
	printblockExtra(bp);
    }
    // // condprintf("(end of list)\n");
}

static void printblockExtra(void *bp) 
{
    size_t hsize, halloc, fsize, falloc, next, prev;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
	
    // // condprintf("getting the footer\n");
    fsize = GET_SIZE(FTRP(bp));
    // // condprintf("got the footer\n");
    falloc = GET_ALLOC(FTRP(bp));  
    next = GET_NEXT_FREE(bp);
    prev = GET_PREV_FREE(bp);  
    
    if (hsize == 0) {
	// condprintf("%p: EOL\n", bp);
	return;
    }

    condprintf("\t\t> bp: %p, *bp: %x, header: [%d:%c] footer: [%d:%c] next:%x prev: %x\n",
 	   bp, 
 	   *(size_t*)bp,
 	   hsize, (halloc ? 'a' : 'f'), 
 	   fsize, (falloc ? 'a' : 'f'),
 	   next, prev); 
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

