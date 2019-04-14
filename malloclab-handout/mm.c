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
#ifdef NEXT_FIT
    "tutt07+ewilli24",
#else
    "tutt07+ewilli24",
#endif
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

/* $end mallocmacros */

/* Global variables */
static char *free_list_root_p;
static char *heap_listp;  /* pointer to first block */  
#ifdef NEXT_FIT
static char *rover;       /* next fit rover */
#endif

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
    condprintf("<MM_INIT>\n");

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

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

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
    condprintf("<MALLOC>\n");
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
	condprintf("at the end of malloc...\n");
	// printFreelist();
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {

	//TODO prints
	condprintf("at the end of malloc...\n");
	// printFreelist();
	return NULL;
    }
    place(bp, asize);
    // TODO now let's put the rover in the next spot.
    // rover = NEXT_BLKP(bp);
    //
    // TODO printing the freelist here.
    condprintf("at the end of malloc...\n");
    // printFreelist();
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    condprintf("<FREE>\n");
    // condprintf("freeing...\n");
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
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	condprintf("ERROR: mm_malloc failed in mm_realloc\n");
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
	condprintf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	condprintf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	condprintf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    // printf("extending the heapo\n");
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
    // condprintf("placing...\n");
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 

	// new part for linking the explicit free list
	// moving the links to the adjusted position of the free block
	char* adjustedBp = (char*)(bp + asize);
	SET_NEXT_FREE((char *)adjustedBp, GET_NEXT_FREE(bp));
	SET_PREV_FREE((char *)adjustedBp, GET_PREV_FREE(bp));

	size_t* bpOldNextFree;
	bpOldNextFree = (size_t*)GET_NEXT_FREE(bp);

	if(GET_PREV_FREE(bp) == 0)
	{
	    // PUT(free_list_root_p, (char *)bp + asize);
	    free_list_root_p = (char *)(bp + asize);
	}
	else
	{
	    SET_PREV_FREES_NEXT(bp, (char *)(bp + asize));
	}
	if(bpOldNextFree != 0)
	{
	    SET_NEXT_FREES_PREV(bp, (char *)(bp + asize));
	}
	// 
	// SET_PREV_FREES_NEXT(bp, (char *)bp + asize);
	// SET_NEXT_FREES_PREV(bp, (char *)bp + asize);

	// old, already existed
	// condprintf("placing case 1, with csize as %d, asize as %d\n", csize, asize);
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
	// new, link the things on the left and right.
	dissociateBlockFromList(bp);

	// old
	// condprintf("placing case 2, with csize as %d\n", csize);
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
#ifdef NEXT_FIT 
    /* next fit search */
    char *oldrover = rover;

    /* search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    return NULL;  /* no fit found */
#else 

    // EXPLICIT FREE LIST SEARCH
    
    char *bp;

    // iterate across the free  list, find a spot  that is big enough, and use this.
    // for(bp = free_list_root_p; GET_NEXT_FREE(bp) != 0; bp = GET_NEXT_FREE(bp))
    for(bp = free_list_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp))
    {
	// condprintf("spinning");
	if(asize <= GET_SIZE(HDRP(bp)))
	{
	    return bp;
	}
    }
    // needs to run one more time
//     if(asize <= GET_SIZE(HDRP(bp)))
//     {
// 	return bp;
//     }
    return NULL; // no fit found

    // UNUSED
    
    /* first fit search */
    //void *bp;

    //for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	//    return bp;
	//}
    //}
    //return NULL; /* no fit */
#endif
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */

// TODO express this explicitly in each case of coalesce, not as one function.
static void insertFreeBlockAtBeginning(void* bp) {

	// set the next of this block to the current, old, next.
	// PUT(bp, GET_NEXT_FREE(free_list_root_p));
	condprintf("\tuseful stats before: bp: %p, *bp: %x, free_list_root_p: %p, *free_list_root_p: %x\n",
		bp, *(size_t*)bp, free_list_root_p, *(size_t*)free_list_root_p);

	// only set a next if the next thing isn't the adjacent block itself
	// this is exactly the same as when the root pointer's next is nothing (there's only 1 thing).
	if(free_list_root_p != NEXT_BLKP(bp) && bp != free_list_root_p) {
	    SET_NEXT_FREE(bp, free_list_root_p);
	} else if(bp == free_list_root_p) {
	  // case 3 hits here.
	} else {
	    // don't necessarily do this becasue case 3 it needs this link still.
	    SET_NEXT_FREE(bp, 0);
	    condprintf("There's only one thing currently in free_list_root_p, no next\n");
	}


	condprintf("\tuseful stats unbefore: bp: %p, *bp: %x, free_list_root_p: %p, *free_list_root_p: %x\n",
		bp, *(size_t*)bp, free_list_root_p, *(size_t*)free_list_root_p);

	// set prev to zero.
	SET_PREV_FREE(bp, 0);

	// set the next's previous to this, if there is a next.
	if(GET_NEXT_FREE(bp) != 0) {
	    condprintf("the next frees prev being set\n");
	    SET_NEXT_FREES_PREV(bp, bp);
	    condprintf("done with that\n");
	}
	// set the root pointer 
	free_list_root_p = bp;

	condprintf("\tuseful stats doubly unbefore: bp: %p, *bp: %x, free_list_root_p: %p, *free_list_root_p: %x\n",
		bp, *(size_t*)bp, free_list_root_p, *(size_t*)free_list_root_p);
}

static void dissociateBlockFromList(void* bp) {

    // condprintf("dissociating a block...\n");

    size_t* prevThing = (size_t*)GET_PREV_FREE(bp);
    size_t* nextThing = (size_t*)GET_NEXT_FREE(bp);
    // case 1 - only right exists
    if(!prevThing && nextThing) {
	// set the next to refer to boundary, aka 0
	SET_NEXT_FREES_PREV(bp, 0);
	// update the root.
	// free_list_root_p = nextThing;
    }
    // case 2 - only left exists
    else if(prevThing && !nextThing) {
	// set the prev to refer to boundary, aka 0
	SET_PREV_FREES_NEXT(bp, 0);
	// update the root to be zero.
    }
    // case 3 - both exist
    else if(prevThing && nextThing) {
	SET_NEXT_FREES_PREV(bp, prevThing);
	SET_PREV_FREES_NEXT(bp, nextThing);
    }
    // else do nothing
}

static void *coalesce(void *bp) 
{
    // condprintf("prealesce...\n");
    // printFreelist();
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // condprintf("going in.\n");
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // condprintf("going in.\n");
    size_t size = GET_SIZE(HDRP(bp));

    // condprintf("going in.\n");

    if(!hasFinishedInit) {

	condprintf("-coalesce case 0\n");
	// set up the first free memory block with null refs to next and prev.
	// PUT(GET(free_list_root_p), 0);
	// PUT(GET(free_list_root_p + WSIZE), 0);
	// condprintf("postalesce...\n");
	printFreelist();
	return bp;
    }
    else if (prev_alloc && next_alloc) {            /* Case 1 */
	condprintf("-coalesce case 1\n");
	// new
	insertFreeBlockAtBeginning(bp);
	// old
	// condprintf("postalesce case 1...\n");
	printFreelist();
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	
	condprintf("-coalesce case 2\n");
	// if free_list_root_p is same thing as the next block pointer
	// same thing as: if there's only one item in the list

	// new, for the right block pointer, link its prev and next 
	// in order to dissociate it.
	dissociateBlockFromList(NEXT_BLKP(bp));

	// everything after the dissociation above is exactly the same as case one.
	insertFreeBlockAtBeginning(bp);

	// old
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));


	// condprintf("postalesce case 2...\n");
	printFreelist();
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	condprintf("-coalesce case 3\n");
	// new, for the right block pointer, link its prev and next 
	// in order to dissociate it.
	dissociateBlockFromList(PREV_BLKP(bp));

	// old
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

	bp = PREV_BLKP(bp);

	// NOTE: this comes after because it needs to operate on the prev location.
	// everything after the dissociation above is exactly the same as case one.
	insertFreeBlockAtBeginning(bp);

	// condprintf("postalesce case 3...\n");
	printFreelist();
    }

    else {                                     /* Case 4 */
	condprintf("-coalesce case 4\n");
	// new, for the right block pointer, link its prev and next 
	// in order to dissociate it.
	dissociateBlockFromList(PREV_BLKP(bp));
	dissociateBlockFromList(NEXT_BLKP(bp));

	// old
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

	// NOTE: this comes after because it needs to operate on the prev location.
	// everything after the dissociation above is exactly the same as case one.
	insertFreeBlockAtBeginning(bp);

	// condprintf("postalesce case 4...\n");
	printFreelist();
    }

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
	rover = bp;
#endif

    return bp;
}



static void printFreelist(void) {
    condprintf("\tthe current list:\n");

    condprintf("\tfree_list_root_p: %p, *free_list_root_p: %x\n", free_list_root_p, *(size_t*)free_list_root_p);
    // iterate across the free list and print the blocks.
    char *bp;

    // iterate across the free  list, find a spot  that is big enough, and use this.
    // for(bp = free_list_root_p; GET_NEXT_FREE(bp) != 0; bp = GET_NEXT_FREE(bp))
    for(bp = free_list_root_p; bp != 0; bp = (char*)GET_NEXT_FREE(bp))
    {
	// condprintf("(next bp is %p)\n", bp);
	printblockExtra(bp);
    }
    // condprintf("(end of list)\n");
}

static void printblockExtra(void *bp) 
{
    size_t hsize, halloc, fsize, falloc, next, prev;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
	
    // condprintf("getting the footer\n");
    fsize = GET_SIZE(FTRP(bp));
    // condprintf("got the footer\n");
    falloc = GET_ALLOC(FTRP(bp));  
    next = GET_NEXT_FREE(bp);
    prev = GET_PREV_FREE(bp);  
    
    if (hsize == 0) {
	condprintf("%p: EOL\n", bp);
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

