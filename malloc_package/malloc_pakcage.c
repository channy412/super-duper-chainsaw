/*
 * malloc_package.c - Explicit free list using LIFO, first fit malloc package.
 *
 * In this approach, each block has word size footer and header.
 * To use explicit free list, every free block has word size next, prev.
 * Blocks are immediately coalesced when freed. 
 * Freed block is inserted at the head of the list(LIFO).
 * Linked list used here is a circular doubly linked list. 
 * First fit policy is used when searching. Realloc isn't implemented.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "memlib.h"


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Predefined numbers */
#define WSIZE 4              /* Word and header/footer size */
#define DSIZE 8              /* Double word size */
#define CHUNKSIZE (1<<14)    /* Extend heap by this amount = 16KB = 4 * page size */

#define Max(x,y)  ( (x) > (y) ? (x) : (y) )


/* Pack a size and allocated biy into a word */
#define PACK(size,alloc)   ( (size) | (alloc) )

/* Read and write a word at address p */
#define GET(p)          ( *(unsigned int *)(p) )
#define PUT(p, val)     ( *(unsigned int *)(p)  = (unsigned int)(val) )


/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)


/* Given block ptr bp(block pointer), compute address of its header, footer, next, prev */
#define HDRP(bp)    ((char *)(bp) - WSIZE )
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT(bp)    (bp)
#define PREV(bp)    ((char *)(bp) + WSIZE)


/* Given block ptr bp, compute address of adjacent next and previous blocks */
#define NEXT_BLKP(bp)   ( (char *)(bp)   +  GET_SIZE(HDRP(bp))     )
#define PREV_BLKP(bp)   ( (char *)(bp)   -  GET_SIZE( (char *)(bp) - DSIZE ) )


/* Given block ptr bp, compute size of adjacent next and previous blocks */
#define GET_PREV_SIZE(bp)    (GET_SIZE( (char *)(bp) - DSIZE ))
#define GET_NEXT_SIZE(bp)    (GET_SIZE(HDRP(NEXT_BLKP(bp))))


/* Given FREE block ptr bp, compute address of FREE LIST's next and previous blocks */
#define NEXT_NODE(bp)   (void*)(*(unsigned int*)bp)
#define PREV_NODE(bp)   (void*)(*((unsigned int*)bp + 0x1 ))


/* Given prev, next, set next node, set prev node of free list */
#define SET_NEXT(prev,next)  (PUT(NEXT(prev), next))
#define SET_PREV(prev,next)  (PUT(PREV(next), prev))


static void *heap_listp;             /*  start address - points to the footer of prologue */
static void *list_head = NULL;       /* head node of free list */
static void *extend_heap(size_t words);





/*
 *  my_init - initialize the malloc package.
 *  return value : 0 on success, -1 on error.
 *  prologue and epilog is used and it is useful when coalescing.
 */
int my_init()
{
    list_head = NULL;
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)(- 1)) return -1;

    /* chekc double word alignment */
    if( heap_listp != (void*) (ALIGN( (unsigned long) heap_listp)) ) {
     heap_listp = (void*) (ALIGN( (unsigned long) heap_listp));
    }

    /* Set prologue and epilogue*/
    PUT(heap_listp, 0);                             /* padding for 8 byte alingment */ 
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1) );    /*      prologue header         */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1) );    /*      prologue footer         */ 
    PUT(heap_listp + (3*WSIZE), PACK(0,1) );        /*      epilogue header         */
    heap_listp += (2*WSIZE);

    /* Expand the empty heap with a free block of CHUNKSIZE bytes */
    if ( extend_heap(CHUNKSIZE/WSIZE) == NULL ) return -1;

    return 0;
}



/* 
* add_list - add a free block to the free list 
* Insert ptr block to the head of the list 
*/
static void add_list(void *ptr) {
    if(list_head == NULL) { /* if the list is empty */
        list_head = ptr;
        PUT(NEXT(ptr), ptr);
        PUT(PREV(ptr), ptr);
    } else {
    SET_PREV(PREV_NODE(list_head),ptr);
    SET_NEXT(PREV_NODE(list_head),ptr);
    SET_NEXT(ptr,list_head);
    SET_PREV(ptr,list_head);
    list_head = ptr;
    }
}



/*
* remove_from_list - remove ptr block from the free list 
* If the size of list was 1, make the list NULL
*/
static void remove_from_list(void *ptr) {
    /* if ptr is the only element */
    if( ptr == NEXT_NODE(ptr) ) {
        if( ptr != list_head) printf("error in remove from list\n");
        list_head = NULL;
        return;
    }

    /* else */
    if ( ptr == list_head) {
        list_head = NEXT_NODE(ptr);
    }

    void *prev_node = PREV_NODE(ptr);
    void *next_node = NEXT_NODE(ptr);
    SET_PREV(prev_node, next_node);
    SET_NEXT(prev_node, next_node);
}




/* 
* entend_heap - expand heap with the amount of words size 
* add this new chunk to the free list
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain 8 byte alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if( (long)(bp = mem_sbrk(size)) == -1  ) return NULL;


    /* Initialize free block header/footer and the epilogue header */
    PUT( HDRP(bp), PACK(size, 0)  );            /* previous epilogue block to new block's header */
    PUT( FTRP(bp), PACK(size, 0)  );
    PUT( HDRP(NEXT_BLKP(bp)), PACK(0, 1)  );

    add_list(bp);
    return bp;
}





/* 
* find_fit - find a free block with (size >= asize)
* first fit policy is used here
*/
static void* find_fit(size_t asize) {
    void * bp;

    if(list_head == NULL) return NULL;
    
    /* first fit */
    if( !GET_ALLOC(HDRP(list_head)) && ( asize <= GET_SIZE(HDRP(list_head))) ) {
        return list_head;
    }       
    for( bp = NEXT_NODE(list_head) ; bp != list_head ; bp = NEXT_NODE(bp) ) {
        if( !GET_ALLOC(HDRP(bp)) && ( asize <= GET_SIZE(HDRP(bp))) ) {
            return bp;
        }
    }

    /* No fit */
    return NULL;  
}




/*
* place - place block of size asize at bp. 
* Split block if ((remaining size) >= 8 words)
* Use lateral part of splited block to remain free list untouched
*/
static void* place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    /* Split this block */
    if( (csize - asize) >= 4*DSIZE ) {
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));  
        return bp;
    }

    /* Use the whole block */
    else {
        remove_from_list(bp);
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
        return bp;
    }

}



/*
 *  my_malloc - Allocate a block by searching the free list.
 *  Find the block with first fit.
 *  If no block found, allocate heap more.
 *  Always allocate a block whose size is a multiple of the alignment.
 */
void *my_malloc(size_t size)
{
    size_t asize;        /* adjusted size */
    size_t extendsize;   /* Amount to extend heap if no fit */
    char * bp;

    /* Ignore spurious requests */
    if( size == 0) return NULL;


    /* Minimum block size = 4* word   since 2 word for header and footer, double word alignment */
    if ( size <= DSIZE) asize = 2 * DSIZE;
    else asize = ALIGN(size) + DSIZE;   /*  Additional DSIZE for header and footer */


    /* Search the free list for a fit */
    if ( (bp = find_fit(asize)) != NULL)  {
        bp = place(bp, asize);
        return bp;
    }


    /* No fit found, Get more memory and place the block */
    extendsize = Max(asize, CHUNKSIZE);
    if( (bp = extend_heap(extendsize/WSIZE)) == NULL ) 
        return NULL;

    bp = place(bp,asize);
    return bp;
}






/*
 *  my_free - Frees a block.
 *  Coalesce if there exists adjacent free block(Immediate Coalscing).
 *  Add this new free block the the head of the free list(LIFO).
 */
void my_free(void *ptr)
{
    void * ptr_save = ptr;
    size_t size = GET_SIZE(HDRP(ptr));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));


    /* Ignore invalid free request*/
    if( !GET_ALLOC(HDRP(ptr))) 
        return;
    

    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size, 0));


    /* case 1 */
    if( prev_alloc && next_alloc) {
        /* now deal with free list */
        add_list(ptr);
    }

    /* case 2 */
    else if( prev_alloc && !next_alloc) {
        void *next_ptr = NEXT_BLKP(ptr);

        /* Coalecse */
        size += GET_NEXT_SIZE(ptr);
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));

        /* now deal with free list */
        remove_from_list(next_ptr);
        add_list(ptr);
    }

    /* case 3 */
    else if( !prev_alloc && next_alloc) {
        /* Coalecse */
        size += GET_PREV_SIZE(ptr);
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size,0));
        ptr = PREV_BLKP(ptr);

        /* now deal with free list */
        remove_from_list(ptr);
        add_list(ptr);
    }

    /* case 4 */
    else {
        void *next_ptr = NEXT_BLKP(ptr);

        /* Coalecse */
        size += GET_PREV_SIZE(ptr) + GET_NEXT_SIZE(ptr);
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);

        /* now deal with free list */
        remove_from_list(next_ptr);
        remove_from_list(ptr);
        add_list(ptr);
    }


    ptr = ptr_save;
}




/*
 *  my_exit - finalize the malloc package.
 *  free all the unfreed blocks
 */
void my_exit(void)
{
    void * bp = heap_listp;

    /* traverse the entire heap and free all unfreed block */
    for( bp = NEXT_BLKP(heap_listp) ; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp) ) {
        if( GET_ALLOC(HDRP(bp)) )  {
            my_free(bp);
        }
    }
}
