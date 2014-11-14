/*
 * mm.c
 * Name: Meiheng Lu
 * ID: meihengl
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 * 
 * I use segregated lists with LIFO policy to save free blocks, simple second
 * fit policy to find the fitable free block through comparing the first two
 * fitable free blocks, and choose the one with less left size. For segregated 
 * list, I have total nine lists, which increases by multiple 2. The least free
 * block has 16 byte, 4 for header, 4 for next free block address (last 32 bit), 
 * 4 for previous free block address (last 32 bit), and 4 for footer. If the 
 * free block is the first element in the list, then its previous block address
 * will be 0, and if it is the last one, then its next block is NULL. Besids, I 
 * remove the footer of allocated blocks to get better space utilization, 
 * the status of previous block can be saved in next block last second bit, 
 * we also need to store the last block status in the epilogue, which may be 
 * useful in coalescing extend heap, since the header position of epilogue 
 * will become the header of new extend block. I use the last three free
 * bits of the header as the cycle bit, prev_alloc bit and alloc bit 
 * respectively. For alloc bit, it saves the status of the current block.
 * For prev_alloc bit, it saves the status of physical previous block.
 * For cycle bit, it is used in check_list to check whether all free blocks
 * are in the segregated lists.  
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_PTR(P) ((size_t*)(((char*)(p)) - SIZE_T_SIZE))
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// macros for list
#define WSIZE 4 
#define DSIZE 8
#define CHUNKSIZE 160 
#define MAX(x, y) ((x) > (y)? (x) : (y))
/* the starting adress of the heap */
#define PINIT (char *)0x800000000
/* define segregated list ptr, size class pointer */
static char *heap_listp = NULL;
static char *sc16p = NULL; 
static char *sc32p = NULL; 
static char *sc64p = NULL; 
static char *sc128p = NULL; 
static char *sc256p = NULL; 
static char *sc512p = NULL; 
static char *sc1024p = NULL; 
static char *sc2048p = NULL; 
static char *sc2049p = NULL; 
/* the upper size of the segregated list */
#define SIZE0 0
#define SIZE16 16
#define SIZE32 32
#define SIZE64 64
#define SIZE128 128
#define SIZE256 256
#define SIZE512 512
#define SIZE1024 1024
#define SIZE2048 2048
#define SIZEMAX  0xffffffffffffffff

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}


// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Read a word at address p
static inline unsigned int GET(char *p){
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    return (*(unsigned int *)(p));
}

// Write a word at address p
static inline void PUT(char *p, unsigned int val){
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    (*(unsigned int *)(p)) = val;
    return;
}

// Return the size of the given block in multiples of the word size
static inline unsigned int GET_SIZE(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    return (GET(p) & ~0x7);
}

// Return 1 if the block is allocated, 0 otherwise
static inline unsigned int GET_ALLOC(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    return (GET(p) & 0x1);
}

// Return 1 if the physical previous block is allocated, 0 otherwise
static inline unsigned int GET_PREV_ALLOC(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    return (GET(p) & 0x2);
}

// Write 1 if the block is allocated, 0 otherwise
static inline void PUT_PREV_ALLOC(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    (*(unsigned int *)(p)) = ((*(unsigned int *)(p)) | 0x2);
    return;
}

// Clear the prev alloc info
static inline void CLEAR_PREV_ALLOC(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    *(unsigned int *)(p) = (*(unsigned int *)(p) & ~0x2);
    return;
}

// Combine the size and alloc
static inline int PACK(unsigned int size, unsigned int alloc) {
    REQUIRES((alloc == 0) || (alloc == 1));
    return (size | alloc);
}

// Given a block bp, get its header address
// In checklist, the header address may over mem_heap_hi()
// hence, cannot REQUIRES(in_heap(bp))
static inline char *HDRP(char *bp) {
    REQUIRES(bp != NULL);
    return (bp - WSIZE);
}

// Given a block bp, get its footer address
static inline char *FTRP(char *bp) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    return (bp + GET_SIZE(HDRP(bp)) - DSIZE);
}

// Given bp, get its next physical block address
static inline char *NEXT_PHYP(char *bp) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    return (bp + GET_SIZE(HDRP(bp)));
}

// Given bp, get its previous physical block address
static inline char *PREV_PHYP(char *bp) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    REQUIRES(in_heap(bp - DSIZE));
    return (bp - GET_SIZE(bp - DSIZE));
}

// Given bp, get its next free block address in list,
// we only save the last 32 bit of the address, so when
// retrive we need to revert it, which may result in getting 
// PINIT when previous storing NULL
static inline char *NEXT_BLKP(char *bp) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    return ((char *)((unsigned long)GET(bp) | 0x800000000));
}

// Given bp, get its previous free block address in list,
// the same problem with NEXT_BLKP above
static inline char *PREV_BLKP(char *bp) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    REQUIRES(in_heap(bp + WSIZE));
    return ((char *)((unsigned long)GET(bp + WSIZE) | 0x800000000));
}

// Read the cycle info at address p
static inline unsigned int GET_CYCLE(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    return (GET(p) & 0x4);
}

// Put the cycle info at address p
static inline void PUT_CYCLE(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    *(unsigned int *)(p) = (*(unsigned int *)(p) | 0x4); 
    return;
}

// Clear the cycle info at address p
static inline void CLEAR_CYCLE(char *p) {
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    *(unsigned int *)(p) = (*(unsigned int *)(p) & ~0x4); 
    return;
}

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

static void *extend_heap(size_t words);
static void *coalesce(char *bp);
static void place(char *bp, size_t asize);
static char *find_fit(size_t asize);
static void delete(char *bp, size_t size);
static void insert(char *bp, size_t size);
static void checkblock(void *bp);
static void printblock(void *bp);
static void checklist(void);
static void check_list(char *scp, size_t lowsize, size_t upsize);
static char *findfit(char *bp,char *sizep,size_t *sp,size_t los,size_t ups);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {

    /* reset the segregated list root ptr */ 
    heap_listp = NULL;
    sc16p = NULL; 
    sc32p = NULL; 
    sc64p = NULL; 
    sc128p = NULL; 
    sc256p = NULL; 
    sc512p = NULL; 
    sc1024p = NULL; 
    sc2048p = NULL; 
    sc2049p = NULL; 

    char *bp;
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)(-1))
        return -1;
    PUT(heap_listp, 0);                         /* alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));/* prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));/* prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));    /* epilogue header */
    /* set epilogue header as prev_alloc */
    PUT_PREV_ALLOC(heap_listp + 3*WSIZE); 
    heap_listp += (2*WSIZE);

    /* extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    /* initialize the segregated list, previous is root, set it as 0 */
    bp = heap_listp + DSIZE;
    PUT(bp, (unsigned long)NULL);
    PUT((bp + WSIZE), 0);
    /* allocate bp to coresponding list according to size */
    sc256p = bp;    
    return 0;
}

/*
 * extend heap with CHUNKSIZE
 */

static void *extend_heap(size_t words){
    REQUIRES(words != 0);
    words = words;
    char *bp;
    size_t size;

    /* allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (((long)(bp = mem_sbrk(size)) == -1))
        return NULL;

    /* initialize free block header/footer and epilogue header */
    if (GET_PREV_ALLOC(HDRP(bp))){
        PUT(HDRP(bp), PACK(size, 0));        // free block header 
        PUT(FTRP(bp), PACK(size, 0));        // free block footer 
        PUT_PREV_ALLOC(HDRP(bp));            // prev alloc situation 
    }
    else{
        PUT(HDRP(bp), PACK(size, 0));        
        PUT(FTRP(bp), PACK(size, 0));       
    }
    /* new epilogue header, prev block is free */
    PUT((bp + size - WSIZE), PACK(0, 1));  
    return coalesce(bp);    
}

/*
 * sub_function of find_fit, find a free block in a certain free list
 * sizep is the size class ptr, sp is the given size ptr, los is lowsize
 * ups is upsize, if find fitable free block ptr, return it, oterwise, 
 * return bp = NULL, and update size to let it go into next size class
 */
static char *findfit(char *bp,char *sizep,size_t *sp,size_t los,size_t ups){

    REQUIRES(sp != NULL);

    bp = bp;
    sizep = sizep;
    sp = sp;
    los = los;
    ups = ups;

    char *ptr, *bp1 = NULL, *bp2 = NULL;
    size_t  leftsize1 = SIZEMAX, leftsize2 = SIZEMAX;

    if ((*sp <= los) || (*sp > ups))
        return bp;
    else{
        /* fisrt find fit */
        for (ptr = sizep; (ptr!=PINIT)&&(ptr!=NULL); ptr = NEXT_BLKP(ptr)){
            if (GET_SIZE(HDRP(ptr)) >= *sp){
                leftsize1 = GET_SIZE(HDRP(ptr)) - *sp;
                bp1 = ptr;
                break;
            }
        }
    }
    /* if ptr = NULL, no fit has been found */
    if ((ptr == NULL) || (ptr == PINIT)){         
        *sp = ups + 1;
        return bp;
    }
   
    /* second find fit */
    for (ptr=NEXT_BLKP(bp1);(ptr!=PINIT)&&(ptr!=NULL);ptr=NEXT_BLKP(ptr)){
        if (GET_SIZE(HDRP(ptr)) >= *sp){
            leftsize2 = GET_SIZE(HDRP(ptr)) - *sp;
            bp2 = ptr;
            break;     
        }
    }
    /* choose one with leftsize */
    bp = (leftsize1 > leftsize2)? bp2: bp1;
    
    return bp;
}

/* 
 * find the fit size class and return fitable free block ptr
 */
static char *find_fit(size_t asize){

    REQUIRES(asize != 0);
    asize = asize;
    size_t size = asize;
    char *bp = NULL;
    bp = findfit(bp, sc16p, &size, SIZE0, SIZE16); 
    bp = findfit(bp, sc32p, &size, SIZE16, SIZE32); 
    bp = findfit(bp, sc64p, &size, SIZE32, SIZE64); 
    bp = findfit(bp, sc128p, &size, SIZE64, SIZE128); 
    bp = findfit(bp, sc256p, &size, SIZE128, SIZE256); 
    bp = findfit(bp, sc512p, &size, SIZE256, SIZE512); 
    bp = findfit(bp, sc1024p, &size, SIZE512, SIZE1024); 
    bp = findfit(bp, sc2048p, &size, SIZE1024, SIZE2048);
    bp = findfit(bp, sc2049p, &size, SIZE2048, SIZEMAX);

    return bp;
}

/*
 * set the free block as allocated, if the leftsize is large enough to
 * be a new free block, then cut it as a new free block
 */ 
static void place(char *bp, size_t asize){

    REQUIRES(bp != NULL);
    REQUIRES(asize != 0);

    bp = bp;
    asize = asize;
    size_t freeblksize = GET_SIZE(HDRP(bp));
    size_t leftsize = freeblksize - asize;

    /* leftsize less than 16 byte, cannot cut it */
    if (leftsize < 2*DSIZE){
        /* check for the prev_alloc */
        if (GET_PREV_ALLOC(HDRP(bp))){
            PUT(HDRP(bp), PACK(freeblksize, 1));
            PUT_PREV_ALLOC(HDRP(bp));
        }
        else
            PUT(HDRP(bp), PACK(freeblksize, 1));

        PUT_PREV_ALLOC(HDRP(NEXT_PHYP(bp)));
        delete(bp, freeblksize);
    }   

    /* cut the left free block as a new free block */
    else{
        if (GET_PREV_ALLOC(HDRP(bp))){
            PUT(HDRP(bp), PACK(asize, 1));
            PUT_PREV_ALLOC(HDRP(bp));
        }
        else
            PUT(HDRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_PHYP(bp)), PACK(leftsize, 0));
        PUT(FTRP(NEXT_PHYP(bp)), PACK(leftsize, 0));
        PUT_PREV_ALLOC(HDRP(NEXT_PHYP(bp)));
        /* delete the original free block from its size class list
         * add the new free block to its size class list */
        delete(bp, freeblksize);
        insert(NEXT_PHYP(bp), leftsize);
    }
    return; 
}

/*
 * delete the free block from its size class segregated list
 */
static void delete(char *bp, size_t size){

    REQUIRES(bp != NULL);
    REQUIRES(size != 0);
    bp = bp;
    size = size;
    char **scp;
    /* choose the rigjt size class ptr */
    if (size <= 16)
        scp = &sc16p;
    else if (size <= 32)
        scp = &sc32p;
    else if (size <= 64)
        scp = &sc64p;
    else if (size <= 128)
        scp = &sc128p;
    else if (size <= 256)
        scp = &sc256p;
    else if (size <= 512)
        scp = &sc512p;
    else if (size <= 1024)
        scp = &sc1024p;
    else if (size <= 2048)
        scp = &sc2048p;
    else
        scp = &sc2049p;

    /* update the list */
    /* the first element in segregated list */
    if (GET(bp + WSIZE) == 0){
        if (NEXT_BLKP(bp) == PINIT) 
        /* next block ptr = NULL */
            *scp = NULL;
        else{
        /* set the next block connects to the root */
            *scp = NEXT_BLKP(bp);
            PUT((NEXT_BLKP(bp) + WSIZE), 0); 
        }  
    }
    /* an element in the middle of the list */
    else{
        if (NEXT_BLKP(bp) == PINIT)
        /* next block ptr = NULL */
            PUT(PREV_BLKP(bp), (unsigned long) NULL);
        else{
        /* connecy prev and next blocks */
            PUT((NEXT_BLKP(bp) + WSIZE), GET(bp + WSIZE));
            PUT((PREV_BLKP(bp)), (GET(bp)));
        }
   }
    return;
}

/*
 * insert the free block to corresponding list 
 */
static void insert(char *bp, size_t size){

    REQUIRES(bp != NULL);
    REQUIRES(size != 0);
    bp = bp;
    size = size;
    char **scp;
    if (size <= 16)
        scp = &sc16p;
    else if (size <= 32)
        scp = &sc32p;
    else if (size <= 64)
        scp = &sc64p;
    else if (size <= 128)
        scp = &sc128p;
    else if (size <= 256)
        scp = &sc256p;
    else if (size <= 512)
        scp = &sc512p;
    else if (size <= 1024)
        scp = &sc1024p;
    else if (size <= 2048)
        scp = &sc2048p;
    else
        scp = &sc2049p;


    if (*scp == NULL){
       PUT((bp + WSIZE), 0);
       PUT(bp, (unsigned long)NULL);
       *scp = bp;
    }
    else{
        PUT((bp + WSIZE), 0);
        PUT(bp, (unsigned long)(*scp));
        PUT((NEXT_BLKP(bp) + WSIZE), (unsigned long)(bp));
        *scp = bp;
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {

    checkheap(1);  // Let's make sure the heap is ok!
    size = size;
    size_t asize;      /* adjust size */
    size_t extendsize; /* require to expend heap */
    char *bp;
    
    /* initialize the heap */
    if (heap_listp == NULL)
        mm_init();
    /* ignore sperious requests */
    if (size == 0)
        return NULL;
    /* adjust block size to satisfy alignment */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    /* search the freelist to allocate */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* no fit found, require to extend_heap */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {

    if (ptr == NULL) {
        return;
    }

    checkheap(1);  // Let's make sure the heap is ok!
    ptr = ptr;
    char *bp;
    size_t size = GET_SIZE(HDRP(ptr));

    /* keep the prev_alloc same */
    if (GET_PREV_ALLOC(HDRP(ptr))){
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT_PREV_ALLOC(HDRP(ptr));
    }
    else{
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    /* cleat the prev_alloc of next physical blk */
    CLEAR_PREV_ALLOC(HDRP(NEXT_PHYP(ptr)));

    bp = coalesce(ptr);
    return;
}

/*
 * coalesce - four cases needed to be consider
 */
static void *coalesce(char *bp){

    REQUIRES(bp != NULL);
    bp = bp;
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_PHYP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1: no free block, just insert it */
    if (prev_alloc && next_alloc)
        insert(bp, size);
    /* case 2: previous free block, delete old and insert new */
    if ((!prev_alloc) && next_alloc){
        delete(PREV_PHYP(bp), GET_SIZE(HDRP(PREV_PHYP(bp))));
        size += GET_SIZE(HDRP(PREV_PHYP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_PHYP(bp);
        /* update header, keep prev_alloc same */
        if (GET_PREV_ALLOC(HDRP(bp))){
            PUT(HDRP(bp), PACK(size, 0));
            PUT_PREV_ALLOC(HDRP(bp));
        }
        else
            PUT(HDRP(bp), PACK(size, 0));
        insert(bp, size);
    }
    /* case 3: next free block */
    if (prev_alloc && (!next_alloc)){
        delete(NEXT_PHYP(bp), GET_SIZE(HDRP(NEXT_PHYP(bp))));
        size += GET_SIZE(HDRP(NEXT_PHYP(bp)));
        PUT(FTRP(NEXT_PHYP(bp)), PACK(size, 0));
        /* update header, keep prev_alloc same */
        if (GET_PREV_ALLOC(HDRP(bp))){
            PUT(HDRP(bp), PACK(size, 0));
            PUT_PREV_ALLOC(HDRP(bp));
        }
        else
            PUT(HDRP(bp), PACK(size, 0));
        insert(bp, size);
    }
    /* case 4: both free block */
    if ((!prev_alloc) && (!next_alloc)){
        delete(PREV_PHYP(bp), GET_SIZE(HDRP(PREV_PHYP(bp))));
        delete(NEXT_PHYP(bp), GET_SIZE(HDRP(NEXT_PHYP(bp))));
        size += GET_SIZE(HDRP(PREV_PHYP(bp)));
        size += GET_SIZE(HDRP(NEXT_PHYP(bp)));
        PUT(FTRP(NEXT_PHYP(bp)), PACK(size, 0));
        bp = PREV_PHYP(bp);
        /* update header, keep prev_alloc same */
        if (GET_PREV_ALLOC(HDRP(bp))){
            PUT(HDRP(bp), PACK(size, 0));
            PUT_PREV_ALLOC(HDRP(bp));
        }
        else
            PUT(HDRP(bp), PACK(size, 0));
        insert(bp, size);
    }
    return bp;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    
    checkheap(1);  // Let's make sure the heap is ok!
    oldptr = oldptr;
    size = size;
    size_t oldsize;
    char *newptr;

    if (size == 0){
        free(oldptr);
        return 0;
    }

    if (oldptr == NULL){
        return malloc(size);
    }

    newptr = malloc(size);
    if (!newptr)
        return 0;
    
    oldsize = GET_SIZE(HDRP(oldptr));
    if (size < oldsize)
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    nmemb = nmemb;
    size = size;

    checkheap(1);  // Let's make sure the heap is ok!
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * Returns 0 if no errors were found, otherwise returns the error
 */
int mm_checkheap(int verbose) {

    verbose = verbose;
    char *bp;
    if (verbose)
        printf("Heap (%p:)\n", heap_listp);
    
    /* check prologue */
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
        checkblock(heap_listp);
    /* check block */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_PHYP(bp)){
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }
    /* check epilogue */
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    /* check segregated list */
    if (verbose)
        checklist();
    return 0;
}
   
/*
 * sub_functionof checklist,check single list
 */ 
static void check_list(char *scp, size_t lowsize, size_t upsize){
   
    scp = scp;
    lowsize = lowsize;
    upsize = upsize;
    char *p;
    for (p = scp; (p != NULL) && (p != PINIT); p = NEXT_BLKP(p)){

        REQUIRES(in_heap(p));
        if ((NEXT_BLKP(p) != PINIT) && (p != (PREV_BLKP(NEXT_BLKP(p)))))
            printf("prev/next pointers are not consistent\n");
        if (GET_ALLOC(HDRP(p)) != 0)
            printf("free list contains allocated block\n");
        if (!GET_ALLOC(HDRP(NEXT_PHYP(p))) || !GET_PREV_ALLOC(HDRP(p)))
            printf("contiguous free blocks\n");
        if (GET_SIZE(HDRP(p)) <= lowsize)
            printf("free block containing in wrong list\n");
        if (GET_SIZE(HDRP(p)) > upsize)
            printf("free block containing in wrong list\n");
        if (GET_CYCLE(HDRP(p)) == 1)
            printf("with cycle in the list\n");

        /* set the last third bit as 1, which means the free block 
         * has been checked in the list before */
        PUT_CYCLE(HDRP(p));
    }
        return;
}

/*
 * checklist
 */
static void checklist(void){

    /* check each list */
    check_list(sc16p, SIZE0, SIZE16);
    check_list(sc32p, SIZE16, SIZE32);
    check_list(sc64p, SIZE32, SIZE64);
    check_list(sc128p, SIZE64, SIZE128);
    check_list(sc256p, SIZE128, SIZE256);
    check_list(sc512p, SIZE256, SIZE512);
    check_list(sc1024p, SIZE512, SIZE1024);
    check_list(sc2048p, SIZE1024, SIZE2048);
    check_list(sc2049p, SIZE2048, SIZEMAX);

    /* check whether all free blocks are all in the lists 
     * according to the cycle bit */
    char *p;
    for (p = heap_listp + DSIZE; GET_SIZE(HDRP(p)) != 0; p = NEXT_PHYP(p)){
        if (!GET_ALLOC(HDRP(p))){
            if (!GET_CYCLE(HDRP(p)))
                printf("free block not in the list\n");
            CLEAR_CYCLE(HDRP(p));
        }
    }
    return;
}

static void printblock(void *bp){
    
    REQUIRES(bp != NULL);
    bp = bp;
    size_t hsize, halloc;
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));

    if (hsize == 0){
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%lu:%c]\n", bp, hsize, (halloc? 'a':'f'));
    return;
}

/* 
 * since the footer has been removed, there's no need to check 
 * the matching of footer and header
 */
static void checkblock(void *bp){

    REQUIRES(bp != NULL);
    bp = bp;
    if ((size_t)bp % 8)
        printf("Error: %p is not double word aligned\n", bp);
}
