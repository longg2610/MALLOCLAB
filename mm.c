/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Long Pham",
    /* First member's full name */
    "Long Pham",
    /* First member's email address */
    "pham_l3@denison.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 /*double word is 16 bytes is 64-bit systems*/

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) /*one word size - 8 bytes*/

#define SET 1
#define RESET 0
#define ALLOCATED 1
#define FREE 0
#define MINBLOCKSIZE (SIZE_T_SIZE + SIZE_T_SIZE)

size_t heap_size = mem_heapsize - SIZE_T_SIZE - SIZE_T_SIZE; /*heap_size without prologue & epilogue*/

size_t* free_list_h;

/*helper functions*/
size_t blockSize(size_t* word){return (*word) & (~0x7);}
size_t allocStatus(size_t* word){return (*word) & (0x1);}
void setBlockSize(size_t* word, size_t size)
{
    *word = size;
    *(word + blockSize(word) / SIZE_T_SIZE - 1) = size;
}

void setAllocStatus(size_t* word, int alloc_status)
{
    if (alloc_status == ALLOCATED)
    {
        *word |= ALLOCATED;
        *(word + blockSize(word) / SIZE_T_SIZE - 1) |= ALLOCATED;
    }
        
    else
    {
        *word &= ~ALLOCATED;
        *(word + blockSize(word) / SIZE_T_SIZE - 1) &= ~ALLOCATED;
    } 
}
size_t* nextBlock(size_t *word){return word + blockSize(word) / SIZE_T_SIZE;}
size_t* prevBlock(size_t* word){return word - blockSize(word - 1) / SIZE_T_SIZE;}
int atEpilogue(size_t* ptr){return (allocStatus(ptr) == ALLOCATED) && (blockSize(ptr) == 0);}
void changeHead(size_t* head, size_t size, int alloc_op)
{
    *head = size;
    if (alloc_op == ALLOCATED)
        *head |= 0x1;
    else if (alloc_op == FREE)
        *head &= ~0x1;
}
void copyHeadToFoot(size_t* header){*(header + blockSize(header) / SIZE_T_SIZE - 1) = *header;}


/*key functions' signatures*/
void* coalesce(size_t* to_free);
void split(size_t total, size_t taken, size_t* taken_blk);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();    
    mem_sbrk(SIZE_T_SIZE);
    
    *((size_t*) mem_heap_lo()) = 0x1;

    size_t* heap_end = (size_t *)mem_heap_hi();
    heap_end = (char *)(heap_end) + 1; /*mem_heap_hi is one byte behind, increase so that mem_heap_lo + 1 == mem_heap_hi*/
    *heap_end &= 0x0; /*clear all bits*/
    *heap_end |= 0x1; /*and set allocated with size 0 to mark end of heap*/


    /*currently two blocks with 0x1 (allocated with size = 0)*/
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if(size == 0) return NULL;
    size_t *ptr = (size_t *)mem_heap_lo();
    ptr += 1;                                              /*first word unused*/
    int newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE); /*header and footer, two extra words*/
    /*policy: first-fit*/

    while (!(atEpilogue(ptr) == 1) &&                                   /*boundary check*/
           (allocStatus(ptr) == ALLOCATED ||                           /*while not yet found a free block*/
            blockSize(ptr) < newsize))                                 /*or block does not fit*/
    {
        ptr = nextBlock(ptr); /* get to next block*/
        
    }

    if (atEpilogue(ptr) == 1)           /*end of heap, request more VM*/
    {
        void *p = mem_sbrk(newsize); 
        if (p == (void *)-1)
            return NULL;
        else
        {
            size_t *new_mem = (size_t *)p;
            setBlockSize(new_mem, newsize);
            setAllocStatus(new_mem, FREE);      /*new mem free, coalesce*/
        
            /*new epilogue*/
            *(new_mem + blockSize(new_mem) / SIZE_T_SIZE) &= 0x0;
            *(new_mem + blockSize(new_mem) / SIZE_T_SIZE) |= ALLOCATED;

            size_t* new_mem_coalesced = (size_t*) (coalesce(new_mem));
            split(blockSize(new_mem_coalesced), newsize, new_mem_coalesced);
            setAllocStatus(new_mem_coalesced, ALLOCATED);
            
            return (void *)((char *)(new_mem_coalesced) + SIZE_T_SIZE); /*return start of payload*/
        }
    }

    /*found a free large enough block*/
    else if (allocStatus(ptr) == FREE && blockSize(ptr) >= newsize) 
    {
        /*do not change size here*/
        split(blockSize(ptr), newsize, ptr);
        setAllocStatus(ptr, ALLOCATED);

        return (void *)((size_t *)ptr + 1); /*return start of payload*/
    }
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t *to_free = (char *)(ptr - SIZE_T_SIZE);
    coalesce(to_free);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    if (size == 0)
    {
        mm_free(ptr);
        return (void *)NULL;
    }

    size_t newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE);
    size_t* p = (size_t *)((char *)(ptr) - SIZE_T_SIZE);
    if (blockSize(p) < newsize)
    {
        /*if next free block (if any) enough to hold size - curr_size bytes -> realloc in place*/
        if (allocStatus(nextBlock(p)) == FREE && blockSize(p) + blockSize(nextBlock(p)) >= newsize)
        {
            size_t merged_block_size = blockSize(p) + blockSize(nextBlock(p));
            split(merged_block_size, newsize, p);
            setBlockSize(p, merged_block_size);
            setAllocStatus(p, ALLOCATED);
            return ptr;
        }

        /*next block allocated, but prev block is free and can accommodate*/
        else if( (allocStatus(nextBlock(p)) == ALLOCATED)
                && ((allocStatus(p-1) == FREE) && ((blockSize(p) + blockSize(p-1)) >= newsize)) )
        { 
            size_t merged_block_size = blockSize(p) + blockSize(p-1);
            size_t *prev_block_head = prevBlock(p);
            memcpy((prev_block_head + 1), ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE);

            split(merged_block_size, newsize, prev_block_head);
            setBlockSize(prev_block_head, merged_block_size);
            setAllocStatus(prev_block_head, ALLOCATED);

            return (prev_block_head + 1);

        }

        /*next block free but combined size cannot accomodate, check if prev block free and if adding its size can accommodate*/
        else if ( (blockSize(p) + blockSize(nextBlock(p)) < newsize)
                && (allocStatus(p-1) == FREE && (blockSize(p-1) + blockSize(p) + blockSize(nextBlock(p))) >= newsize))
        {
            size_t merged_block_size = blockSize(p-1) + blockSize(p) + blockSize(nextBlock(p));
            size_t *prev_block_head = prevBlock(p);
            memcpy(prev_block_head + 1, ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE);

            split(merged_block_size, newsize, prev_block_head);
            setBlockSize(prev_block_head, merged_block_size);
            setAllocStatus(prev_block_head, ALLOCATED);
            return (prev_block_head + 1);
        }

        /*all other cases: find a new block to allocate with size + curr_size, 
        copy memory of curr_size bytes to this new block,
        and free curr block (ptr)*/
        else
        {
            void *new_block = mm_malloc(newsize);
            memcpy(new_block, ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE); /*copy the payload only, exclude header & footer*/
            mm_free((char *)(p) + SIZE_T_SIZE);
            return new_block;
        }
    }

    /*if size < curr_size -> set ptr's size to size, free block of curr_size-size bytes */
    else if (blockSize(p) > newsize)
    {
        size_t remaining_size = blockSize(p) - newsize;
        setBlockSize(p, newsize);
        setAllocStatus(p, ALLOCATED);
    
        size_t* remaining_block = nextBlock(p);
        setBlockSize(remaining_block, remaining_size);
        setAllocStatus(remaining_block, FREE);

        coalesce(remaining_block);
        return ptr; 
    }
    return ptr;
}


void split(size_t total, size_t taken, size_t* taken_blk)
/*block @ taken_blk will be allocated with size taken and any leftover will be free block*/
{
    if (total > taken && total - taken >= MINBLOCKSIZE)
    {
        /*only set BLOCKSIZE to newsize if splitted, otherwise BLOCKSIZE is existing BLOCKSIZE -> just set alloc bit*/
        setBlockSize(taken_blk, taken);
        
        size_t remains = total - taken;
        size_t* remains_blk = nextBlock(taken_blk);

        setBlockSize(remains_blk, remains);
        setAllocStatus(remains_blk, FREE);

    }
}



void* coalesce(size_t* to_free)
{
    /*previous and next both allocated, simply reset allocate bit*/
    if(allocStatus(nextBlock(to_free)) == ALLOCATED && allocStatus(to_free - 1) == ALLOCATED)
    {
        setAllocStatus(to_free, FREE);
        return (void*) to_free;
    }

    /*next block free, previous block allocated*/
    else if (allocStatus(nextBlock(to_free)) == FREE && allocStatus(to_free - 1) == ALLOCATED)
    {
        setBlockSize(to_free, blockSize(to_free) + blockSize(nextBlock(to_free)));
        setAllocStatus(to_free, FREE);

        return (void*) to_free;
    }

    /*previous block free, next block allocated*/
    else if (allocStatus(nextBlock(to_free)) == ALLOCATED && allocStatus(to_free - 1) == FREE)
    {
        size_t *prev_block_head = prevBlock(to_free);
        setBlockSize(prev_block_head, blockSize(prev_block_head) + blockSize(to_free));
        setAllocStatus(prev_block_head, FREE);

        return (void*) prev_block_head;
    }
    /*previous and next free*/
    else
    {
        size_t *prev_block_head = prevBlock(to_free);
        setBlockSize(prev_block_head, blockSize(prev_block_head) + blockSize(to_free) + blockSize(nextBlock(to_free)));
        setAllocStatus(prev_block_head, FREE);

        return (void*) prev_block_head;
    }
}



int mm_check(void)
{

    
}
