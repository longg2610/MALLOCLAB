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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16  /*double word is 16 bytes is 64-bit systems*/

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))  /*one word size - 8 bytes*/

#define ALLOCATED 1
#define FREE 0
#define BLOCK_SIZE(word) (*word & ~0x7)
#define ALLOC_STATUS(word) (*word & 0x1)
#define MINBLOCKSIZE (SIZE_T_SIZE + SIZE_T_SIZE)


int* heap_end;
size_t* nextBlock(size_t* word)
{
    return word + BLOCK_SIZE(word) / SIZE_T_SIZE;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();

    heap_end = (int*) mem_heap_hi();
    *heap_end &= 0x0;       /*clear all bits*/
    *heap_end |= 0x1;       /*and set allocated with size 0 to mark end of heap*/
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	    return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/


    size_t* ptr = (size_t*) mem_heap_lo();
    ptr += 1;  /*first word unused*/
    int newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE);  /*header and footer, two extra words*/
    
    /*policy: first-fit*/
    while(!(ALLOC_STATUS(ptr) == ALLOCATED && BLOCK_SIZE(ptr) == 0) &&       /*boundary check*/
        (ALLOC_STATUS(ptr) == ALLOCATED ||                           /*while not yet found a free block*/
        BLOCK_SIZE(ptr) < newsize))                       /*or block does not fit*/
    {
        ptr = nextBlock(ptr); /* get to next block (alternative: (char*) heap_start + BLOCK_SIZE(heap_start))*/
    }
    

    if (ALLOC_STATUS(ptr) == ALLOCATED && BLOCK_SIZE(ptr) == 0)  /*end of heap, request more VM*/
    {
        void *p = mem_sbrk(newsize);
        if (p == (void *)-1)
            return NULL;
        else 
        {
            size_t* new_mem = (size_t*) p;
            *new_mem = newsize;
            *new_mem |= ALLOCATED; 

            /*footer*/
            *(new_mem + BLOCK_SIZE(new_mem) / SIZE_T_SIZE - 1) = newsize;
            *(new_mem + BLOCK_SIZE(new_mem) / SIZE_T_SIZE - 1) |= ALLOCATED;

            /*increment p to skip header word, (char*) p to make p byte-addressable*/
            return (void *)((char *)new_mem + SIZE_T_SIZE); 
        } 
    }  

    /*policy: split*/
    else if(ALLOC_STATUS(ptr) == FREE && BLOCK_SIZE(ptr) >= newsize)  /*found a free large enough block*/
    {
        /*split if there is extra space and extra space is at least minimum block size*/
        if(BLOCK_SIZE(ptr) > newsize && BLOCK_SIZE(ptr) - newsize >= MINBLOCKSIZE)
        {
            size_t* free_split = ptr + newsize / SIZE_T_SIZE;
            *free_split = BLOCK_SIZE(ptr) - newsize;                           /*set header of new splited block*/
            *free_split &= ~0x7;                                         /*reset allocate bit*/
            *(free_split + BLOCK_SIZE(free_split) / SIZE_T_SIZE - 1) = BLOCK_SIZE(free_split);   /*footer of new splited block*/
            *(free_split + BLOCK_SIZE(free_split) / SIZE_T_SIZE - 1) &= ~0x7;
        }
        

        *ptr = newsize;
        *ptr |= ALLOCATED; 
        *(ptr + BLOCK_SIZE(ptr) / SIZE_T_SIZE - 1) = newsize;
        *(ptr + BLOCK_SIZE(ptr) / SIZE_T_SIZE - 1) |= ALLOCATED;
        return (void*) ((char*) ptr + SIZE_T_SIZE);   /*return start of payload*/
    }
        



}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t* to_free = (char*) (ptr - SIZE_T_SIZE);
    /*reset allocate bit*/
    *to_free &= ~0x7; 
    *(to_free + BLOCK_SIZE(to_free) / SIZE_T_SIZE - 1) &= ~0x7;

    size_t* prev_block_foot = to_free - 1;

    /*next block free*/
    if(ALLOC_STATUS(nextBlock(to_free)) == FREE)
    {
        *to_free = BLOCK_SIZE(to_free) + BLOCK_SIZE(nextBlock(to_free));
        *to_free &= ~0x7;
        *(to_free + BLOCK_SIZE(to_free) / SIZE_T_SIZE - 1) = BLOCK_SIZE(to_free);
        *(to_free + BLOCK_SIZE(to_free) / SIZE_T_SIZE - 1) &= ~0x7;
    }

    /*previous block free*/
    if(ALLOC_STATUS(prev_block_foot) == FREE)
    {
        size_t* prev_block_head = prev_block_foot - (BLOCK_SIZE(prev_block_foot) / SIZE_T_SIZE) + 1;
        *prev_block_head = BLOCK_SIZE(to_free) + BLOCK_SIZE(prev_block_head);
        *prev_block_head &= ~0x7;
        *(prev_block_head + BLOCK_SIZE(prev_block_head) / SIZE_T_SIZE - 1) = BLOCK_SIZE(prev_block_head);
        *(prev_block_head + BLOCK_SIZE(prev_block_head) / SIZE_T_SIZE - 1) &= ~0x7;
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    /*
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
    */
    if(ptr == NULL)
    {
        return mm_malloc(size);
    }

    if(size == 0)
    {
        mm_free(ptr);
        return (void*) NULL;
    }

    /*size > curr_size ->  
    if yes then change size of curr_size, and split if there are remaining memory
    if no then */

    size_t newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE);
    size_t* p = (size_t*) ((char*) (ptr - SIZE_T_SIZE));
    if(BLOCK_SIZE(p) < newsize)
    {
        /*if next free block (if any) enough to hold size - curr_size bytes -> realloc in place*/
        if(ALLOC_STATUS(nextBlock(p)) == FREE && BLOCK_SIZE(p) + BLOCK_SIZE(nextBlock(p)) >= newsize)
        {
            size_t merged_block_size = BLOCK_SIZE(p) + BLOCK_SIZE(nextBlock(p));
            *p = merged_block_size;
            *p |= ALLOCATED;

            *(p + BLOCK_SIZE(p) / SIZE_T_SIZE - 1) = merged_block_size;
            *(p + BLOCK_SIZE(p) / SIZE_T_SIZE - 1) |= ALLOCATED;

            /*split if newly merged block bigger than newsize*/
            if(merged_block_size > newsize && merged_block_size - newsize >= MINBLOCKSIZE)
            {
                size_t* free_split = p + newsize / SIZE_T_SIZE;
                *free_split = merged_block_size - newsize;                           /*set header of new splited block*/
                *free_split &= ~0x7;
                *(free_split + BLOCK_SIZE(free_split) / SIZE_T_SIZE - 1) = BLOCK_SIZE(free_split);   /*footer of new splited block*/
                *(free_split + BLOCK_SIZE(free_split) / SIZE_T_SIZE - 1) &= ~0x7;
            }

            return ptr;
        }
        /*find a new block to allocate with size + curr_size, copy memory of curr_size bytes to this new block,
        and free curr block (ptr)*/
        else 
        {
            void* new_block = mm_malloc(newsize);
            memcpy(new_block, p, BLOCK_SIZE(p));
            mm_free((char*) (p + SIZE_T_SIZE));
            return new_block;
        }

    }

    /*if size < curr_size -> set ptr's size to size, free block of curr_size-size bytes */
    else if(BLOCK_SIZE(p) > newsize)
    {
        size_t remaining_size = BLOCK_SIZE(p) - newsize;

        *p = newsize;
        *p |= ALLOCATED;

        /*footer*/
        *(p + BLOCK_SIZE(p) / SIZE_T_SIZE - 1) = newsize;
        *(p + BLOCK_SIZE(p) / SIZE_T_SIZE - 1) |= ALLOCATED;

        size_t* remaining_block = p + BLOCK_SIZE(p) / SIZE_T_SIZE;
        *remaining_block = remaining_size;
        *remaining_block &= ~0x7;
        *(remaining_block + BLOCK_SIZE(remaining_block) / SIZE_T_SIZE - 1) = remaining_size;
        *(remaining_block + BLOCK_SIZE(remaining_block) / SIZE_T_SIZE - 1) &= ~0x7;

        mm_free((char*) (remaining_block + SIZE_T_SIZE));

        return ptr; /*realloc in place*/

    }
    
}


int mm_check(void)
{

}











