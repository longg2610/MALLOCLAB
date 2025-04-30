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

#define ALLOCATED 1
#define FREE 0
#define MINBLOCKSIZE (SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE)
#define BINCOUNT 20

size_t* bins [BINCOUNT];    /*segregated free list bins*/

/*helper functions*/
void print_free_list(size_t* free_list_h);
size_t blockSize(size_t* head){return (*head) & (~0x7);}
size_t allocStatus(size_t* head){return (*head) & (0x1);}
void setBlockSize(size_t* head, size_t size)
{
    *head = size;
    *(head + blockSize(head) / SIZE_T_SIZE - 1) = size;
}

void setAllocStatus(size_t* head, int alloc_status)
{
    if (alloc_status == ALLOCATED)
    {
        *head |= ALLOCATED;
        *(head + blockSize(head) / SIZE_T_SIZE - 1) |= ALLOCATED;
    }
        
    else
    {
        *head &= ~ALLOCATED;
        *(head + blockSize(head) / SIZE_T_SIZE - 1) &= ~ALLOCATED;
    } 
}

size_t* getPred(size_t* head){return (size_t*) (*(head + 1));}
size_t* getSucc(size_t* head){return (size_t*) (*(head + 2));}

void setPred(size_t* head, size_t* ptr){*(head + 1) = ptr;}
void setSucc(size_t* head, size_t* ptr){*(head + 2) = ptr;}

size_t* nextBlock(size_t *head){return head + blockSize(head) / SIZE_T_SIZE;}
size_t* prevBlock(size_t* head){return head - blockSize(head - 1) / SIZE_T_SIZE;}
int atEpilogue(size_t* ptr){return (allocStatus(ptr) == ALLOCATED) && (blockSize(ptr) == 0);}
int endOfList(size_t* block){return (getSucc(block) == NULL);}
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
void splice(size_t* block);
void insertFreeBlock(size_t* free_list, size_t* block);
int findBin(size_t size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();    
    /*4 for head, foot, pred, succ of sentinel, 2 sentinels head and tail, BINCOUNT of those for BINCOUNT free lists. plus one for epilogue*/
    mem_sbrk(MINBLOCKSIZE * 2 * BINCOUNT + SIZE_T_SIZE); 
    
    /*initialize the epilogue block*/
    size_t* epilogue = (size_t *)mem_heap_hi();
    epilogue = (char *)(epilogue) + 1; 
    epilogue = epilogue - 1;
    *epilogue = 0x1; /*allocated with size 0*/

    for(int i = 0; i < BINCOUNT; i++)
    {
        bins[i] = ((size_t*) mem_heap_lo()) + (MINBLOCKSIZE * 2 * i) / SIZE_T_SIZE;   
        setBlockSize(bins[i], MINBLOCKSIZE);  /*sentinel head*/
        setAllocStatus(bins[i], ALLOCATED);
        setPred(bins[i], NULL);
        setSucc(bins[i], nextBlock(bins[i]));

        size_t* free_list_t = nextBlock(bins[i]);
        setBlockSize(free_list_t, MINBLOCKSIZE);  /*sentinel tail*/
        setAllocStatus(free_list_t, ALLOCATED);
        setPred(free_list_t, bins[i]);
        setSucc(free_list_t, NULL);
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if(size == 0)        /*spurious requests*/
        return NULL; 
    int newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE); /*header, footer, pred, succ*/
    int starting_bin = findBin(newsize);

    for (int b = starting_bin; b < BINCOUNT; b++)
    {
        size_t* ptr = bins[b]; 
        while (!(endOfList(ptr)) &&                                   /*boundary check*/
            (allocStatus(ptr) == ALLOCATED ||                           /*while not yet found a free block*/
                blockSize(ptr) < newsize))                                 /*or block does not fit*/
        {
            ptr = getSucc(ptr);   /*get to next free block*/
        }
        
        /*found a free large enough block*/
        if (allocStatus(ptr) == FREE && blockSize(ptr) >= newsize) 
        {
            split(blockSize(ptr), newsize, ptr);
            return (void *)((size_t*)ptr + 1); /*return start of payload*/
        }
        
    }


    void* new_mem = mem_sbrk(newsize); 
    if (new_mem == (void *)-1)
        return NULL;
    else
    {
        setBlockSize(new_mem, newsize);
        setAllocStatus(new_mem, FREE);      /*new mem free, coalesce*/
        
        /*new epilogue*/
        *(nextBlock(new_mem)) = 0x1;
        
        new_mem = (size_t*) (coalesce(new_mem));
        split(blockSize(new_mem), newsize, new_mem);
        return (void *)((size_t*)(new_mem) + 1); /*return start of payload*/
    }
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t* to_free = (char *)(ptr - SIZE_T_SIZE);
    coalesce(to_free);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return (void *)NULL;
    }

    size_t newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE);
    size_t* p = (size_t*)(ptr - SIZE_T_SIZE);

    if (blockSize(p) < newsize)   /*unlike in malloc, p is ALLOCATED*/
    {
        /*if next free block (if any) enough to hold size - curr_size bytes -> realloc in place*/
        if (allocStatus(nextBlock(p)) == FREE && blockSize(p) + blockSize(nextBlock(p)) >= newsize)
        {
            size_t* next_block_head = nextBlock(p);
            size_t merged_block_size = blockSize(p) + blockSize(next_block_head);

            /*splice free next block*/
            splice(next_block_head);
            
            setBlockSize(p, merged_block_size); 
            setAllocStatus(p, ALLOCATED);
            split(merged_block_size, newsize, p);
                    
            return ptr;
        }

        /*all other cases: find a new block to allocate with size + curr_size, 
        copy memory of curr_size bytes to this new block,
        and free curr block (ptr)*/
        else
        {
            void* new_block = mm_malloc(newsize);
            memcpy(new_block, ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE );  /*copy the payload only, exclude header & footer*/
            mm_free(ptr);
            return new_block;
        }
    }

    /*if size < curr_size -> set ptr's size to size, free block of curr_size-size bytes, only split if remaining is at least MINBLOCKSIZE */
    else if (blockSize(p) > newsize && blockSize(p) - newsize >= MINBLOCKSIZE)
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
    int taken_blk_alloc_status = allocStatus(taken_blk);
    if (total > taken && total - taken >= MINBLOCKSIZE)
    {
        /*only set BLOCKSIZE to newsize if splitted, otherwise BLOCKSIZE is existing BLOCKSIZE -> just set alloc bit*/
        setBlockSize(taken_blk, taken);
        size_t* remains_blk = nextBlock(taken_blk);
        setBlockSize(remains_blk, total - taken);
        setAllocStatus(remains_blk, FREE);

        /*only get free blocks iff taken_blk is FREE, as in realloc it is ALLOCATED*/
        if(taken_blk_alloc_status == FREE)
        {
            splice(taken_blk);
        }

        size_t* free_list_h = bins[findBin(blockSize(remains_blk))];
        insertFreeBlock(free_list_h, remains_blk); /*both alloc and realloc returns the remaining memory to head of free list*/
    }

    /*cant split, malloc needs to reconnect pointers (realloc already reconnected inside realloc's function body)*/
    else if (taken_blk_alloc_status == FREE)   
    {
        splice(taken_blk);
    }
   
    setAllocStatus(taken_blk, ALLOCATED);  /*mark taken_blk as ALLOCATED*/
}

void* coalesce(size_t* to_free)
{    
    /*previous and next both allocated, simply reset allocate bit*/
    if(allocStatus(nextBlock(to_free)) == ALLOCATED && allocStatus(to_free - 1) == ALLOCATED)
    {
        setAllocStatus(to_free, FREE);

        /*add free block to head of free list*/
        size_t* free_list_h = bins[findBin(blockSize(to_free))];
        insertFreeBlock(free_list_h, to_free);
        return (void*) to_free;
    }

    /*next block free, previous block allocated*/
    else if (allocStatus(nextBlock(to_free)) == FREE && allocStatus(to_free - 1) == ALLOCATED)
    {
        /*splice*/
        size_t* next_block_head = nextBlock(to_free);
        splice(next_block_head);

        setBlockSize(to_free, blockSize(to_free) + blockSize(next_block_head));
        setAllocStatus(to_free, FREE);

        /*add free block to head of free list*/
        size_t* free_list_h = bins[findBin(blockSize(to_free))];
        insertFreeBlock(free_list_h, to_free);
        return (void*) to_free;
    }

    /*previous block free, next block allocated*/
    else if (allocStatus(nextBlock(to_free)) == ALLOCATED && allocStatus(to_free - 1) == FREE)
    {
        size_t *prev_block_head = prevBlock(to_free);
        splice(prev_block_head);

        setBlockSize(prev_block_head, blockSize(prev_block_head) + blockSize(to_free));
        setAllocStatus(prev_block_head, FREE);

        /*add free block to head of free list (same code as above)*/
        size_t* free_list_h = bins[findBin(blockSize(prev_block_head))];
        insertFreeBlock(free_list_h, prev_block_head);
        return (void*) prev_block_head;
    }

    /*previous and next free*/
    else
    {        
        size_t* prev_block_head = prevBlock(to_free);
        size_t* next_block_head = nextBlock(to_free);

        splice(prev_block_head);
        splice(next_block_head);

        setBlockSize(prev_block_head, blockSize(prev_block_head) + blockSize(to_free) + blockSize(next_block_head));
        setAllocStatus(prev_block_head, FREE);

        /*add free block to head of free list*/
        size_t* free_list_h = bins[findBin(blockSize(prev_block_head))];
        insertFreeBlock(free_list_h, prev_block_head);
        return (void*) prev_block_head;
    }
}

void insertFreeBlock(size_t* free_list, size_t* block)
{
    size_t* cur_first_block = getSucc(free_list);
    setSucc(block, cur_first_block);
    setPred(cur_first_block, block);
    setSucc(free_list, block);
    setPred(block, free_list);
}

void splice(size_t* block)
{
    size_t* pred = getPred(block);
    size_t* succ = getSucc(block);
    setSucc(pred, succ);
    setPred(succ, pred);
}

int findBin(size_t size)
{
    if (size <= 16) return 0;
    if (size <= 32) return 1;
    if (size <= 64) return 2;
    if (size <= 128) return 3;
    if (size <= 256) return 4;
    if (size <= 512) return 5;
    if (size <= 1024) return 6;
    if (size <= 2048) return 7;
    if (size <= 4096) return 8;
    if (size <= 8192) return 9;
    if (size <= 16384) return 10;
    if (size <= 32768) return 11;
    if (size <= 65536) return 12;
    if (size <= 131072) return 13;
    if (size <= 262144) return 14;
    if (size <= 524288) return 15;
    if (size <= 1048576) return 16;
    if (size <= 2097152) return 17;
    if (size <= 4194304) return 18;
    return 19;  // fallback bin for very large blocks
}

void print_free_list(size_t* free_list_h)
{
    size_t* ptr = free_list_h;
    while (!endOfList(ptr))
    {
        printf("%d -> ",ptr);
        ptr = getSucc(ptr);
    }
    printf("EOL\n");
}

/*MALLOC-SPLIT FOR ADDRESS-ORDERED FREE LIST*/
/*size_t* prev_free = getPred(taken_blk);
size_t* next_free = getSucc(taken_blk);
setSucc(prev_free, remains_blk);            
setPred(remains_blk, prev_free);
if(!atEpilogue(next_free))
    setPred(next_free, remains_blk);
setSucc(remains_blk, next_free);*/


/*OPTIMIZATION FOR REALLOC WHICH CONSIDERS PREV BLOCK AS WELL*/

/*next block allocated, but prev block is free and can accommodate*/
/*else if( (allocStatus(nextBlock(p)) == ALLOCATED)
        && ((allocStatus(p-1) == FREE) && ((blockSize(p) + blockSize(p-1)) >= newsize)) )
{ 
    printf("case 2\n");
    
    size_t *prev_block_head = prevBlock(p);
    size_t* prev_blk_head_pred = getPred(prev_block_head);
    size_t* prev_blk_head_succ = getSucc(prev_block_head);
    size_t merged_block_size = blockSize(p) + blockSize(prev_block_head);

    setSucc(prev_blk_head_pred, prev_blk_head_succ);
    if(!atEpilogue(prev_blk_head_succ))
        setPred(prev_blk_head_succ, prev_blk_head_pred);

    setBlockSize(prev_block_head, merged_block_size);
    setAllocStatus(prev_block_head, FREE);
    int splitted = split(merged_block_size, newsize, prev_block_head);
    memcpy((prev_block_head + 1), ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE);
    printf("splitted: %d\n", splitted);
    setAllocStatus(prev_block_head, ALLOCATED);
    return (prev_block_head + 1);

}*/

/*next block free but combined size cannot accomodate, check if prev block free and if adding its size can accommodate*/
/*else if ( (blockSize(p) + blockSize(nextBlock(p)) < newsize)
        && (allocStatus(p-1) == FREE && (blockSize(p-1) + blockSize(p) + blockSize(nextBlock(p))) >= newsize))
{
    printf("case 3\n");

    size_t merged_block_size = blockSize(p-1) + blockSize(p) + blockSize(nextBlock(p));
    size_t *prev_block_head = prevBlock(p);
    size_t *next_block_head = nextBlock(p);

    setSucc(getPred(prev_block_head), getSucc(prev_block_head));
    if(!atEpilogue(getSucc(prev_block_head)))
        setPred(getSucc(prev_block_head), getPred(prev_block_head));
    
    setSucc(getPred(next_block_head), getSucc(next_block_head));
    if(!atEpilogue(getSucc(next_block_head)))
        setPred(getSucc(next_block_head), getPred(next_block_head));

    setBlockSize(prev_block_head, merged_block_size);
    int splitted = split(merged_block_size, newsize, prev_block_head);
    memcpy(prev_block_head + 1, ptr, blockSize(p) - SIZE_T_SIZE - SIZE_T_SIZE);

    setAllocStatus(prev_block_head, ALLOCATED);
    return (prev_block_head + 1);
}*/
