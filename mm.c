/*
 * mm.c - The fastest, not the most memory-efficient malloc package.
 *
 * In this approach, a block is allocated by finding its appropriate bin based on its size.
 * The free block found is then allocated and splitted if necessary, the free block returns 
 * to its appropriate free list. When a block is freed, it is coalesced with adjacent blocks.
 * The combined free block returns to its free list. Each block has at least one header, one footer,
 * and a pred and succ pointers for free block management. Realloc is implemented using mm_malloc and
 * mm_free, which handles three main cases: new block shrinks, new block expands on an adjacent next
 * block, and others where calls to malloc and memcpy will be needed. However, there are room for
 * improvements in which previous free block can be considered, which will likely reduce fragmentation.
 *
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

/*double word (8) alignment */
#define ALIGNMENT 8 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) /*one word size - 8 bytes*/

#define ALLOCATED 1
#define FREE 0
#define MINBLOCKSIZE (SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE) /*header, footer, pred, succ*/
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

size_t* nextBlock(size_t *head){return head + blockSize(head) / SIZE_T_SIZE;}
size_t* prevBlock(size_t* head){return head - blockSize(head - 1) / SIZE_T_SIZE;}

size_t* getPred(size_t* head){return (size_t*) (*(head + 1));}
size_t* getSucc(size_t* head){return (size_t*) (*(head + 2));}
void setPred(size_t* head, size_t* ptr){*(head + 1) = ptr;}
void setSucc(size_t* head, size_t* ptr){*(head + 2) = ptr;}

int endOfList(size_t* head){return (getSucc(head) == NULL);}
int atEpilogue(size_t* head){return (allocStatus(head) == ALLOCATED) && (blockSize(head) == 0);}

/*key functions' signatures*/
void allocSplit(size_t total, size_t taken, size_t* taken_blk);
void* coalesce(size_t* to_free);
void splice(size_t* head);  /*reconnect the predecessor and the successor of a block*/
void insertFreeBlock(size_t* free_list, size_t* head);
int findBin(size_t size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();    

    /*4 for head, foot, pred, succ of sentinel, 2 sentinels head and tail, BINCOUNT of those for BINCOUNT free lists, plus one for epilogue*/
    mem_sbrk(MINBLOCKSIZE * 2 * BINCOUNT + SIZE_T_SIZE); 
    
    /*initialize the epilogue block*/
    size_t* epilogue = (size_t *)mem_heap_hi();
    epilogue = (char *)(epilogue) + 1; 
    epilogue = epilogue - 1;
    *epilogue = 0x1;                /*epilogue is allocated with size 0*/

    for(int i = 0; i < BINCOUNT; i++)
    {
        /*get sentinel head*/
        bins[i] = ((size_t*) mem_heap_lo()) + (MINBLOCKSIZE * 2 * i) / SIZE_T_SIZE;  
        
        /*initialize sentinel head*/
        setBlockSize(bins[i], MINBLOCKSIZE);  
        setAllocStatus(bins[i], ALLOCATED);
        setPred(bins[i], NULL);
        setSucc(bins[i], nextBlock(bins[i]));

        /*get sentinel tail*/
        size_t* free_list_t = nextBlock(bins[i]);

        /*initialize sentinel tail*/
        setBlockSize(free_list_t, MINBLOCKSIZE); 
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
    int newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE); /*align with header, footer, pred, succ*/
    int starting_bin = findBin(newsize);                                /*the smallest bin that a search for free blocks starts from*/

    for (int b = starting_bin; b < BINCOUNT; b++)
    {
        size_t* blk = bins[b]; 
        while (!(endOfList(blk)) &&                                     /*boundary check*/
            (allocStatus(blk) == ALLOCATED ||                           /*while not yet found a free block*/
                blockSize(blk) < newsize))                              /*or block does not fit*/
        {
            blk = getSucc(blk);                                         /*get to next free block*/
        }
        
        /*found a free large enough block*/
        if (allocStatus(blk) == FREE && blockSize(blk) >= newsize) 
        {
            splice(blk);                                     /*take blk out of its free list, reconnecting its predecessor with its successor*/
            allocSplit(blockSize(blk), newsize, blk);        /*allocate it and split if necessary*/
            return (void *)((size_t*)blk + 1);               /*return start of payload*/
        }
    }

    /*reaching here means there are no free blocks available, requesting more memory*/
    void* new_mem = mem_sbrk(newsize); 
    if (new_mem == (void*) - 1)                     /*memory request failed*/
        return NULL;
    else
    {
        /*initialize the newly allocated memory*/
        setBlockSize(new_mem, newsize);
        setAllocStatus(new_mem, FREE);     
        
        /*new epilogue*/
        *(nextBlock(new_mem)) = 0x1;
        
        new_mem = (size_t*) (coalesce(new_mem));                /*coalesce new free block with any adjacent free blocks*/
        splice(new_mem);                                        /*take new_mem out of its free list, reconnecting its predecessor with its successor*/
        allocSplit(blockSize(new_mem), newsize, new_mem);       /*allocate it and split if necessary*/
        return (void *)((size_t*)(new_mem) + 1);                /*return start of payload*/
    }
}


/*
 * mm_free - Free a block and coalesce with any adjacent free blocks.
 */
void mm_free(void *ptr)
{
    size_t* blk = (char *)(ptr - SIZE_T_SIZE);  /*get the header*/
    coalesce(blk);                              /*free and coalesce*/
}

/*
 * mm_realloc - Implemented in terms of mm_malloc and mm_free. 
Support three cases:
1. Block shrinks
2. Block gets bigger and there is adjacent free memory to contain it.
3. Other cases: malloc a new block, copy current block to new block, and free the current block.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)                /*realloc a NULL block is equivalent to malloc a new block*/
        return mm_malloc(size);
        
    if (size == 0)                  /*realloc to size 0 is equivalent to free*/
    {
        mm_free(ptr);
        return (void *)NULL;
    }

    size_t newsize = ALIGN(size + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE + SIZE_T_SIZE);
    size_t* blk = (size_t*)(ptr - SIZE_T_SIZE);

    if (blockSize(blk) < newsize)
    {
        /*if next free block (if any) enough to hold newsize -> realloc in place*/
        if (allocStatus(nextBlock(blk)) == FREE && blockSize(blk) + blockSize(nextBlock(blk)) >= newsize)
        {
            size_t* next_block_head = nextBlock(blk);
            size_t merged_block_size = blockSize(blk) + blockSize(next_block_head);

            /*splice free next block*/
            splice(next_block_head);
            
            /*change the block size accordingly and split it if necessary*/
            setBlockSize(blk, merged_block_size); 
            setAllocStatus(blk, ALLOCATED);
            allocSplit(merged_block_size, newsize, blk);
            return ptr;
        }

        /*malloc a new block, copy current block to this new block, and free current block*/
        else
        {
            void* new_block = mm_malloc(newsize);
            memcpy(new_block, ptr, blockSize(blk) - SIZE_T_SIZE - SIZE_T_SIZE );  /*copy the payload only, exclude header & footer*/
            mm_free(ptr);
            return new_block;
        }
    }

    /*block shrinks -> free the remaining memory; only split if remaining is at least MINBLOCKSIZE */
    else if (blockSize(blk) > newsize && blockSize(blk) - newsize >= MINBLOCKSIZE)
    {
        size_t remaining_size = blockSize(blk) - newsize;

        /*change current block's size to newsize*/  
        setBlockSize(blk, newsize);
        setAllocStatus(blk, ALLOCATED);
    
        size_t* remaining_block = nextBlock(blk);

        /*set remaining block's size and coalesce it*/
        setBlockSize(remaining_block, remaining_size);
        setAllocStatus(remaining_block, FREE);
        coalesce(remaining_block);
        return ptr; 
    }
    return ptr;
}

/*this function checks if a block can be splitted, set the headers and footers of the blocks,
return the free block to its appropriate free list, and mark the allocated block*/
void allocSplit(size_t total, size_t taken, size_t* taken_blk)
/*block @ taken_blk will be allocated with size taken and any leftover will be free block*/
{
    if (total > taken && total - taken >= MINBLOCKSIZE)
    {
        setBlockSize(taken_blk, taken);

        /*set fields for the remaining memory*/
        size_t* remains_blk = nextBlock(taken_blk);
        setBlockSize(remains_blk, total - taken);
        setAllocStatus(remains_blk, FREE);
        
        /*coalesce remaining memory with any adjacent free block*/
        setAllocStatus(taken_blk, ALLOCATED);
        coalesce(remains_blk);
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
        /*splice free next block*/
        size_t* next_block_head = nextBlock(to_free);
        splice(next_block_head);

        /*change to total size*/
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
        /*splice free prev block*/
        size_t *prev_block_head = prevBlock(to_free);
        splice(prev_block_head);

        /*change to total size*/
        setBlockSize(prev_block_head, blockSize(prev_block_head) + blockSize(to_free));
        setAllocStatus(prev_block_head, FREE);

        /*add free block to head of free list*/
        size_t* free_list_h = bins[findBin(blockSize(prev_block_head))];
        insertFreeBlock(free_list_h, prev_block_head);
        return (void*) prev_block_head;
    }

    /*previous and next free*/
    else
    {        
        /*splice free prev block*/
        size_t* prev_block_head = prevBlock(to_free);
        splice(prev_block_head);

        /*splice free next block*/
        size_t* next_block_head = nextBlock(to_free);
        splice(next_block_head);

        /*change to total size*/
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
