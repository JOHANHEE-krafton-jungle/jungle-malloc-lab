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
    "a team",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기를 정렬 기준에 맞춰서 바꾼 값

/* custom define */
#define WSIZE 8 /* 워드, 헤더랑 풋터의 사이즈 (바이트) */
#define DSIZE 16 /* 더블 워드의 크기 (바이트) */
#define CHUNKSIZE (1<<12) /* 힙을 얼마만큼 확장할 것인지 (4KB) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc)) /* 워드에 사이즈와 할당 여부를 표시 */

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드를 읽어서 리턴함
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* p를 unsigned int를 가리키는 포인터로 형변환한 뒤, p가 가리키는 메모리 공간에 val 값을 저장 */

#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 헤더에서 사이즈를 리턴함
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 헤더에서 할당 여부를 리턴함

#define HDRP(bp) ((char *)(bp) - WSIZE) // bp=블록 시작 포인터 받아서, 블록 헤더의 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 풋터의 주소 계산 (시작 포인터 + 블록 헤더에서 데이터 부분 사이즈 읽어옴 - 워드 사이즈의 2배)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 블록 포인터 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 블록 포인터 계산

static char* heap_listp; // 가용 리스트의 데이터 블록 시작 부분을 가리킴 (prologue 바로 뒤)

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // 앞 뒤 모두 할당된 상태
        return bp;
    } else if (prev_alloc && !next_alloc) { // 뒤에만 가용인 상태
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) { // 앞에만 가용인 상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)))); // 둘 다 가용인 상태
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/* 힙을 CHUNKSIZE 바이트로 확장하고, 실패하면 NULL, 성공하면 통합을 시행한다. */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) { 
        return NULL; // sbrk 실패하면 NULL값 반환
    }

    // 확장된 가용 블록의 header와 footer 초기화
    PUT(HDRP(bp), PACK(size, 0)); // hear 초기화
    PUT(FTRP(bp), PACK(size, 0)); // footer 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // epliogue header 초기화

    return coalesce(bp);
}

static void *find_fit(size_t size) {
    // size를 받아서, 해당 size에 적합한 블록의 포인터를 반환함

    // first fit으로 해보자
    // 전체 블록 순회하면서, 이미 할당된 상태이면 패스, 가용 가능하고 크기가 인자값 size보다 크거나 같으면 해당 블록의 시작 주소 반환

    char *curr_ptr = heap_listp;

    while (1) {
        if (GET_SIZE(HDRP(curr_ptr)) <= 0) {
            return NULL; // 할당되어 있는데, SIZE가 0인 경우
        }
        
        if (!(GET_ALLOC(HDRP(curr_ptr))) && GET_SIZE(HDRP(curr_ptr)) >= size) {
            break; // 할당할 수 있고, Size가 더 큼
        }
        
        curr_ptr = NEXT_BLKP(curr_ptr);
    }

    return curr_ptr;
}

static void place(char *bp, size_t size) {
    // bp 포인터를 받아서, 해당 bp 위치에 size만큼의 메모리를 할당함
    size_t prev_size = GET_SIZE(HDRP(bp));

    if ((prev_size - size) >= (2*DSIZE)) {
        // bp로 시작하는 메모리 공간에 adjustedSize만큼 공간 할당
        PUT(HDRP(bp), PACK(size, 1)); // head에 size, 1 할당
        PUT(FTRP(bp), PACK(size, 1)); // footer 초기화    
        bp = NEXT_BLKP(bp);

        // 빈 공간은 쪼갠 상태로 다시 표기
        PUT(HDRP(bp), PACK(prev_size - size, 0));
        PUT(FTRP(bp), PACK(prev_size - size, 0));
    } else {
        PUT(HDRP(bp), PACK(prev_size, 1)); // head에 size, 1 할당
        PUT(FTRP(bp), PACK(prev_size, 1)); // footer 초기화    
    }
}

/* 할당기를 초기화하고, 성공이면 0 아니면 1을 리턴한다. */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // Epilogue header
    heap_listp += (2*WSIZE); // prologue 건너뛰고, 실제 데이터 공간으로 이동

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t adjustedSize;
    size_t extendedSize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        adjustedSize = 2*DSIZE;
    } else {
        adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // 적절한 가용리스트를 찾음 (할당 정책은 find fit)
    if ((bp = find_fit(adjustedSize)) != NULL) {
        place(bp, adjustedSize);
        return bp;
    }

    // 적절한 가용 리스트를 못 찾으면 추가 메모리를 요청함
    extendedSize = MAX(adjustedSize, CHUNKSIZE);
    if ((bp = extend_heap(extendedSize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, adjustedSize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 ptr가 가리키는 메모리 주소의 크기를 size 바이트로 확장
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}