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

#define GET(p) (*(unsigned long *)(p)) // p가 참조하는 워드를 읽어서 리턴함
#define PUT(p, val) (*(unsigned long *)(p) = (val)) /* p를 unsigned int를 가리키는 포인터로 형변환한 뒤, p가 가리키는 메모리 공간에 val 값을 저장 */

#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 헤더에서 사이즈를 리턴함
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 헤더에서 할당 여부를 리턴함

#define HDRP(bp) ((char *)(bp) - WSIZE) // bp=블록 시작 포인터 받아서, 블록 헤더의 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 풋터의 주소 계산 (시작 포인터 + 블록 헤더에서 데이터 부분 사이즈 읽어옴 - 워드 사이즈의 2배)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 블록 포인터 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 블록 포인터 계산

typedef struct _node {
    struct _node *prev;
    struct _node *next;
} freeListNode;

typedef struct _struct_free_list {
    freeListNode *head;
    freeListNode *tail;
} freeList; 

// 힙 영역의 데이터 블록 시작 부분을 가리킴 (prologue 바로 뒤)
static char* heap_listp; 
// 가용 리스트
static freeList free_list_array[16];

int mm_log2(unsigned long asize) {
    // log2 함수
    int count = 0;

    while (asize > 1) {
        asize >>= 1; // n = n / 2
        count ++;
    }

    return count;
}

// free_list에 bp를 ptr 값으로 갖는 node를 삽입, 머리 부분에 삽입 -> 해제
static void insert_node(freeList *free_list, char *bp) {
    freeListNode *node = (freeListNode *)bp; 

    node->prev = NULL;

    if (free_list->head != NULL) {
        node->next = free_list->head;
        free_list->head->prev = node;
    } else {
        node->next = NULL;
        free_list->tail = node;
    }    

    free_list->head = node;
}

// bp를 ptr 값으로 갖는 node를 찾은 뒤, 해당 노드를 삭제 -> 할당
static void delete_node(freeList *free_list, char *bp) {
    freeListNode *node = (freeListNode *)bp;

    // 찾은 다음 로직
    // if (node == free_list->head && node == free_list->tail) {
    if (!(node->next) && !(node->prev)) {
        // 삭제하려는 노드가 가용 리스트의 유일한 노드인 경우
        free_list->head = NULL;
        free_list->tail = NULL;
    } else if (!(node->prev)) {
        // 삭제하려는 노드가 가용 리스트의 헤드인 경우
        node->next->prev = NULL;
        free_list->head = node->next;
    } else if (!(node->next)) {
        // 삭제하려는 노드가 가용 리스트의 꼬리인 경우
        node->prev->next = NULL;
        free_list->tail = node->prev;
    } else {
        // 일반적인 경우
        node->prev->next = node->next;
        node->next->prev = node->prev;
    }
}

static void *coalesce(void *bp)
{
    // free해서 넘긴 애들을 통합 및 가용 리스트에 담아주기

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t prev_size = GET_SIZE(FTRP(PREV_BLKP(bp)));

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // 앞 뒤 모두 할당된 상태
        int index = (mm_log2(size) > 20) ? 15 : mm_log2(size) - 5;
        insert_node(&(free_list_array[index]), bp);
        return bp;
    } else if (prev_alloc && !next_alloc) { // 뒤에만 가용인 상태
        int next_index = (mm_log2(next_size) > 20) ? 15 : mm_log2(next_size) - 5;
        delete_node(&(free_list_array[next_index]), NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        int index = (mm_log2(size) > 20) ? 15 : mm_log2(size) - 5;
        insert_node(&(free_list_array[index]), bp);
    } else if (!prev_alloc && next_alloc) { // 앞에만 가용인 상태
        int prev_index = (mm_log2(prev_size) > 20) ? 15 : mm_log2(prev_size) - 5;
        delete_node(&(free_list_array[prev_index]), PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        int index = (mm_log2(size) > 20) ? 15 : mm_log2(size) - 5;
        insert_node(&(free_list_array[index]), bp);
    } else {
        int next_index = (mm_log2(next_size) > 20) ? 15 : mm_log2(next_size) - 5;
        int prev_index = (mm_log2(prev_size) > 20) ? 15 : mm_log2(prev_size) - 5;
        delete_node(&(free_list_array[next_index]), NEXT_BLKP(bp));
        delete_node(&(free_list_array[prev_index]), PREV_BLKP(bp));

        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)))); // 둘 다 가용인 상태
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        int index = (mm_log2(size) > 20) ? 15 : mm_log2(size) - 5;
        insert_node(&(free_list_array[index]), bp);
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
    // size를 받아서, 해당 size에 적합한 블록의 node 포인터를 반환함

    // first fit 버전
    // 가용 리스트 순회하면서, 이미 할당된 상태이면 패스, 가용 가능하고 크기가 인자 값 size보다 크거나 같으면 해당 블록의 시작 주소 반환

    int index = (mm_log2(size) > 20) ? 15 : mm_log2(size) - 5;

    while (index < 16) {
        freeListNode *currNode = free_list_array[index].head;

        while (currNode != NULL) {
            char *currPtr = (char *)currNode;
            if (GET_SIZE(HDRP(currPtr)) >= size) {
                return currNode;
            }
            currNode = currNode->next;
        }

        index ++;
    }

    return NULL;
}

static void place(freeListNode *node, size_t size) {
    // bp 노드 포인터를 받아서, 해당 bp 위치에 size만큼의 메모리를 할당함
    char *bp = (char *)node;
    size_t prev_size = GET_SIZE(HDRP(bp));

    int index = (mm_log2(prev_size) > 20) ? 15 : mm_log2(prev_size) - 5;

    if ((prev_size - size) >= (2*DSIZE)) {
        // bp로 시작하는 메모리 공간에 adjustedSize만큼 공간 할당
        delete_node(&(free_list_array[index]), bp);
        PUT(HDRP(bp), PACK(size, 1)); // head에 size, 1 할당
        PUT(FTRP(bp), PACK(size, 1)); // footer 초기화    

        bp = NEXT_BLKP(bp);

        // 빈 공간은 쪼갠 상태로 다시 표기
        PUT(HDRP(bp), PACK(prev_size - size, 0));
        PUT(FTRP(bp), PACK(prev_size - size, 0));
        coalesce(bp);
    } else {
        // free_list에서 삭제
        delete_node(&(free_list_array[index]), bp);

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
    
    for (int i=0; i<16; i++) {
        free_list_array[i].head = NULL;
        free_list_array[i].tail = NULL;
    }

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
    freeListNode *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        adjustedSize = 2*DSIZE; // 32B
    } else { 
        adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 16B의 배수로 올림
    }

    // 적절한 가용리스트를 찾음 (할당 정책은 find fit)
    bp = find_fit(adjustedSize);

    if (bp != NULL) {
        place(bp, adjustedSize);
        return (char *)bp;
    }

    // 적절한 가용 리스트를 못 찾으면 추가 메모리를 요청함
    extendedSize = MAX(adjustedSize, CHUNKSIZE);
    if ((bp = extend_heap(extendedSize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, adjustedSize);
    return (char *)bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */

void mm_free(void *bp)
{
    if (bp == NULL) {
        return ;
    }

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
    if (!ptr)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    char *oldptr = ptr;
    size_t oldSize = GET_SIZE(HDRP(oldptr)); // 전체 크기
    size_t asize = DSIZE * (((size) + (DSIZE) + (DSIZE-1)) / DSIZE); // 확장하려는 size를 16B의 배수로 올림 (페이로드 크기가 아니라, 블록 전체 크기가 됨)

    if (oldSize == asize) {
        return oldptr;
    }

    if (asize > oldSize) { // 확장하는 경우
        size_t nextSize = GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 다음 블록의 전체 크기
        size_t prevSize = GET_SIZE(FTRP(PREV_BLKP(oldptr))); // 이전 블록의 전체 크기

        if (!(GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))) && nextSize + oldSize >= asize) { // 뒤에 가용 블록이 있고, 뒤 가용 블록의 사이즈가 충분한 경우
            int index = (mm_log2(nextSize) > 20) ? 15 : mm_log2(nextSize) - 5;
            delete_node(&(free_list_array[index]), NEXT_BLKP(oldptr)); // 뒤의 가용 블록을 가용 리스트에서 제거

            size_t remainder_size = oldSize + nextSize - asize;

            if ((remainder_size) >= (2*DSIZE)) {
                PUT(HDRP(oldptr), PACK(asize, 1));
                PUT(FTRP(oldptr), PACK(asize, 1));

                char *remainder_ptr = NEXT_BLKP(oldptr);
                PUT(HDRP(remainder_ptr), PACK(remainder_size, 0));
                PUT(FTRP(remainder_ptr), PACK(remainder_size, 0));

                int rindex = (mm_log2(remainder_size) > 20) ? 15 : mm_log2(remainder_size) - 5;
                insert_node(&(free_list_array[rindex]), remainder_ptr);
            } else {
                PUT(HDRP(oldptr), PACK(oldSize + nextSize, 1));
                PUT(FTRP(oldptr), PACK(oldSize + nextSize, 1));
            }

            return oldptr;
        } else if (!(GET_ALLOC(FTRP(PREV_BLKP(oldptr)))) && prevSize + oldSize >= asize) { // 앞에 가용 블록이 있고, 앞 가용 블록의 사이즈가 충분한 경우
            int index = (mm_log2(prevSize) > 20) ? 15 : mm_log2(prevSize) - 5;
            delete_node(&(free_list_array[index]), PREV_BLKP(oldptr)); // 앞의 가용 블록을 가용 리스트에서 제거

            size_t remainder_size = oldSize + prevSize - asize; // 전체 크기
            char *newptr = PREV_BLKP(oldptr);

            memmove(newptr, oldptr, oldSize-DSIZE);

            if ((remainder_size) >= (2*DSIZE)) {
                PUT(HDRP(newptr), PACK(asize, 1));
                PUT(FTRP(newptr), PACK(asize, 1));

                char *remainder_ptr = NEXT_BLKP(newptr);
                PUT(HDRP(remainder_ptr), PACK(remainder_size, 0));
                PUT(FTRP(remainder_ptr), PACK(remainder_size, 0));

                int rindex = (mm_log2(remainder_size) > 20) ? 15 : mm_log2(remainder_size) - 5;
                insert_node(&(free_list_array[rindex]), remainder_ptr);
            } else {
                PUT(HDRP(newptr), PACK(oldSize + prevSize, 1));
                PUT(FTRP(newptr), PACK(oldSize + prevSize, 1));
            }

            return newptr;
        } else { // 앞 뒤 둘다 가용 블록이 없는 경우 
            void *newptr = mm_malloc(size); // malloc해서 새롭게 추가해야함
            if (!newptr) return NULL;

            memcpy(newptr, oldptr, oldSize-DSIZE);
            mm_free(oldptr);
            return newptr;
        }
    } else { // 축소하는 경우
        size_t remainder_size = oldSize - asize; // 전체 크기

        if ((remainder_size) >= (2*DSIZE)) { // 나머지 블록 쪼개서 쓰기
            PUT(HDRP(oldptr), PACK(asize, 1));
            PUT(FTRP(oldptr), PACK(asize, 1));

            char *remainder_ptr = NEXT_BLKP(oldptr);
            PUT(HDRP(remainder_ptr), PACK(remainder_size, 0));
            PUT(FTRP(remainder_ptr), PACK(remainder_size, 0));

            int rindex = (mm_log2(remainder_size) > 20) ? 15 : mm_log2(remainder_size) - 5;
            insert_node(&(free_list_array[rindex]), remainder_ptr);
        } 
        
        return oldptr;
    }
}

/*
같으면 그냥 반환
늘리는 경우 -> 기존 사이즈에서 해결 가능하면 그냥 반환 / 해결 불가능하면 해당 사이즈 가용 리스트에 접근해서 새로 malloc -> 기존 꺼 free
줄이는 경우 -> 해당 클래스 가용 리스트 안에서 할 수 있으면 그냥 반환 / 해결 불가능하면 해당 해당 사이즈 가용 리스트에 접근해서 새로 malloc -> 기존 꺼 free

*/

/*
32
64
.
.
.
1048576

(총 16개)
*/