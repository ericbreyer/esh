#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "ringBuffer.h"

struct ringBuffer
{
    int size;
    int insertPtr;
    char * buf[0];
};

struct ringBuffer * constructRingBuffer(int size) {
    struct ringBuffer * new = calloc(sizeof *new + (sizeof *new->buf * size), 1);
    new->size = size;
    new->insertPtr = 0;
    for(int i = 0; i < size; ++i) {
        new->buf[i] = malloc(2);
        strcpy(new->buf[i], " ");
    }
    return new;
}

void destroyRingBuffer(struct ringBuffer * buf) {
    free(buf);
}

void ringBuffer_print(struct ringBuffer * this) {
    printf("┌──────────┐\n");
    printf("│Size:%5d│\n", this->size);
    printf("├──────────┤\n");
    for(int i = 0; i < this->size; ++i) {
        printf("│%10s│", this->buf[i]);
        if(i== this->insertPtr) printf(" <-- next insert %d", this->insertPtr);
        printf("\n");
    }
    printf("└──────────┘\n");
}

void ringBuffer_insert(struct ringBuffer * this, char * val) {
    free(this->buf[this->insertPtr]);
    this->buf[this->insertPtr] = malloc(strlen(val));
    strcpy(this->buf[this->insertPtr], val);
    this->insertPtr = (this->insertPtr + 1) % this->size;
}

char * ringBuffer_get(struct ringBuffer * this, int offset) {
    int loc = (this->insertPtr - offset) % this->size;
    if (loc < 0) {
        loc += this->size;
    }
    return this->buf[loc];
}