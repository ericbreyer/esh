#pragma once

struct ringBuffer;

struct ringBuffer * constructRingBuffer(int size);
void destroyRingBuffer(struct ringBuffer * buf);
void ringBuffer_print(struct ringBuffer * this);
void ringBuffer_insert(struct ringBuffer * this, char * val);
char * ringBuffer_get(struct ringBuffer * this, int offset);