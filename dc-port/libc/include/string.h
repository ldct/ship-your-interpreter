#ifndef DC_LIBC_STRING_H
#define DC_LIBC_STRING_H
#include <stddef.h>
void *memcpy(void *d, const void *s, size_t n);
void *memset(void *d, int c, size_t n);
void *memchr(const void *s, int c, size_t n);
char *strchr(const char *s, int c);
size_t strlen(const char *s);
char *strncpy(char *d, const char *s, size_t n);
#endif
