#ifndef DC_LIBC_STDLIB_H
#define DC_LIBC_STDLIB_H
#include <stddef.h>
#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1
void *malloc(size_t n);
void free(void *p);
void *realloc(void *p, size_t n);
void exit(int code) __attribute__((noreturn));
void abort(void) __attribute__((noreturn));
char *getenv(const char *name);
long strtol(const char *s, char **end, int base);
int system(const char *cmd);
#endif
