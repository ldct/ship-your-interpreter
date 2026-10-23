/* Minimal stdio for the bare-metal dc port (dc-port/libc/libc.c). */
#ifndef DC_LIBC_STDIO_H
#define DC_LIBC_STDIO_H
#include <stddef.h>
#include <stdarg.h>

#define EOF (-1)

typedef struct dc_file { int fd; } FILE;

extern FILE *const stdin;
extern FILE *const stdout;
extern FILE *const stderr;

int fputc(int c, FILE *f);
int putchar(int c);
size_t fwrite(const void *p, size_t size, size_t n, FILE *f);
int fprintf(FILE *f, const char *fmt, ...);
int vfprintf(FILE *f, const char *fmt, va_list ap);
int snprintf(char *buf, size_t n, const char *fmt, ...);
int getc(FILE *f);
int ungetc(int c, FILE *f);
int fflush(FILE *f);
int fclose(FILE *f);
int ferror(FILE *f);
int fileno(FILE *f);
void perror(const char *s);
FILE *fopen(const char *path, const char *mode);
#endif
