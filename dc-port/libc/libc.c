/* A minimal C library for the bare-metal dc port.
 *
 * Only what GNU dc 1.4.1 (dc/*.c, lib/number.c) uses, written for
 * verification: no buffering, no locale, no reentrancy structures.
 *
 *  - Standard output goes to the HTIF console one byte per `tohost` store;
 *    standard error is discarded; standard input is at end of file.
 *  - `printf` conversions: %s, %c, %d, %ld, %u, %lu, %o and %#o (the only
 *    ones dc uses), no widths.
 *  - `malloc`: a 16-byte header holding the payload size (a multiple of 16)
 *    before each block; a first-fit free list (blocks are reused whole, never
 *    split or merged) and a bump pointer from `_end` to `__heap_end`;
 *    `NULL` when the heap is exhausted.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

/* ---------------------------------------------------------------- HTIF */

volatile uint64_t tohost __attribute__((section(".tohost"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost"), aligned(8)));

#define HTIF_DEV_CONSOLE (1ULL << 56)
#define HTIF_CMD_WRITE   (1ULL << 48)

void _exit(int code) __attribute__((noreturn));
void _exit(int code)
{
	tohost = ((uint64_t)(uint32_t)code << 1) | 1;
	for (;;) {}
}

void exit(int code) { _exit(code); }
void abort(void) { _exit(134); }
void __assert_fail(void) { _exit(134); }

/* ---------------------------------------------------------------- stdio */

static FILE files[3] = { {0}, {1}, {2} };
FILE *const stdin = &files[0];
FILE *const stdout = &files[1];
FILE *const stderr = &files[2];

int errno;

int fputc(int c, FILE *f)
{
	if (f->fd == 1)
		tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
	return (unsigned char)c;
}

int putchar(int c) { return fputc(c, stdout); }

size_t fwrite(const void *p, size_t size, size_t n, FILE *f)
{
	const unsigned char *s = p;
	size_t len = size * n;
	for (size_t i = 0; i < len; i++)
		fputc(s[i], f);
	return n;
}

int getc(FILE *f) { (void)f; return EOF; }
int ungetc(int c, FILE *f) { (void)f; return c; }
int fflush(FILE *f) { (void)f; return 0; }
int fclose(FILE *f) { (void)f; return 0; }
int ferror(FILE *f) { (void)f; return 0; }
int fileno(FILE *f) { return f->fd; }
int isatty(int fd) { return fd <= 2; }
void perror(const char *s) { (void)s; }
FILE *fopen(const char *path, const char *mode) { (void)path; (void)mode; return NULL; }
_sig_func_ptr signal(int sig, _sig_func_ptr f) { (void)sig; (void)f; return SIG_DFL; }

/* The formatter writes through a sink: a stream, or a bounded buffer. */
struct sink {
	FILE *f;		/* stream, or NULL for a buffer */
	char *buf;
	size_t size;	/* buffer capacity including the NUL */
	size_t len;		/* characters produced so far */
};

static void emit(struct sink *k, char c)
{
	if (k->f)
		fputc(c, k->f);
	else if (k->len + 1 < k->size)
		k->buf[k->len] = c;
	k->len++;
}

static void emit_unsigned(struct sink *k, unsigned long v, unsigned base)
{
	char d[24];
	int n = 0;
	do {
		d[n++] = "0123456789abcdef"[v % base];
		v /= base;
	} while (v);
	while (n)
		emit(k, d[--n]);
}

static int format(struct sink *k, const char *fmt, va_list ap)
{
	for (; *fmt; fmt++) {
		if (*fmt != '%') {
			emit(k, *fmt);
			continue;
		}
		fmt++;
		int alt = 0, lng = 0;
		if (*fmt == '#') { alt = 1; fmt++; }
		if (*fmt == 'l') { lng = 1; fmt++; }
		switch (*fmt) {
		case 's': {
			const char *s = va_arg(ap, const char *);
			while (*s)
				emit(k, *s++);
			break;
		}
		case 'c':
			emit(k, (char)va_arg(ap, int));
			break;
		case 'd': {
			long v = lng ? va_arg(ap, long) : va_arg(ap, int);
			unsigned long u = (unsigned long)v;
			if (v < 0) {
				emit(k, '-');
				u = -u;
			}
			emit_unsigned(k, u, 10);
			break;
		}
		case 'u':
			emit_unsigned(k, lng ? va_arg(ap, unsigned long) : va_arg(ap, unsigned), 10);
			break;
		case 'o': {
			unsigned long u = lng ? va_arg(ap, unsigned long) : va_arg(ap, unsigned);
			if (alt && u)
				emit(k, '0');
			emit_unsigned(k, u, 8);
			break;
		}
		case '%':
			emit(k, '%');
			break;
		default:
			return -1;
		}
	}
	return (int)k->len;
}

int vfprintf(FILE *f, const char *fmt, va_list ap)
{
	struct sink k = { f, NULL, 0, 0 };
	return format(&k, fmt, ap);
}

int fprintf(FILE *f, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	int r = vfprintf(f, fmt, ap);
	va_end(ap);
	return r;
}

int snprintf(char *buf, size_t n, const char *fmt, ...)
{
	struct sink k = { NULL, buf, n, 0 };
	va_list ap;
	va_start(ap, fmt);
	int r = format(&k, fmt, ap);
	va_end(ap);
	if (n)
		buf[k.len < n ? k.len : n - 1] = '\0';
	return r;
}

/* ---------------------------------------------------------------- stdlib */

char *getenv(const char *name) { (void)name; return NULL; }
int system(const char *cmd) { (void)cmd; return -1; }

long strtol(const char *s, char **end, int base)
{
	/* Only reached through getenv, which always fails. */
	(void)base;
	if (end)
		*end = (char *)s;
	return 0;
}

/* ---------------------------------------------------------------- string */

void *memcpy(void *d, const void *s, size_t n)
{
	unsigned char *dp = d;
	const unsigned char *sp = s;
	while (n--)
		*dp++ = *sp++;
	return d;
}

void *memset(void *d, int c, size_t n)
{
	unsigned char *dp = d;
	while (n--)
		*dp++ = (unsigned char)c;
	return d;
}

void *memchr(const void *s, int c, size_t n)
{
	const unsigned char *p = s;
	for (; n; n--, p++)
		if (*p == (unsigned char)c)
			return (void *)p;
	return NULL;
}

char *strchr(const char *s, int c)
{
	for (;; s++) {
		if (*s == (char)c)
			return (char *)s;
		if (!*s)
			return NULL;
	}
}

size_t strlen(const char *s)
{
	size_t n = 0;
	while (s[n])
		n++;
	return n;
}

char *strncpy(char *d, const char *s, size_t n)
{
	size_t i = 0;
	for (; i < n && s[i]; i++)
		d[i] = s[i];
	for (; i < n; i++)
		d[i] = '\0';
	return d;
}

/* ---------------------------------------------------------------- malloc */

extern char _end[];
extern char __heap_end[];

struct header {
	size_t size;			/* payload bytes, a multiple of 16 */
	struct header *next;	/* free-list link while free */
};

static char *brk_ptr;
static struct header *free_list;

void *malloc(size_t n)
{
	size_t size = (n + 15) & ~(size_t)15;
	if (size < n)
		return NULL;
	struct header **pp = &free_list;
	for (struct header *h = free_list; h; pp = &h->next, h = h->next) {
		if (h->size >= size) {
			*pp = h->next;
			return h + 1;
		}
	}
	if (!brk_ptr)
		brk_ptr = (char *)(((uintptr_t)_end + 15) & ~(uintptr_t)15);
	if ((size_t)(__heap_end - brk_ptr) < sizeof(struct header) + size)
		return NULL;
	struct header *h = (struct header *)brk_ptr;
	h->size = size;
	brk_ptr += sizeof(struct header) + size;
	return h + 1;
}

void free(void *p)
{
	if (!p)
		return;
	struct header *h = (struct header *)p - 1;
	h->next = free_list;
	free_list = h;
}

void *realloc(void *p, size_t n)
{
	if (!p)
		return malloc(n);
	struct header *h = (struct header *)p - 1;
	if (n <= h->size)
		return p;
	void *q = malloc(n);
	if (q) {
		memcpy(q, p, h->size);
		free(p);
	}
	return q;
}
