/* A minimal C library for the bare-metal Gforth 1.0 port.
 *
 * The Gforth sources are preprocessed against the riscv64 glibc headers (so
 * they see glibc's declarations and ABI) and linked against this file
 * instead of glibc. It follows dc-port/libc/libc.c: the HTIF console, the
 * formatter and the allocator are the same code, so their dc specs carry
 * over; everything Gforth needs beyond dc is added below.
 *
 *  - Standard output goes to the HTIF console one byte per `tohost` store;
 *    standard error is discarded; standard input is at end of file.
 *  - No terminal (`isatty` is 0), no environment, no files except the
 *    boot image, which `fopen` serves read-only from memory (`gf_image`).
 *  - `mmap` (anonymous only) hands out fresh, never reused memory from the
 *    same bump pointer as `malloc`; fresh RAM is zero, so it needs no clearing.
 *  - Floating point, libm, dynamic loading, processes and directories are
 *    excluded from the verified subset: their entry points stop the machine
 *    with status 134 or report failure.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>

#define EOF (-1)
#define NULL_FILE ((FILE *)0)

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

/* Excluded from the verified subset (floating point, libm, dynamic
 * loading): reaching one of these stops the machine with status 134. */
#define UNSUPPORTED(name) void name(void) { _exit(134); }
UNSUPPORTED(acos) UNSUPPORTED(acosh) UNSUPPORTED(asin) UNSUPPORTED(asinh)
UNSUPPORTED(atan) UNSUPPORTED(atan2) UNSUPPORTED(atanh) UNSUPPORTED(cos)
UNSUPPORTED(cosh) UNSUPPORTED(exp) UNSUPPORTED(exp10) UNSUPPORTED(expm1)
UNSUPPORTED(fabs) UNSUPPORTED(floor) UNSUPPORTED(ldexp) UNSUPPORTED(log)
UNSUPPORTED(log10) UNSUPPORTED(log1p) UNSUPPORTED(pow) UNSUPPORTED(rint)
UNSUPPORTED(sin) UNSUPPORTED(sincos) UNSUPPORTED(sinh) UNSUPPORTED(sqrt)
UNSUPPORTED(tan) UNSUPPORTED(tanh) UNSUPPORTED(strtod)

/* ---------------------------------------------------------------- errno */

int errno;
int *__errno_location(void) { return &errno; }

/* ---------------------------------------------------------------- stdio */

typedef struct gf_file {
	int fd;
	const unsigned char *data;	/* read-only contents, or NULL */
	size_t size, pos;
	int eof;
} FILE;

static FILE files[4] = { {0}, {1}, {2}, {3} };
FILE *const stdin = &files[0];
FILE *const stdout = &files[1];
FILE *const stderr = &files[2];

int fputc(int c, FILE *f)
{
#ifdef GF_DEBUG_STDERR
	if (f->fd == 2)
		f = stdout;
#endif
	if (f->fd == 1)
		tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
	return (unsigned char)c;
}

int putchar(int c) { return fputc(c, stdout); }
int putc(int c, FILE *f) { return fputc(c, f); }

size_t fwrite(const void *p, size_t size, size_t n, FILE *f)
{
	const unsigned char *s = p;
	size_t len = size * n;
	for (size_t i = 0; i < len; i++)
		fputc(s[i], f);
	return n;
}

int fputs(const char *s, FILE *f)
{
	while (*s)
		fputc(*s++, f);
	return 0;
}

int ungetc(int c, FILE *f) { (void)f; return c; }
int fflush(FILE *f) { (void)f; return 0; }
int ferror(FILE *f) { (void)f; return 0; }
void clearerr(FILE *f) { f->eof = 0; }
int feof(FILE *f) { return f->eof; }
int fileno(FILE *f) { return f->fd; }
int isatty(int fd) { (void)fd; return 0; }
void perror(const char *s) { (void)s; }
int setvbuf(FILE *f, char *buf, int mode, size_t size)
{ (void)f; (void)buf; (void)mode; (void)size; return 0; }
void flockfile(FILE *f) { (void)f; }
void funlockfile(FILE *f) { (void)f; }
FILE *fdopen(int fd, const char *mode) { (void)fd; (void)mode; return NULL_FILE; }
FILE *popen(const char *cmd, const char *mode) { (void)cmd; (void)mode; return NULL_FILE; }
int pclose(FILE *f) { (void)f; return -1; }

/* The boot image, linked in by image.S. */
extern const unsigned char gf_image[], gf_image_end[];
#define GF_IMAGE_NAME "kernl64l.fi"

static int ends_with(const char *s, const char *suffix)
{
	size_t n = 0, m = 0;
	while (s[n])
		n++;
	while (suffix[m])
		m++;
	if (m > n)
		return 0;
	for (size_t i = 0; i < m; i++)
		if (s[n - m + i] != suffix[i])
			return 0;
	return n == m || s[n - m - 1] == '/';
}

FILE *fopen(const char *path, const char *mode)
{
	if (mode[0] != 'r' || !ends_with(path, GF_IMAGE_NAME))
		return NULL_FILE;
	FILE *f = &files[3];
	f->data = gf_image;
	f->size = (size_t)(gf_image_end - gf_image);
	f->pos = 0;
	f->eof = 0;
	return f;
}

int fclose(FILE *f) { (void)f; return 0; }

size_t fread(void *p, size_t size, size_t n, FILE *f)
{
	unsigned char *d = p;
	if (!f->data || size == 0) {
		f->eof = 1;
		return 0;
	}
	size_t want = size * n, got = 0;
	while (got < want && f->pos < f->size)
		d[got++] = f->data[f->pos++];
	if (got < want)
		f->eof = 1;
	return got / size;
}

int fgetc(FILE *f)
{
	if (!f->data || f->pos >= f->size) {
		f->eof = 1;
		return EOF;
	}
	return f->data[f->pos++];
}

int getc(FILE *f) { return fgetc(f); }
int getc_unlocked(FILE *f) { return fgetc(f); }

int fseeko(FILE *f, long off, int whence)
{
	long base = whence == 0 ? 0 : whence == 1 ? (long)f->pos : (long)f->size;
	if (!f->data || base + off < 0)
		return -1;
	f->pos = (size_t)(base + off);
	f->eof = 0;
	return 0;
}

int fseek(FILE *f, long off, int whence) { return fseeko(f, off, whence); }
long ftello(FILE *f) { return f->data ? (long)f->pos : -1; }
void rewind(FILE *f) { fseeko(f, 0, 0); }

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

int printf(const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	int r = vfprintf(stdout, fmt, ap);
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
int setenv(const char *n, const char *v, int o) { (void)n; (void)v; (void)o; return -1; }
int system(const char *cmd) { (void)cmd; return -1; }
char *setlocale(int cat, const char *loc) { (void)cat; (void)loc; return "C"; }

static int digit_value(char c)
{
	if (c >= '0' && c <= '9') return c - '0';
	if (c >= 'a' && c <= 'z') return c - 'a' + 10;
	if (c >= 'A' && c <= 'Z') return c - 'A' + 10;
	return 99;
}

unsigned long __isoc23_strtoul(const char *s, char **end, int base)
{
	unsigned long v = 0;
	while (*s == ' ' || *s == '\t')
		s++;
	if (base == 0)
		base = 10;
	for (int d; (d = digit_value(*s)) < base; s++)
		v = v * base + d;
	if (end)
		*end = (char *)s;
	return v;
}

long __isoc23_strtol(const char *s, char **end, int base)
{
	while (*s == ' ' || *s == '\t')
		s++;
	if (*s == '-')
		return -(long)__isoc23_strtoul(s + 1, end, base);
	return (long)__isoc23_strtoul(s, end, base);
}

int atoi(const char *s) { return (int)__isoc23_strtol(s, NULL, 10); }

/* ---------------------------------------------------------------- ctype */

/* glibc's table: indexable from -128 to 255; the bit values are glibc's
 * little-endian _ISupper ... _ISalnum. */
enum {
	C_UPPER = 0x100, C_LOWER = 0x200, C_ALPHA = 0x400, C_DIGIT = 0x800,
	C_XDIGIT = 0x1000, C_SPACE = 0x2000, C_PRINT = 0x4000, C_GRAPH = 0x8000,
	C_BLANK = 0x1, C_CNTRL = 0x2, C_PUNCT = 0x4, C_ALNUM = 0x8,
};

static unsigned short ctype_table[384];
static const unsigned short *ctype_ptr;

const unsigned short **__ctype_b_loc(void)
{
	if (!ctype_ptr) {
		for (int c = 0; c < 128; c++) {
			unsigned short b = 0;
			int up = c >= 'A' && c <= 'Z', lo = c >= 'a' && c <= 'z';
			int dg = c >= '0' && c <= '9';
			if (up) b |= C_UPPER;
			if (lo) b |= C_LOWER;
			if (up || lo) b |= C_ALPHA | C_ALNUM;
			if (dg) b |= C_DIGIT | C_ALNUM | C_XDIGIT;
			if ((c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) b |= C_XDIGIT;
			if (c == ' ' || (c >= 9 && c <= 13)) b |= C_SPACE;
			if (c == ' ' || c == '\t') b |= C_BLANK;
			if (c < 32 || c == 127) b |= C_CNTRL;
			if (c >= 32 && c < 127) b |= C_PRINT;
			if (c > 32 && c < 127) b |= C_GRAPH;
			if (c > 32 && c < 127 && !up && !lo && !dg) b |= C_PUNCT;
			ctype_table[128 + c] = b;
		}
		ctype_ptr = ctype_table + 128;
	}
	return &ctype_ptr;
}

int toupper(int c) { return c >= 'a' && c <= 'z' ? c - 'a' + 'A' : c; }

/* ---------------------------------------------------------------- string */

void *memcpy(void *d, const void *s, size_t n)
{
	unsigned char *dp = d;
	const unsigned char *sp = s;
	while (n--)
		*dp++ = *sp++;
	return d;
}

/* memmove and memset move whole 8-byte words where the alignment allows:
 * the kernel image's boot moves and clears ~300 KB (`move`, `erase`), and
 * the loader copies the 455 KB image, which byte loops make the bulk of
 * every run. memcpy stays dc's byte loop (its spec carries over). */
void *memmove(void *d, const void *s, size_t n)
{
	unsigned char *dp = d;
	const unsigned char *sp = s;
	int words = (((uintptr_t)dp ^ (uintptr_t)sp) & 7) == 0;
	if (dp <= sp) {
		if (words) {
			while (n && ((uintptr_t)dp & 7)) {
				*dp++ = *sp++;
				n--;
			}
			for (; n >= 8; n -= 8, dp += 8, sp += 8)
				*(uint64_t *)dp = *(const uint64_t *)sp;
		}
		while (n--)
			*dp++ = *sp++;
	} else {
		if (words) {
			while (n && ((uintptr_t)(dp + n) & 7)) {
				n--;
				dp[n] = sp[n];
			}
			for (; n >= 8; n -= 8)
				*(uint64_t *)(dp + n - 8) = *(const uint64_t *)(sp + n - 8);
		}
		while (n--)
			dp[n] = sp[n];
	}
	return d;
}

void *memset(void *d, int c, size_t n)
{
	unsigned char *dp = d;
	uint64_t w = (unsigned char)c * 0x0101010101010101ULL;
	while (n && ((uintptr_t)dp & 7)) {
		*dp++ = (unsigned char)c;
		n--;
	}
	for (; n >= 8; n -= 8, dp += 8)
		*(uint64_t *)dp = w;
	while (n--)
		*dp++ = (unsigned char)c;
	return d;
}

int memcmp(const void *a, const void *b, size_t n)
{
	const unsigned char *p = a, *q = b;
	for (; n; n--, p++, q++)
		if (*p != *q)
			return *p - *q;
	return 0;
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

char *strrchr(const char *s, int c)
{
	const char *r = NULL;
	for (;; s++) {
		if (*s == (char)c)
			r = s;
		if (!*s)
			return (char *)r;
	}
}

size_t strlen(const char *s)
{
	size_t n = 0;
	while (s[n])
		n++;
	return n;
}

int strcmp(const char *a, const char *b)
{
	while (*a && *a == *b)
		a++, b++;
	return (unsigned char)*a - (unsigned char)*b;
}

int strncmp(const char *a, const char *b, size_t n)
{
	for (; n; n--, a++, b++) {
		if (*a != *b)
			return (unsigned char)*a - (unsigned char)*b;
		if (!*a)
			return 0;
	}
	return 0;
}

char *strcpy(char *d, const char *s)
{
	char *r = d;
	while ((*d++ = *s++))
		;
	return r;
}

char *strerror(int e) { (void)e; return "error"; }
const char *strerrordesc_np(int e) { (void)e; return "error"; }
char *strsignal(int s) { (void)s; return "signal"; }

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

void *calloc(size_t n, size_t size)
{
	size_t len = n * size;
	if (size && len / size != n)
		return NULL;
	void *p = malloc(len);
	if (p)
		memset(p, 0, len);
	return p;
}

int mcheck(void (*f)(int)) { (void)f; return 0; }
int mprobe(void *p) { (void)p; return 0; }

/* Anonymous mappings: page-aligned fresh memory from the bump pointer,
 * never returned. Fresh RAM is zero, as an anonymous mapping must be. */
#define MAP_FIXED 0x10
#define MAP_ANONYMOUS 0x20
#define MAP_FAILED ((void *)-1)
#define PAGE 4096

void *mmap(void *addr, size_t len, int prot, int flags, int fd, long off)
{
	(void)prot;
	if (flags & MAP_FIXED) {
		/* The loader maps the image file over memory it has just
		 * allocated (`dict_alloc_read`): copy the file's bytes. */
		FILE *f = &files[3];
		if (fd != f->fd || !f->data || off < 0 || (size_t)off > f->size)
			return MAP_FAILED;
		size_t n = f->size - (size_t)off;
		memmove(addr, f->data + off, n < len ? n : len);
		return addr;
	}
	if (!(flags & MAP_ANONYMOUS) || fd != -1)
		return MAP_FAILED;
	if (!brk_ptr)
		brk_ptr = (char *)(((uintptr_t)_end + 15) & ~(uintptr_t)15);
	char *p = (char *)(((uintptr_t)brk_ptr + PAGE - 1) & ~(uintptr_t)(PAGE - 1));
	len = (len + PAGE - 1) & ~(size_t)(PAGE - 1);
	if (p > __heap_end || (size_t)(__heap_end - p) < len)
		return MAP_FAILED;
	brk_ptr = p + len;
	return p;
}

int munmap(void *addr, size_t len) { (void)addr; (void)len; return 0; }
int mprotect(void *addr, size_t len, int prot) { (void)addr; (void)len; (void)prot; return 0; }
int getpagesize(void) { return PAGE; }
long sysconf(int name) { return name == 30 /* _SC_PAGESIZE */ ? PAGE : -1; }

/* ---------------------------------------------------------------- atomics */

/* One hart, no interrupts: plain loads and stores are atomic. */
uint64_t __atomic_fetch_add_8(volatile void *p, uint64_t v, int m)
{
	(void)m;
	volatile uint64_t *q = p;
	uint64_t old = *q;
	*q = old + v;
	return old;
}

uint64_t __atomic_exchange_8(volatile void *p, uint64_t v, int m)
{
	(void)m;
	volatile uint64_t *q = p;
	uint64_t old = *q;
	*q = v;
	return old;
}

_Bool __atomic_compare_exchange_8(volatile void *p, void *expected, uint64_t v,
				  _Bool weak, int sm, int fm)
{
	(void)weak; (void)sm; (void)fm;
	volatile uint64_t *q = p;
	uint64_t *e = expected;
	if (*q == *e) {
		*q = v;
		return 1;
	}
	*e = *q;
	return 0;
}

int pthread_mutex_lock(void *m) { (void)m; return 0; }
int pthread_mutex_unlock(void *m) { (void)m; return 0; }

/* ---------------------------------------------------------------- OS */

/* Signals: never delivered. */
int sigaction(int s, const void *a, void *o) { (void)s; (void)a; (void)o; return 0; }
int sigemptyset(void *set) { (void)set; return 0; }
int sigaddset(void *set, int s) { (void)set; (void)s; return 0; }
int sigprocmask(int h, const void *s, void *o) { (void)h; (void)s; (void)o; return 0; }
int sigaltstack(const void *s, void *o) { (void)s; (void)o; return 0; }

/* Time: the clock stands at zero. */
int clock_gettime(int clk, void *ts)
{
	(void)clk;
	memset(ts, 0, 16);
	return 0;
}

int gettimeofday(void *tv, void *tz)
{
	(void)tz;
	memset(tv, 0, 16);
	return 0;
}

int getrusage(int who, void *ru) { (void)who; memset(ru, 0, 144); return 0; }
int nanosleep(const void *req, void *rem) { (void)req; (void)rem; return 0; }

void *localtime_r(const long *t, void *tm)
{
	(void)t;
	memset(tm, 0, 56);
	((int *)tm)[3] = 1;	/* tm_mday */
	((int *)tm)[5] = 70;	/* tm_year */
	return tm;
}

/* No files, directories, terminal, processes or dynamic libraries. */
int open(const char *p, int fl, ...) { (void)p; (void)fl; errno = 2; return -1; }
int access(const char *p, int m) { (void)p; (void)m; errno = 2; return -1; }
int fstat(int fd, void *st) { (void)fd; (void)st; errno = 9; return -1; }
int ftruncate(int fd, long len) { (void)fd; (void)len; errno = 9; return -1; }
int chdir(const char *p) { (void)p; errno = 2; return -1; }
int mkdir(const char *p, int m) { (void)p; (void)m; errno = 30; return -1; }
int rename(const char *a, const char *b) { (void)a; (void)b; errno = 30; return -1; }
int unlink(const char *p) { (void)p; errno = 30; return -1; }
char *getcwd(char *buf, size_t n) { (void)buf; (void)n; errno = 2; return NULL; }
void *opendir(const char *p) { (void)p; errno = 2; return NULL; }
void *readdir(void *d) { (void)d; return NULL; }
int closedir(void *d) { (void)d; return 0; }
void *getpwnam(const char *n) { (void)n; return NULL; }
int getpgrp(void) { return 1; }
int tcgetpgrp(int fd) { (void)fd; errno = 25; return -1; }
int tcgetattr(int fd, void *t) { (void)fd; (void)t; errno = 25; return -1; }
int tcsetattr(int fd, int a, const void *t) { (void)fd; (void)a; (void)t; errno = 25; return -1; }
int tcflow(int fd, int a) { (void)fd; (void)a; errno = 25; return -1; }
int ioctl(int fd, unsigned long r, ...) { (void)fd; (void)r; errno = 25; return -1; }
int pselect(int n, void *r, void *w, void *e, const void *t, const void *s)
{ (void)n; (void)r; (void)w; (void)e; (void)t; (void)s; return 0; }
void *dlopen(const char *f, int fl) { (void)f; (void)fl; return NULL; }
void *dlsym(void *h, const char *s) { (void)h; (void)s; return NULL; }
int dlclose(void *h) { (void)h; return 0; }
char *dlerror(void) { return "no dynamic libraries"; }
int fnmatch(const char *p, const char *s, int fl) { (void)p; (void)s; (void)fl; return 1; }
