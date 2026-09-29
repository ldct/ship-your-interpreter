/* HTIF back end for newlib (from c/src/htif.c; stdout only).
 *
 * Implements the low-level syscalls in terms of the riscv-tests HTIF
 * (host-target interface) convention: a 64-bit `tohost` mailbox that the
 * host watches. Console output is device 1 / command 1, exit is device 0
 * with the low payload bit set. This is what Spike and the sail-riscv
 * emulators (including the Lean one) implement. There is no filesystem
 * and no console input; the script to run is linked into the image
 * (see src/script.S). */
#ifdef DC_HTIF

#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

/* The host locates these by the section name `.tohost` in the ELF. */
volatile uint64_t tohost __attribute__((section(".tohost"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost"), aligned(8)));

#define HTIF_DEV_CONSOLE (1ULL << 56)
#define HTIF_CMD_WRITE   (1ULL << 48)

/* Each 8-byte store is a complete HTIF command; the sail model processes
 * it synchronously and clears the mailbox, so no ready-polling is needed. */
static void htif_putc(char c) {
    tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
}

ssize_t _write(int fd, const void *buf, size_t len) {
    /* Only stdout reaches the HTIF console; stderr is discarded, so the
     * console is exactly what `dc -e` writes to standard output. */
    if (fd != 1) return (ssize_t)len;
    const char *p = buf;
    for (size_t i = 0; i < len; i++) htif_putc(p[i]);
    return (ssize_t)len;
}

ssize_t _read(int fd, void *buf, size_t len) {
    (void)fd; (void)buf; (void)len;
    return 0; /* EOF: no console input over HTIF */
}

int _open(const char *path, int flags, int mode) {
    (void)path; (void)flags; (void)mode;
    errno = ENOENT;
    return -1;
}

int _close(int fd) { (void)fd; return 0; }

off_t _lseek(int fd, off_t offset, int whence) {
    (void)fd; (void)offset; (void)whence;
    errno = ESPIPE;
    return -1;
}

int _fstat(int fd, struct stat *st) {
    memset(st, 0, sizeof *st);
    st->st_mode = (fd <= 2) ? S_IFCHR : S_IFREG;
    return 0;
}

int _isatty(int fd) { return fd <= 2; }

/* --- heap -------------------------------------------------------------- */

extern char _end[];       /* from link.ld */
extern char __heap_end[];

void *_sbrk(ptrdiff_t incr) {
    static char *brk;
    if (!brk) brk = _end;
    if (brk + incr > __heap_end) { errno = ENOMEM; return (void *)-1; }
    char *prev = brk;
    brk += incr;
    return prev;
}

/* --- process ----------------------------------------------------------- */

void _exit(int code) {
    tohost = ((uint64_t)(uint32_t)code << 1) | 1;
    for (;;) {}
}

int _kill(int pid, int sig) { (void)pid; (void)sig; errno = EINVAL; return -1; }
int _getpid(void) { return 1; }

#else
/* Non-HTIF build: nothing here. */
typedef int not_empty_translation_unit;
#endif

#ifdef DC_HTIF
/* `!` (shell escape) is outside the model; no command processor. */
int system(const char *cmd) { (void)cmd; return -1; }
#endif
