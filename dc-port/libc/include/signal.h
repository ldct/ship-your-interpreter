#ifndef DC_LIBC_SIGNAL_H
#define DC_LIBC_SIGNAL_H
typedef int sig_atomic_t;
typedef void (*_sig_func_ptr)(int);
#define SIG_DFL ((_sig_func_ptr)0)
#define SIG_IGN ((_sig_func_ptr)1)
#define SIGINT 2
_sig_func_ptr signal(int sig, _sig_func_ptr f);
#endif
