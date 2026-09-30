#ifndef DC_LIBC_ASSERT_H
#define DC_LIBC_ASSERT_H
void __assert_fail(void) __attribute__((noreturn));
#define assert(e) ((e) ? (void)0 : __assert_fail())
#endif
