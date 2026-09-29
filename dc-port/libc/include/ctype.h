/* The C locale. */
#ifndef DC_LIBC_CTYPE_H
#define DC_LIBC_CTYPE_H
#define isdigit(c) ((unsigned)(c) - '0' < 10u)
#define isspace(c) ((c) == ' ' || (unsigned)(c) - '\t' < 5u)
#define isgraph(c) ((unsigned)(c) - 33u < 94u)
#endif
