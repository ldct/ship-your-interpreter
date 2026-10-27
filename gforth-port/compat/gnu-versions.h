/* Shadows glibc's <gnu-versions.h> so that Gforth's own engine/getopt.c and
 * getopt1.c are compiled instead of being elided in favour of glibc's
 * getopt, which this port does not link. */
#define _GNU_GETOPT_INTERFACE_VERSION 0
