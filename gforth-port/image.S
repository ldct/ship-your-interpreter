/* The Gforth boot image, served to the loader by fopen (libc/gflibc.c). */
    .section .gf_image, "a"
    .balign 8
    .globl gf_image, gf_image_end
gf_image:
    .incbin GF_IMAGE
gf_image_end:
