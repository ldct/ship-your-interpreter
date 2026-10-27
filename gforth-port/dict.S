/* The Gforth dictionary: the boot image, relocated for this address at
 * build time (scripts/gforth/gen_gf_image.py). The dictionary's free space
 * follows in .gf_dict_free (link.ld). */
    .section .gf_dict, "aw"
    .balign 8
    .globl gf_dict
gf_dict:
    .incbin GF_DICT
