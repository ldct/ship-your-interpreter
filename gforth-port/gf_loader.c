/* The port's image loader: replaces engine/main.c's gforth_loader (whose
 * definition in main.o is made weak by the Makefile).
 *
 * The image is relocated at build time (scripts/gforth/gen_gf_image.py) for
 * its address in the ELF (`.gf_dict`, followed by the rest of the dictionary
 * space as zero memory), so loading reduces to the loader's bookkeeping:
 * gforth_init, the primitive table, the cumulative group table that
 * gforth_relocate would have left, and the stack sizes. Compiled like
 * main.c (preprocessed against Gforth's headers). */
#include "forth.h"

int gforth_init(void);
void set_stack_sizes(ImageHeader *header);
int getpagesize(void);

extern Cell groups[32];
extern Cell npriminfos;
extern char gf_dict[];

ImageHeader *gforth_loader(char *imagename, char *path)
{
	ImageHeader *header = (ImageHeader *)gf_dict;
	int i;
	Cell sum = 0;

	(void)imagename;
	(void)path;
	if (gforth_init())
		return NULL;
	pagesize = getpagesize();
	vm_prims = gforth_engine(0 sr_call);
	for (npriminfos = 0; vm_prims[npriminfos] != 0; npriminfos++)
		;
	for (i = 0; i < 32; i++) {
		sum += groups[i];
		groups[i] = sum;
	}
	set_stack_sizes(header);
	return header;
}
