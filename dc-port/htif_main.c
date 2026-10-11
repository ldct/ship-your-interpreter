/* Bare-metal entry point for GNU dc 1.4.1 (bc 1.07.1) over HTIF.
 *
 * Equivalent to `dc -e PROGRAM` (dc/dc.c, `main`, case 'e', followed by
 * `return flush_okay()`), where PROGRAM is the NUL-terminated text in
 * `dc_script.text`. The buffer is preceded by a 16-byte magic so tools can
 * locate it in the ELF file and substitute another program without changing
 * the code image (scripts/dc/patch_elf.py). */
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dc.h"
#include "dc-proto.h"
#include "number.h"

#define DC_SCRIPT_MAX 8192

const char *progname;

struct dc_script {
	char magic[16];
	char text[DC_SCRIPT_MAX];
};

struct dc_script dc_script = {
	"@@DC-SCRIPT-v1@@",
	"[hello, world]p",
};

/* dc.c: flush_okay */
static int
flush_okay(void)
{
	int r = EXIT_SUCCESS;
	if (ferror(stdout) || fflush(stdout) || fclose(stdout))
		r = EXIT_FAILURE;
	return r;
}

int
main(void)
{
	dc_data string;

	progname = "dc";
	dc_math_init();
	dc_string_init();
	dc_register_init();
	dc_array_init();
	string = dc_makestring(dc_script.text, strlen(dc_script.text));
	if (dc_evalstr(&string) != DC_SUCCESS)
		return flush_okay();
	dc_free_str(&string.v.string);
	return flush_okay();
}
