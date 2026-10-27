/* Bare-metal entry point for Gforth 1.0 over HTIF.
 *
 * Equivalent to `gforth -i kernl64l.fi -e PROGRAM -e bye`, where PROGRAM is
 * the NUL-terminated text in `gf_script.text`. The buffer is preceded by a
 * 16-byte magic so tools can locate it in the ELF file and substitute another
 * program without changing the code image. */
#define GF_SCRIPT_MAX 8192

long gforth_main(int argc, char **argv, char **env);

struct gf_script {
	char magic[16];
	char text[GF_SCRIPT_MAX];
};

struct gf_script gf_script = {
	"@@GF-SCRIPT-v1@@",
	"2 3 + . cr",
};

int
main(void)
{
	static char *argv[] = {
		"gforth", "-i", "kernl64l.fi", "-e", gf_script.text, "-e", "bye", 0
	};
	static char *envp[] = { 0 };
	return (int)gforth_main(7, argv, envp);
}
