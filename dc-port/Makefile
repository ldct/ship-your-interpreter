# Bare-metal RV64I build of GNU dc 1.4.1 (GNU bc 1.07.1) over HTIF.
#
#   make RISCV_CC=/path/to/riscv-none-elf-gcc     build dc-riscv-htif.elf
#
# Uses the toolchain of c/while-riscv-htif.elf (xPack GNU RISC-V Embedded
# GCC 15.2.0, newlib) and the same startup code, linker script and flags.
# The upstream source is downloaded and checked against its SHA-256.

BC_VERSION := 1.07.1
BC_URL     := https://ftp.gnu.org/gnu/bc/bc-$(BC_VERSION).tar.gz
BC_SHA256  := 62adfca89b0a1c0164c2cdca59ca210c1d44c3ffc46daf9931cf4942664cb02a
BUILD      ?= build

RISCV_CC     ?= riscv-none-elf-gcc
RISCV_CFLAGS := -std=gnu11 -O2 -march=rv64i -mabi=lp64 -mcmodel=medany -DDC_HTIF

DC_SRC := eval.c misc.c numeric.c stack.c string.c array.c

dc-riscv-htif.elf: htif_main.c htif.c crt0.S link.ld $(BUILD)/bc/config.h
	$(RISCV_CC) $(RISCV_CFLAGS) -I$(BUILD)/bc -I$(BUILD)/bc/h -I$(BUILD)/bc/dc \
	    -nostartfiles -T link.ld -o $@ crt0.S htif.c htif_main.c \
	    $(addprefix $(BUILD)/bc/dc/,$(DC_SRC)) $(BUILD)/bc/lib/number.c

$(BUILD)/bc/config.h:
	mkdir -p $(BUILD)
	curl -sSfL $(BC_URL) -o $(BUILD)/bc.tar.gz
	echo "$(BC_SHA256)  $(BUILD)/bc.tar.gz" | sha256sum -c -
	tar xzf $(BUILD)/bc.tar.gz -C $(BUILD)
	rm -rf $(BUILD)/bc && mv $(BUILD)/bc-$(BC_VERSION) $(BUILD)/bc
	cd $(BUILD)/bc && ./configure --host=riscv-none-elf CC=$(RISCV_CC) \
	    CFLAGS="$(RISCV_CFLAGS)" > configure.log

clean:
	rm -rf $(BUILD)

.PHONY: clean
