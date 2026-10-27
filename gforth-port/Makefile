# Bare-metal RV64I build of Gforth 1.0 (indirect-threaded engine) over HTIF.
#
#   make GF_BUILD=/path/to/gforth-riscv64-build      build gforth-riscv-htif.elf
#
# GF_BUILD is a Gforth 1.0.0 tree configured with
# `./configure --host=riscv64-linux-gnu` after a native build, so that the
# vmgen output (engine/prim.i, prim_lab.i, ...), engine/config.h and
# kernl64l.fi exist (gforth-plan/g0/build_and_measure.sh does this).
#
# The Gforth sources are preprocessed against the riscv64 glibc headers
# (GF_CPP, without -O so that no glibc inline functions are used) and
# compiled freestanding for rv64i/lp64 (RISCV_CC), with the engine flags of
# Gforth's own Makefile, then linked with libc/ instead of glibc and with
# libgcc. Startup code and linker script are the dc port's.

GF_BUILD  ?= ../../gforth-build/brv
GF_ENGINE  = $(GF_BUILD)/engine
GF_IMAGE  ?= $(GF_BUILD)/kernl64l.fi
BUILD     ?= build

GF_CPP    ?= riscv64-linux-gnu-gcc
RISCV_CC  ?= riscv64-unknown-elf-gcc

GF_DEFS   := -DDEFAULTPATH='"."' -DINDIRECT_THREADED -DGFORTH_DEBUGGING \
             -D__thread=
GF_CPPFLAGS = -U_FORTIFY_SOURCE -Icompat -I$(GF_BUILD)/arch/riscv -I$(GF_ENGINE) $(GF_DEFS)

RISCV_CFLAGS := -O2 -march=rv64i -mabi=lp64 -mcmodel=medany -ffreestanding \
                -fno-builtin -fno-stack-protector -fno-tree-loop-distribute-patterns \
                -fomit-frame-pointer
# engine/Makefile's ENGINE_FLAGS for gcc
ENGINE_FLAGS := -fno-gcse -fcaller-saves -fno-defer-pop -fno-inline -fwrapv \
                -fno-strict-aliasing -fno-cse-follow-jumps -fno-reorder-blocks \
                -fno-reorder-blocks-and-partition -fno-toplevel-reorder \
                -falign-labels=1 -falign-loops=1 -falign-jumps=1 \
                -fno-delete-null-pointer-checks -fno-lto -fno-tree-slp-vectorize

GF_C := main support io signals dblsub getopt getopt1 wcwidth
GF_OBJ := $(BUILD)/engine.o $(addprefix $(BUILD)/,$(addsuffix .o,$(GF_C)))

gforth-riscv-htif.elf: $(GF_OBJ) htif_main.c libc/gflibc.c libc/setjmp.S image.S crt0.S link.ld
	$(RISCV_CC) $(RISCV_CFLAGS) -nostdlib -T link.ld -DGF_IMAGE='"$(GF_IMAGE)"' -o $@ \
	    crt0.S libc/gflibc.c libc/setjmp.S htif_main.c image.S $(GF_OBJ) -lgcc

# One hart, no threads: `-D__thread=` turns Gforth's thread-local variables
# (`PER_THREAD`, e.g. gforth_SPs) into ordinary globals, so nothing uses tp.

# The engine: as engine/Makefile's engine-itc rules (ENGINE=2, then the
# assembler pass with SKIP4 empty and the function renamed).
$(BUILD)/engine.i: $(GF_ENGINE)/engine.c | $(BUILD)
	$(GF_CPP) $(GF_CPPFLAGS) -DENGINE=2 -E $< -o $@
$(BUILD)/engine.S: $(BUILD)/engine.i
	$(RISCV_CC) $(RISCV_CFLAGS) $(ENGINE_FLAGS) -w -S $< -o $@
$(BUILD)/engine.o: $(BUILD)/engine.S
	$(RISCV_CC) -march=rv64i -mabi=lp64 -DSKIP4= -Dgforth_engine2=gforth_engine -c $< -o $@

$(BUILD)/%.i: $(GF_ENGINE)/%.c | $(BUILD)
	$(GF_CPP) $(GF_CPPFLAGS) -E $< -o $@
$(BUILD)/%.o: $(BUILD)/%.i
	$(RISCV_CC) $(RISCV_CFLAGS) -w -c $< -o $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD) gforth-riscv-htif.elf

.PHONY: clean
.PRECIOUS: $(BUILD)/%.i
