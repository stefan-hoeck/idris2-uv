LDFLAGS = -luv
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
 LDFLAGS += -fuse-ld=gold
endif

all: error_gen run_mode_gen size_gen dns_gen

.PHONY: dns_gen
dns_gen:
	$(CC) $(LDFLAGS) -o dns_gen dns_gen.c

.PHONY: error_gen
error_gen:
	$(CC) $(LDFLAGS) -o error_gen error_gen.c

.PHONY: size_gen
size_gen:
	$(CC) $(LDFLAGS) -o size_gen size_gen.c

.PHONY: run_mode_gen
run_mode_gen:
	$(CC) $(LDFLAGS) -o run_mode_gen run_mode_gen.c
