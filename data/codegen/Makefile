LDFLAGS = -luv
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
endif

all: error_gen run_mode_gen size_gen dns_gen file_gen sig_gen

.PHONY: sig_gen
sig_gen:
	$(CC) -o sig_gen sig_gen.c $(LDFLAGS)

.PHONY: file_gen
file_gen:
	$(CC) -o file_gen file_gen.c $(LDFLAGS)

.PHONY: dns_gen
dns_gen:
	$(CC) -o dns_gen dns_gen.c $(LDFLAGS)

.PHONY: error_gen
error_gen:
	$(CC) -o error_gen error_gen.c $(LDFLAGS)

.PHONY: size_gen
size_gen:
	$(CC) -o size_gen size_gen.c $(LDFLAGS)

.PHONY: run_mode_gen
run_mode_gen:
	$(CC) -o run_mode_gen run_mode_gen.c $(LDFLAGS)
