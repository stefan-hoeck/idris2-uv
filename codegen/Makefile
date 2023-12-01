LDFLAGS = -luv
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
 LDFLAGS += -fuse-ld=gold
endif


.PHONY: error_gen
error_gen:
	$(CC) $(LDFLAGS) -o error_gen error_gen.c
