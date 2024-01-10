TARGET = libuv-idris
TARGET_VERSION ?= 0.0.1

INSTALLDIR = ../lib

LDFLAGS = -luv
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
 LDFLAGS += -fuse-ld=gold
endif

all: $(TARGET)


SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)

$(TARGET): $(OBJS)
	$(CC) -shared $(LDFLAGS) -o $@ $^

.PHONY: clean

clean :
	rm -f $(OBJS) $(TARGET)
	rm -rf $(INSTALLDIR)

.PHONY: install

install:
	mkdir -p $(INSTALLDIR)
	install $(TARGET) $(wildcard *.h) $(INSTALLDIR)
	$(DYLIB_WORKAROUND)
