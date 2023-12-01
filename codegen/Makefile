LDFLAGS = -luv
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)


.PHONY: error_gen
error_gen:
	$(CC) $(LDFLAGS) -o error_gen error_gen.c
