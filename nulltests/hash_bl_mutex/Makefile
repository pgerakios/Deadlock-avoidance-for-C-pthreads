.PHONY: all clean

TARGETS := hash_test hash_test_mod
CC=gcc
CFLAGS=-Wall -lpthread -O2  -g  -D_GNU_SOURCE -I.
DEBUG=#-debug

all: $(TARGETS)

myhash.o: myhash.c myhash.h
	$(CC) $(CFLAGS) $< -c -o $@

hash_test.o: hash_test.c myhash.h
	$(CC) $(CFLAGS) $< -c -o $@

hash_test: hash_test.o myhash.o
	$(CC) $(CFLAGS) $^ -o $@

%_mod:
	@cd ../../ && DEBUG=$(DEBUG) DIR=$(PWD) ./run_dir.sh $(PWD)/$@ $(PWD)

clean: 
	rm -f *.o hash_test
	@rm -rf $(TARGETS) *.o *.*~ my.out
	@rm -rf gcc-log.txt first_pass.txt stripped-log.txt
	@rm -rf dot ciltrees tmp

