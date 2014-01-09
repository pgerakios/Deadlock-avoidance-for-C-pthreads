TARGETS := mutex mutex_mod fp_simple fp_simple_mod
LIBS=-lpthread
CFLAGS=-Wall -D_XOPEN_SOURCE=500 -D_GNU_SOURCE 
DEBUG=-debug

all: $(TARGETS)

%_mod: %.c
	cd ../../ && DEBUG=$(DEBUG) DIR=$(PWD) ./run.sh $(PWD)/$@ $(PWD)/$<

ciltrees: 
	$(DUMPER)

%: %.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS) 
	
.PHONY: clean
clean:
	rm -rf $(TARGETS)
	rm -f *.o
	rm -f *.*~
	rm -rf my.out
	rm -rf gcc-log.txt first_pass.txt stripped-log.txt
	rm -rf dot
	rm -rf ciltrees
	rm -rf tmp

