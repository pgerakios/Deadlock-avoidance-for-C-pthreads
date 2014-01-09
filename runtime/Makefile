#echo | gcc -E -dM -
RTOBJ=runtime.o hash.o futex.o hashtable.o hashtable_itr.o
ALLOBJ=test.o $(RTOBJ)
TGT=test
LIBS= -lpthread 
ARCH=$(shell uname -m  | grep "i.*86" |sed 's/^/-march=/')
ARCH64_FLAG=$(shell uname -r | grep 64 | awk '{print "-D__LP64__"}')
DEBUG= -O2
#DEBUG=-Wall -g
#DEBUG_FLAG=-g -DDEBUG
#DEBUG_FLAG=-g
#DEBUG_FLAG=
RT_FLAGS=-D__FUTEX__
#RT_FLAGS=-D__YIELD__
#RT_FLAGS=-D__BUSY__
RT_PERF_COUNTERS=
#RT_PERF_COUNTERS=-D__PERF__COUNTERS__
RT_FUTEX_SPIN_COUNT=-D__FUTEX_SPIN_COUNT__=0
#RT_FUTEX_SPIN_COUNT=-D__FUTEX_SPIN_COUNT__=20
INC=-I/usr/local/lib/ocaml/caml/ -I/usr/lib/ocaml/caml/ -I/usr/lib/ocaml/3.10.2/caml/
CFLAGS= $(RT_FUTEX_SPIN_COUNT) \
	$(RT_PERF_COUNTERS) $(ARCH64_FLAG) $(ARCH) \
	$(RT_FLAGS) $(DEBUG_FLAG) $(DEBUG) \
	$(INC) -c 
#all: $(TGT)

all: $(RTOBJ) 

%.o:	%.c
	$(CC) $(CFLAGS) $< -o $@

$(TGT): $(ALLOBJ) 
	$(CC) $(ALLOBJ) -o $@ $(LIBS) 

clean:
	rm -f *.o

distclean: clean
	rm -f $(TGT)

link: $(RTOBJ) $(EXTOBJ)
	 $(CC) $(RTOBJ) $(EXTOBJ) -o $(EXEC)  $(EXTFLAGS) $(LIBS) $(LFLAGS)

print_debug_flag:	
	@echo "$(DEBUG_FLAG)"
