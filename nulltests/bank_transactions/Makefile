TGT=boudol boudol-nd boudol_mod
LIBS=-lpthread
CFLAGS=-Wall -D_XOPEN_SOURCE=500 -D_GNU_SOURCE 
# -DVERBOSE
all: $(TGT) 

%_mod: %.c
	cd ../../ && DEBUG=$(DEBUG) DIR=$(PWD) ./run.sh $(PWD)/$@ $(PWD)/$<

ciltrees: 
	$(DUMPER)

%: %.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS)

clean:	
	$(RM) $(TGT)
	$(RM) OUTPUT.*
	$(RM) callgrind.out.*
