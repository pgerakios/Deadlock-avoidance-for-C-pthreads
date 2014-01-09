#RELAY_DIR := $(PWD)/..
NULL_ALL := make
BINS := race_temp_anal.exe nullset_radar.exe nullset_race.exe
CLEANER = make clean
DUMPER = make
OUT_DIR := out
OLD_OUT := oldout
START_DIR = $(PWD)
RESULT := 

# what to test
SMALL_TESTS = wrong_count alias0
LARGE_TESTS = 

ALL_TESTS = $(SMALL_TESTS) $(LARGE_TESTS)


small: init $(SMALL_TESTS:%=$(OUT_DIR)/%.out) #diff_c
large: init $(LARGE_TESTS:%=$(OUT_DIR)/%.out)
all: init $(ALL_TESTS:%=$(OUT_DIR)/%.out)

# force diff_check to run
diff_c:
	@echo "=============================================="
	@echo "CHECKING DIFFS"
	$(RELAY_DIR)/scripts/diff_check.sh "\- unsafe \|\- safe\|Delta\|SUMS (\|Total Warnings" $(OUT_DIR)/ $(OLD_OUT)/ $(SMALL_TESTS)


#---------------------------------------------------
# Run the tests and make .out / .err logs


# force output directory to exist
init:
	@test -d $(OUT_DIR) || mkdir $(OUT_DIR)


# regenerate when the ciltrees change, or when the binaries change?
$(OUT_DIR)/%.out: %
	@echo "=============================================="
	@echo "Testing: " $(PWD)/$<; cd $< ; make > ../$@ ;	cd $(PWD)


# regenerate the ciltrees whenever the sources change
# TODO should also do that when the CIL binary is recompiled
%/ciltrees/calls.txt: %/*.c
	cd $(*); $(DUMPER)



#---------------------------------------------------
# Clean up individual test dirs (not the output dir)

.PHONY: clean

clean:
	@for dir in $(SMALL_TESTS); do \
	echo Cleaning $${dir}; \
	cd $${dir}; $(CLEANER); cd ..; \
	done
#	$(foreach dir,$(SMALL_TESTS),cd $(dir); $(CLEANER) > /dev/null ;cd ..;)
	rm -rf out

renew_small:
	$(foreach dir,$(SMALL_TESTS),cd $(dir); $(CLEANER); $(DUMPER);cd ..;)

renew_large:
	$(foreach dir,$(LARGE_TESTS),cd $(dir); $(CLEANER); $(DUMPER);cd ..;)

