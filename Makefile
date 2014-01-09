

#--------------------------------------------------
# Important sub directories 

CIL := cil
CIL_OBJS := $(CIL)/obj/x86_LINUX
CIL_INCLUDE := -I $(CIL_OBJS)
DS_DIR := datastructs
PTA_DIR := pta
SRC := src
VPATH = $(DS_DIR) $(PTA_DIR) $(SRC)


#--------------------------------------------------
# Compiler consts

OCAMLC := $(shell if ocamlc.opt > /dev/null 2>&1; then echo 'ocamlc.opt'; else echo 'ocamlc'; fi)
OCAMLOPT := $(shell if ocamlopt.opt > /dev/null 2>&1; then echo 'ocamlopt.opt'; else echo 'ocamlopt'; fi)
OCAMLDEP := $(shell if ocamldep.opt > /dev/null 2>&1; then echo 'ocamldep.opt'; else echo 'ocamldep'; fi)
OCAMLDOC := $(shell if ocamldoc.opt > /dev/null 2>&1; then echo 'ocamldoc.opt'; else echo 'ocamldoc'; fi)

SUB_INCLUDES=$(addprefix -I , $(VPATH))

INCLUDES := $(CIL_INCLUDE) $(SUB_INCLUDES)
TO_LINK := -ccopt -L$(CIL_OBJS) 
OCAMLFLAGS := -thread $(INCLUDES) -g $(TO_LINK) \
	unix.cma str.cma threads.cma statfs_c.o 
OCAMLOPTFLAGS := -thread $(INCLUDES) -dtypes $(TO_LINK) \
	unix.cmxa str.cmxa threads.cmxa statfs_c.o -g
# add a -p to enable profiling for gprof

OPT_EXT:=.exe
BYTE_EXT:=.byte

#--------------------------------------------------
# Objs/targets

UTILS := gen_num strutil logging stdutil statfs mystats gc_stats \
	config gz_marshal scp inspect timeout size osize

CIL_EXTRAS := exit_funcs pp_visitor scope cilinfos cil_lvals offset \
	type_reach type_utils cast_hierarchy

DATA_STRUCTS := queueset stackset mapset prioqueuemap iset uf \
	intrange hashcons \
	simplehc distributions list_utils graph sparsebitv scc 

PTA := pta_types pta_compile pta_shared pta_cycle pta_offline_cycle \
	pta_fp_test pta_fi_eq pta_fb_eq pta_fs_dir 

BACKING_STORE := backed_summary inout_summary cache_sum

FCACHE := cache cilfiles filecache default_cache

MODSUMS := modsummaryi

NEW_SYMEX := symex_types symex_sum symex

SYMEX := symex_base $(NEW_SYMEX)

OO_PARTITION := addr_taken global_addr_taken faddr_taken oo_partition

FIELD_PARTITION := field_partition

CALLG := summary_keys callg scc_cg

ID_FIX_CG = $(UTILS) $(DATA_STRUCTS) $(FCACHE) fstructs \
	id_fixer $(CIL_EXTRAS) $(PTA) \
	alias_types alias $(CALLG) lvals dot_lib \
	$(OO_PARTITION) $(FIELD_PARTITION) dumpcalls \
	filter_dumpcalls fix_id_cg 

LOCK_STATS = simple_definitions simple_effect_tools \
						 simple_effect_construct simple_effect_dataflow \
						 simple_effect_checks simple_effect

SYMSTATE_BASE = $(UTILS) $(DATA_STRUCTS) $(FCACHE) fstructs \
	id_fixer $(CIL_EXTRAS) $(CALLG) $(BACKING_STORE) \
	$(PTA) alias_types alias lvals dumpcalls \
	threads entry_points 	$(MODSUMS) analysis_dep intraDataflow \
	$(SYMEX) definitions modsummary effect_tools \
	effect_checks effect_construct effect_dataflow \
	effect code_gen

SYMSTATE_STATS = $(SYMSTATE_BASE) $(LOCK_STATS) deadlock_stats

SYMSTATE = $(SYMSTATE_BASE) deadlock

BIN_TARGETS = fix_id_cg$(OPT_EXT) deadlock$(OPT_EXT) deadlock_stats$(OPT_EXT)


ALL_TARGETS = .depend $(BIN_TARGETS)

.PHONY: all clean htmldoc dot

all: .depend $(BIN_TARGETS)



#--------------------------------------------------------
# ML <-> C interface files (requires the C obj file also)

statfs.cmo: statfs.ml statfs_c.o
	$(OCAMLC) $(OCAMLFLAGS) -custom -c $<

statfs.cmx: statfs.ml statfs_c.o
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<


#--------------------------------------------------
# Fix ids + dump the call graph


ID_FIX_CG_OBJS = $(addsuffix .cmx, $(ID_FIX_CG))

fix_id_cg$(OPT_EXT): $(ID_FIX_CG_OBJS)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) \
	$(CIL_OBJS)/cil.cmxa $^

#--------------------------------------------------
# Test the symstate analysis

SYMSTATE_OBJS = $(addsuffix .cmx, $(SYMSTATE))

SYMSTATE_STATS_OBJS = $(addsuffix .cmx, $(SYMSTATE_STATS))

runtime/hash.o: runtime/hash.c
	$(MAKE) -C runtime

deadlock$(OPT_EXT): $(SYMSTATE_OBJS)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) \
	$(CIL_OBJS)/cil.cmxa $^ runtime/hash.o

deadlock_stats$(OPT_EXT): $(SYMSTATE_STATS_OBJS)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) \
	$(CIL_OBJS)/cil.cmxa $^ runtime/hash.o

#--------------------------------------------------
# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.c.o:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<


#--------------------------------------------------
# Clean up


clean:
	rm -f $(ALL_TARGETS)
	rm -f *.cm[iox]
	rm -f *.annot
	rm -f *.o
	rm -f *.*~
	rm -f out.* my.out gmon.out
	rm -f *.sh
	rm -rf gcc-log.txt first_pass.txt stripped-log.txt relay.log
	rm -rf dot ciltrees tmp
	$(foreach dir,$(VPATH), rm -f $(dir)/*.cm[iox])
	$(foreach dir,$(VPATH), rm -f $(dir)/*.o)
	$(foreach dir,$(VPATH), rm -f $(dir)/*.*~)
	$(foreach dir,$(VPATH), rm -f $(dir)/*.annot)

#--------------------------------------------------
# Dependencies

MLI_DEPENDS=$(addsuffix /*.mli,$(VPATH))
ML_DEPENDS=$(addsuffix /*.ml,$(VPATH))

.depend:
	$(OCAMLDEP) $(INCLUDES) \
	$(MLI_DEPENDS) $(ML_DEPENDS) \
	*.mli *.ml > .depend

include .depend

