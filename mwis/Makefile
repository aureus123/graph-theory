
# Makefile for compiling the formalization of MWIS

COQC = coqc
COQFLAGS = -w -notation-overridden -no-glob

all: check_ir.vo prelim.vo mwis.vo mwis_prop.vo

check_ir.vo:
	$(COQC) $(COQFLAGS) check_ir.v

prelim.vo:
	$(COQC) $(COQFLAGS) prelim.v

mwis.vo: prelim.vo
	$(COQC) $(COQFLAGS) mwis.v

mwis_prop.vo: prelim.vo mwis.vo
	$(COQC) $(COQFLAGS) mwis_prop.v


.PHONY: clean

clean:
	rm -f *.vok *.vos *.vo

