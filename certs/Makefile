
# Makefile for checking the instances

COQC = time -p coqc
COQFLAGS = -R ../mwis "" -w -notation-overridden -no-glob


all: easy hard weighted

easy:
	$(COQC) $(COQFLAGS) myciel3.v
	$(COQC) $(COQFLAGS) myciel4.v
	$(COQC) $(COQFLAGS) queen5_5.v
	$(COQC) $(COQFLAGS) _1_FullIns_3.v
	$(COQC) $(COQFLAGS) queen6_6.v
	$(COQC) $(COQFLAGS) _2_Insertions_3.v
	$(COQC) $(COQFLAGS) myciel5.v
	$(COQC) $(COQFLAGS) queen7_7.v
	$(COQC) $(COQFLAGS) _2_FullIns_3.v
	$(COQC) $(COQFLAGS) _3_Insertions_3.v
	$(COQC) $(COQFLAGS) queen8_8.v
	$(COQC) $(COQFLAGS) _1_Insertions_4.v
	$(COQC) $(COQFLAGS) huck.v

hard:
	$(COQC) $(COQFLAGS) _4_Insertions_3.v
	$(COQC) $(COQFLAGS) _3_FullIns_3.v
	$(COQC) $(COQFLAGS) jean.v
	$(COQC) $(COQFLAGS) queen9_9.v
	$(COQC) $(COQFLAGS) david.v
	$(COQC) $(COQFLAGS) mug88_1.v
	$(COQC) $(COQFLAGS) mug88_25.v
	$(COQC) $(COQFLAGS) _1_FullIns_4.v
	$(COQC) $(COQFLAGS) myciel6.v
	$(COQC) $(COQFLAGS) queen8_12.v
	$(COQC) $(COQFLAGS) mug100_1.v
	$(COQC) $(COQFLAGS) mug100_25.v
	$(COQC) $(COQFLAGS) queen10_10.v

weighted:
	$(COQC) $(COQFLAGS) buenosaires.v


.PHONY: clean

clean:
	rm -f *.vok *.vos *.vo

