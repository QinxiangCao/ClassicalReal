CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  Dedekind Cauchy Iso Uncomputable MetricSpace

INCLUDE_DEMO = $(foreach d, $(DIRS), -Q $(CURRENT_DIR)/$(d) CReal.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -Q $(CURRENT_DIR) CReal
DEP_FLAG = $(DEP_DEMO)

Dedekind_FILES = \
  RBase.v ROrder.v RArith.v

Cauchy_FILES = \
  RBase.v RBase_uncomp.v

Iso_FILES = \
  Dedekind2Cauchy.v

MetricSpace_FILES = \
  MS_Def.v

Uncomputable_FILES = \
  ComRealBase.v

FILES = \
  $(Dedekind_FILES:%.v=Dedekind/%.v) \
  $(Cauchy_FILES:%.v=Cauchy/%.v) \
  $(Iso_FILES:%.v=Iso/%.v) \
  $(MetricSpace_FILES:%.v=MetricSpace/%.v) \
  $(Uncomputable_FILES:%.v=Uncomputable/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob

.DEFAULT_GOAL := all

include .depend

