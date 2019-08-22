CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  QArith_ext Dedekind Cauthy Iso Uncomputable MetricSpace

INCLUDE_DEMO = $(foreach d, $(DIRS), -Q $(CURRENT_DIR)/$(d) CReal.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -Q $(CURRENT_DIR) CReal
DEP_FLAG = $(DEP_DEMO)

QArith_ext_FILES = \
  QArith_base_ext.v INR_libs.v

Dedekind_FILES = \
  RBase.v ROrder.v RArith.v

Cauthy_FILES = \
  RBase.v

Iso_FILES = \
  Dedekind2Cauthy.v

MetricSpace_FILES = \
  MS_Def.v

Uncomputable_FILES = \
  Countable.v TMSet.v ComRealBase.v ComRealBase_Dec.v ComRealBase_TMR.v ComRealBaseuu.v ComRealBaseN_Q.v Rinv_Rpow.v

FILES = \
  $(QArith_ext_FILES:%.v=QArith_ext/%.v) \
  $(Dedekind_FILES:%.v=Dedekind/%.v) \
  $(Cauthy_FILES:%.v=Cauthy/%.v) \
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

