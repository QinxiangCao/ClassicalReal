CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  QArith_ext Dedekind Cauchy Iso Uncomputable MetricSpace Correctness

INCLUDE_DEMO = $(foreach d, $(DIRS), -Q $(CURRENT_DIR)/$(d) CReal.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -Q $(CURRENT_DIR) CReal
DEP_FLAG = $(DEP_DEMO)

QArith_ext_FILES = \
  QArith_base_ext.v INQ_libs.v Inject_lemmas.v

Dedekind_FILES = \
  RBase.v ROrder.v RArith.v

Cauchy_FILES = \
  RBase.v RArith.v RSign.v ROrder.v RAbs.v RFloor.v RFunc.v RComplete.v

Iso_FILES = \
  Dedekind2Cauchy.v Cauchy2Dedekind.v Bijection.v

MetricSpace_FILES = \
  M_pack.v M_pre.v M_def.v M_prop.v M_new.v M_base.v M_complete.v

Uncomputable_FILES = \
  Countable.v TMSet.v ComRealBase.v ComRealField.v ComRealBaseLemma1.v ComRealLemmas.v ComRealBase_Dec.v ComRealBase_TMR.v ComRealBaseuu.v ComRealBaseN_Q.v  SingleLemmas.v
Correctness_FILES =  \
  Cauchy_correct.v Dedekind_correct.v
  
FILES = \
  $(QArith_ext_FILES:%.v=QArith_ext/%.v) \
  $(Dedekind_FILES:%.v=Dedekind/%.v) \
  $(Cauchy_FILES:%.v=Cauchy/%.v) \
  $(Iso_FILES:%.v=Iso/%.v) \
  $(MetricSpace_FILES:%.v=MetricSpace/%.v) \
  $(Uncomputable_FILES:%.v=Uncomputable/%.v) \
  $(Correctness_FILES:%.v=Correctness/%.v)

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

