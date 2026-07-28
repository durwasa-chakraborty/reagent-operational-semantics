# Reagent operational semantics — build everything end to end.
#
#   make          # build the Lean mechanization (checks all proofs)
#   make proof    # same as `make`
#   make axioms   # print the axiom dependencies of the main theorems
#   make pdf      # typeset docs/reagent-correctness.pdf from its .tex source
#   make all      # proof + pdf
#   make clean    # remove Lean and LaTeX build artifacts

LAKE      ?= lake
LATEXMK   ?= latexmk
TEXDIR     = docs
TEXMAIN    = reagent-correctness

.PHONY: all proof axioms pdf clean

proof:
	$(LAKE) build

all: proof pdf

# Confirms the consistency theorems rest only on Lean's standard axioms
# (propext, Quot.sound) — no `sorry`, no `native_decide`.
axioms:
	@echo 'import Reagent' > /tmp/_reagent_axioms.lean
	@echo 'open Reagent' >> /tmp/_reagent_axioms.lean
	@echo '#print axioms int_sound' >> /tmp/_reagent_axioms.lean
	@echo '#print axioms ext_sound' >> /tmp/_reagent_axioms.lean
	@echo '#print axioms lcs_commit' >> /tmp/_reagent_axioms.lean
	@echo '#print axioms Trace.locate' >> /tmp/_reagent_axioms.lean
	$(LAKE) env lean /tmp/_reagent_axioms.lean

pdf:
	cd $(TEXDIR) && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(TEXMAIN).tex

clean:
	$(LAKE) clean || true
	cd $(TEXDIR) && $(LATEXMK) -C $(TEXMAIN).tex || true
