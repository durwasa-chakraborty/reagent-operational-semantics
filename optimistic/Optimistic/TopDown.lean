/-
  Top-down rebuild of the Ext proof, one invariant clause at a time.
  Paper side: `optimistic/top-down-prompt.org`.

  Assumed (taken as given, proved elsewhere):
    HistoryOf(τ, witness τ)   -- HistoryOf.lean, witness_h1 … witness_h5
    Int                       -- IntConsistency.lean, int_of_run
-/
import Optimistic.ExtConsistencyP

namespace Optimistic

open Reagent (ThreadMap)

-- Round 1: the invariant is P alone.
--   P(τ) = Ext_c(witness τ): every committed T reads, from outside itself,
--   the value of the last committed writer before it in finish order,
--   or the initial value if there is none.
def Inv₁ (τ : Trace) (_C : Config) : Prop := ExtP τ

-- (B) Inv → Ext_c: read it off.
theorem extC_of_inv₁ {τ : Trace} {C : Config} (h : Inv₁ τ C) : (witness τ).ExtC := h

-- (A) Run C₀ τ C → Inv₁(τ, C), by induction on the run.
theorem inv₁ {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (hrun : Run (initConfig E₀) τ C) : Inv₁ τ C := by
  refine Run.reverseRecOn (motive := fun τ C => Inv₁ τ C) ?_ ?_ hrun
  · -- base: P([]) is vacuous, the empty trace has no transactions
    intro T hT
    obtain ⟨t, ⟨e, he, -⟩, -⟩ := hT
    cases he
  · -- step: P(τ) ∧ C --a--> C'  →  P(τ·a)
    intro ls C ℓ C' hrun ih hstep
    have hrun' : Run (initConfig E₀) (ls ++ [ℓ]) C' := hrun.snoc hstep
    have hu := (inv_ids hrun').2
    cases hstep with
    | ctx _ hh =>
      cases hh with
      -- begin: nothing commits, finish order unchanged; needs the tag to be fresh
      | begin _ _          => exact ext_begin hu ih (inv_bbt hrun).1
      | getLog _ _ _       => sorry
      | getMem _ _ _ _     => sorry
      | setLog _ _ _       => sorry
      | setMem _ _ _ _     => sorry
      | commit _ _ _       => sorry
      | adm _              => sorry
    | kcasRetry _ _ _ _    => sorry
    | retry _ _ _          => sorry

end Optimistic
