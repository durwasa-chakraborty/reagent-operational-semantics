import Optimistic.TopDown

namespace Optimistic

open Reagent (ThreadMap TxId)

/-! ## Statement -/

-- Ext for the optimistic track: part (a) `Ext_c` for committed readers
-- (VIS = AR), part (b) `Ext_u` for retried/pending readers (per-operation VIS).
def History.Ext (H : History) (τ : Trace) : Prop :=
  H.ExtC ∧ H.ExtU (visOf (events τ))

-- Every event of `t` comes before (or is) `t`'s terminator.
-- Lemma N: once `t` has terminated, no step emits an event tagged `t`.
theorem term_last {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {t : TxId} {e b : Event}
    (he : e ∈ events τ) (het : e.label.tx = t) (hb : Terminates (events τ) t b) :
    e = b ∨ OccursBefore (events τ) e b := by
 sorry

-- The lifted VIS/AR lemma: if `S` is visible to an operation `e` of `T`,
-- then `S` comes before `T` in the witness `AR` (finish order).
theorem vis_ar {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') {S T : Transaction} {e : Event}
    (hT : (witness τ).txs T) (hvis : visOf (events τ) S e) (heT : T.E e) :
    (witness τ).ar S T := by
  sorry

/-! ## Main theorem -/

-- The main theorem: some history of the run satisfies Int and Ext.
-- The witness is `witness τ` (finish order); Int holds for every history of τ.
theorem correctness {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H ∧ H.Int ∧ H.Ext τ := by
  have hH : HistoryOf τ (witness τ) := witness_historyOf hrun
  -- Ext_u is not started yet.
  exact ⟨witness τ, hH, int_of_run hrun hH, extC_of_inv₁ (inv₁ hrun), sorry⟩

end Optimistic
