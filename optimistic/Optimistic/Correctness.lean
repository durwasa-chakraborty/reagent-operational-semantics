import Optimistic.ExtConsistency

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
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t e b, e ∈ events τ → e.label.tx = t → Terminates (events τ) t b →
        e = b ∨ OccursBefore (events τ) e b)
    (by intro t e b he; simp [events] at he) ?_ h t e b he het hb
  intro ls C ℓ C' hrun ih hstep
  cases ℓ with
  | adm => simp only [events_snoc_adm]; exact ih
  | ev n =>
    simp only [events_snoc_ev]
    intro t e b he het hb
    rcases terminates_snoc hb with hb₀ | hbn
    · -- old terminator: `n` is not tagged `t`, so `e` is old too
      have hnt : n.label.tx ≠ t := by
        intro hn; rw [← hn] at hb₀; exact tag_not_term hrun hstep b hb₀
      have he₀ : e ∈ events ls := by
        rcases List.mem_append.mp he with he | he
        · exact he
        · rw [List.mem_singleton.mp he] at het; exact absurd het hnt
      rcases ih t e b he₀ het hb₀ with heq | hlt
      · exact Or.inl heq
      · exact Or.inr (OccursBefore.post [n] hlt)
    · -- `b = n` is the new terminator
      have hbn' : b = n := by
        rcases List.mem_append.mp hb.1 with hm | hm
        · exfalso
          have hnt : n.label.tx = t := by rcases hbn with h' | h' <;> rw [h'] <;> rfl
          exact tag_not_term hrun hstep b (hnt ▸ ⟨hm, hb.2⟩)
        · exact List.mem_singleton.mp hm
      subst hbn'
      rcases List.mem_append.mp he with he | he
      · exact Or.inr (OccursBefore.snoc_last he)
      · exact Or.inl (List.mem_singleton.mp he)

-- The lifted VIS/AR lemma: if `S` is visible to an operation `e` of `T`,
-- then `S` comes before `T` in the witness `AR` (finish order).
theorem vis_ar {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') {S T : Transaction} {e : Event}
    (hT : (witness τ).txs T) (hvis : visOf (events τ) S e) (heT : T.E e) :
    (witness τ).ar S T := by
  obtain ⟨-, c, hc, hcl, hce⟩ := hvis
  obtain ⟨t, -, rfl⟩ := hT
  obtain ⟨he, het, hacc⟩ := heT
  have hcS : Terminates (events τ) S.txid c := ⟨hc, Or.inl hcl⟩
  by_cases hfin : Finished (events τ) t
  · -- `T` finished at `b`: `c ≺ e ≺ b`
    obtain ⟨b, hb⟩ := hfin
    refine Or.inl ⟨c, b, hcS, hb, ?_⟩
    rcases term_last hrun he het hb with rfl | heb
    · exfalso
      rcases hb.2 with h' | h' <;> simp [h', Label.isAccess] at hacc
    · exact OccursBefore.trans (inv_ids hrun).2 hce heb
  · -- `T` pending: finished before pending
    exact Or.inr (Or.inl ⟨⟨c, hcS⟩, hfin⟩)

/-! ## Main theorem -/

-- The main theorem: some history of the run satisfies Int and Ext.
-- The witness is `witness τ` (finish order); Int holds for every history of τ.
theorem correctness {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H ∧ H.Int ∧ H.Ext τ := by
  have hH : HistoryOf τ (witness τ) :=
    ⟨witness_h1 τ, witness_h2 hrun, witness_h3 hrun, witness_h4 hrun, witness_h5 hrun⟩
  exact ⟨witness τ, hH, int_of_run hrun hH, extC_witness hrun, extU_witness hrun⟩

/-! ## History with visibility `(T, AR, VIS)` -/

-- A history with visibility. AR orders transactions; VIS relates a
-- transaction to an operation, for every transaction (committed or not).
structure HistoryV where
  txs : Transaction → Prop
  ar  : Transaction → Transaction → Prop
  vis : Transaction → Event → Prop

-- Forget `vis`: the old `History`, so every existing proof stays as it is.
def HistoryV.toHistory (H : HistoryV) : History := ⟨H.txs, H.ar⟩

-- Ext with the history's own VIS: every external read of every T.
def HistoryV.Ext (H : HistoryV) : Prop := H.toHistory.ExtOp H.vis

-- Witness: AR = finish order of the trace, VIS = `end_S ≺ e`.
def witnessV (τ : Trace) : HistoryV :=
  ⟨txsOfTrace τ, finishOrder (events τ), visOf (events τ)⟩

-- The main theorem over `(T, AR, VIS)`: some history of the run satisfies Int and Ext.
theorem correctnessV {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') :
    ∃ H : HistoryV, HistoryOf τ H.toHistory ∧ H.toHistory.Int ∧ H.Ext := by
  have hH : HistoryOf τ (witness τ) :=
    ⟨witness_h1 τ, witness_h2 hrun, witness_h3 hrun, witness_h4 hrun, witness_h5 hrun⟩
  exact ⟨witnessV τ, hH, int_of_run hrun hH, extOp_of_uinv (inv_ext hrun).uread⟩

end Optimistic
