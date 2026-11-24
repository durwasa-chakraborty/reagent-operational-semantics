/-
  Scratch: exists_historyOf, proved.  Not part of the build.

  Edits to paste:

  1. Reagent/Trace.lean, HistoryOf: guard totality and real time with S ≠ T

       ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → H.ar S T ∨ H.ar T S) -- total
       ...
       ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → RealTimeBefore (events τ) S.txid T.txid → H.ar S T)

  2. Reagent/ExtConsistency.lean, the harST line: hrt now takes S ≠ T

       hrt _ _ hST hTT (fun hc => hst (congrArg Transaction.txid hc))
         (rtb_of_block hrun hsocc hte hst hblock)

  3. Reagent/ExtInvariants.lean, block_of_ar, last line: same

       (hrt _ _ hT hS (fun hc => hst (congrArg Transaction.txid hc).symm)
         (rtb_of_block hrun ht hs (fun hc => hst hc.symm) hbts)) har

  4. Reagent/Correctness.lean becomes the file below.
-/

/-
  Reagent — the statement the development exists to prove.

      ∀ C', ∀ τ, ∃ H.  Run C_init τ C'  ⟹  HistoryOf τ H ∧  H ⊨ Int  ∧  H ⊨ Ext
-/
import Reagent.ExtConsistency

namespace Reagent

/-- **Correctness.**  Every run's every history is internally and externally
consistent. -/
theorem correctness {E₀ : ThreadMap} {τ : Trace} {C' : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C') (hH : HistoryOf τ H) : H.Int ∧ H.Ext :=
  ⟨int_of_run hrun hH, ext_of_run hrun hH⟩

/-- **Every run has a history.**  The lock lays transactions out one block after
another; that block order is `ar`. -/
theorem exists_historyOf {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H := by
  have hu := (inv_ids hrun).2
  refine ⟨⟨txsOfTrace τ, fun S T => S.txid ≠ T.txid ∧ BlockBefore (events τ) S.txid T.txid⟩,
    fun T => Iff.rfl, ?_, ?_, ?_, ?_⟩
  · -- total: the lock puts one block first
    rintro S T ⟨s, -, rfl⟩ ⟨t, -, rfl⟩ hST
    have hst : s ≠ t := fun h => hST (by rw [h])
    rcases inv_block hrun s t hst with h | h
    · exact Or.inl ⟨hst, h⟩
    · exact Or.inr ⟨fun h' => hst h'.symm, h⟩
  · -- asymmetric: two blocks cannot each come first
    rintro S T ⟨s, ⟨a, ha, has⟩, rfl⟩ ⟨t, ⟨b, hb, hbt⟩, rfl⟩ ⟨-, h1⟩ ⟨-, h2⟩
    exact BlockBefore.asymm hu ha has hb hbt h1 h2
  · -- transitive: go through any event of the middle block
    rintro S T U ⟨s, ⟨a, ha, has⟩, rfl⟩ ⟨t, ⟨b, hb, hbt⟩, rfl⟩ ⟨u, -, rfl⟩ ⟨-, h1⟩ ⟨-, h2⟩
    refine ⟨?_, ?_⟩
    · intro hsu
      change s = u at hsu
      subst hsu
      exact BlockBefore.asymm hu ha has hb hbt h1 h2
    · intro x hx hxs y hy hyu
      exact OccursBefore.trans hu (h1 x hx hxs b hb hbt) (h2 b hb hbt y hy hyu)
  · -- real time: if `T`'s block came first, `S`'s end would follow `T`'s begin
    rintro S T ⟨s, -, rfl⟩ ⟨t, -, rfl⟩ hST hrt
    have hst : s ≠ t := fun h => hST (by rw [h])
    refine ⟨hst, ?_⟩
    rcases inv_block hrun s t hst with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, ⟨hx, hxl⟩, ⟨hy, hyl⟩, hxy⟩ := hrt
      have hxs : x.label.tx = s := by rcases hxl with h' | h' <;> rw [h'] <;> rfl
      have hyt : y.label.tx = t := by rw [hyl]; rfl
      exact OccursBefore.irrefl hu (OccursBefore.trans hu hxy (h y hy hyt x hx hxs))

/-- **Correctness, non-vacuously.**  Every run has a history, and it is
internally and externally consistent. -/
theorem correctness_exists {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H ∧ H.Int ∧ H.Ext := by
  obtain ⟨H, hH⟩ := exists_historyOf hrun
  exact ⟨H, hH, correctness hrun hH⟩

end Reagent
