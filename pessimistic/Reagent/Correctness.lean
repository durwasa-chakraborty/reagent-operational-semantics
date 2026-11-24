/-
  Reagent — the statement the development exists to prove.

      ∀ C', ∀ τ, ∀ H.  Run C_init τ C'  ∧  HistoryOf τ H  ⟹  H ⊨ Int  ∧  H ⊨ Ext
      WARN
      this doesnt work :: ∀ C', ∀ τ, ∀ H.  Run C_init τ C' ⟹  HistoryOf τ H  ∧  H ⊨ Int  ∧  H ⊨ Ext
-/
import Reagent.ExtConsistency

namespace Reagent

-- NOTE (optimistic) this `∀ H` form holds only because the lock forces `ar`.
--      probably would need some change here
theorem correctness {E₀ : ThreadMap} {τ : Trace} {C' : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C') (hH : HistoryOf τ H) : H.Int ∧ H.Ext :=
  ⟨int_of_run hrun hH, ext_of_run hrun hH⟩


-- NOTE (optimistic) the witness `ar` is `BlockBefore`, which is total only by
--      `inv_block` (the lock). With interleaved blocks, pick another `ar`: order
--      transactions by their terminating event (`eend`/`retry`), with the live
--      one last. The order should still be total.
theorem exists_historyOf {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H := by
  have hu := (inv_ids hrun).2
  refine ⟨⟨txsOfTrace τ, fun S T => S.txid ≠ T.txid ∧ BlockBefore (events τ) S.txid T.txid⟩,
    fun T => Iff.rfl, ?_, ?_, ?_, ?_⟩
  · -- total: the lock puts one block first
    -- NOTE (optimistic) `inv_block` is false once transactions overlap; totality
    --      would come from comparing the positions of the terminating events.
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
    -- NOTE (optimistic) the clause stays in `HistoryOf`. For overlapping pairs
    --      its premise is false, so it says nothing. With the terminating-event
    --      order: `S` ends before `T` begins, and `T` begins before `T` ends.
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

-- NOTE (Optimistic)
--      this theorem is not used here but ∃ H, for optimistic lock can be used.
--      Maybe!
--
theorem correctness_exists {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H ∧ H.Int ∧ H.Ext := by
  obtain ⟨H, hH⟩ := exists_historyOf hrun
  exact ⟨H, hH, correctness hrun hH⟩


end Reagent
