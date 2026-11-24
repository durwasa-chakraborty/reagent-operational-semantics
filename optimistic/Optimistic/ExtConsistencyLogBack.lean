/-
  L⁻ (part (b)): a log entry comes from an access. For every live `t` with log
  `Λ`, if `Λ(x) ≠ ⊥` then some event of `es` tagged `t` accesses `x`.
  Together with L:  `Λ_t(x) = ⊥  ⇔  t has no access to x`.

  One step splits into two worlds, as for Cur:
    others' frame   other logs never change, and `es ⊆ es'`, so a witnessing
                    access is still there
    my frame        the stepping thread's own log: entered, left, or given a
                    new entry by Get-Mem / Set-Mem, which emit an access to
                    that location in the same step

  The table (one line per rule) is the L⁻ field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtConsistencyP

namespace Optimistic

open Reagent (Loc TxId ThId EvId Expr update update_other)

/-! ## The invariant -/

-- L⁻ for one log: every entry of `Λ` is witnessed by an access of `t`.
def LogBackAt (es : List Event) (t : TxId) (Λ : Log) : Prop :=
  ∀ x, Λ x ≠ none → ∃ a ∈ es, a.label.tx = t ∧ a.label.accesses x = true

-- L⁻ for every live thread.
def LogBack (es : List Event) (θ : ThId → Option (TxId × Log × Expr)) : Prop :=
  ∀ i t Λ Ê, θ i = some (t, Λ, Ê) → LogBackAt es t Λ

/-! ## Others' frame -/

-- Events only grow: a witnessing access stays.
theorem LogBackAt.snoc {es : List Event} {n : Event} {t : TxId} {Λ : Log}
    (h : LogBackAt es t Λ) : LogBackAt (es ++ [n]) t Λ := by
  intro x hx
  obtain ⟨a, ha, htag, hacc⟩ := h x hx
  exact ⟨a, List.mem_append_left _ ha, htag, hacc⟩

-- Any event: nobody's L⁻ breaks.
theorem lb_snoc {τ : Trace} {n : Event} {θ : ThId → Option (TxId × Log × Expr)}
    (h : LogBack (events τ) θ) : LogBack (events (τ ++ [.ev n])) θ := by
  rw [events_snoc_ev]
  intro i t Λ Ê hi
  exact (h i t Λ Ê hi).snoc

/-! ## My frame -/

-- begin: my thread enters with the empty log, which has no entries.
theorem lb_enter {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Ê : Expr}
    (h : LogBack es θ) : LogBack es (update θ i (some (t, Log.empty, Ê))) := by
  intro k t' Λ Ê' hk
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
  · obtain ⟨rfl, rfl, -⟩ := hv
    intro x hx
    exact (hx rfl).elim
  · exact h k t' Λ Ê' hk

-- end / retry: my thread leaves.
theorem lb_leave {es : List Event} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    (h : LogBack es θ) : LogBack es (update θ i none) := by
  intro k t Λ Ê hk
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
  · cases hv
  · exact h k t Λ Ê hk

-- My log becomes `Λ₁`: others as given, mine as given.
theorem lb_mine {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Λ₁ : Log} {Ê : Expr}
    (hothers : ∀ k t' Λ Ê', k ≠ i → θ k = some (t', Λ, Ê') → LogBackAt es t' Λ)
    (hmine : LogBackAt es t Λ₁) : LogBack es (update θ i (some (t, Λ₁, Ê))) := by
  intro k t' Λ Ê' hk
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
  · obtain ⟨rfl, rfl, -⟩ := hv
    exact hmine
  · exact hothers k t' Λ Ê' hki hk

-- Get-Mem / Set-Mem at `l`: the new entry at `l` is witnessed by `n` itself.
theorem mine_access {es : List Event} {n : Event} {t : TxId} {Λ : Log} {l : Loc}
    {p : Nat × Nat} (h : LogBackAt es t Λ)
    (htag : n.label.tx = t) (hacc : n.label.accesses l = true) :
    LogBackAt (es ++ [n]) t (update Λ l (some p)) := by
  intro x hx
  by_cases hlx : l = x
  · -- at l: n accesses l
    subst hlx
    exact ⟨n, List.mem_append_right _ (List.mem_singleton_self _), htag, hacc⟩
  · -- elsewhere: the entry is old
    rw [update_other Λ l x _ hlx] at hx
    exact LogBackAt.snoc h x hx

-- Set-Log at `l`: the entry at `l` was already there, so the old witness stays.
theorem mine_keep {es : List Event} {n : Event} {t : TxId} {Λ : Log} {l : Loc}
    {p : Nat × Nat} (h : LogBackAt es t Λ) (hl : Λ l ≠ none) :
    LogBackAt (es ++ [n]) t (update Λ l (some p)) := by
  intro x hx
  by_cases hlx : l = x
  · subst hlx
    exact LogBackAt.snoc h l hl
  · rw [update_other Λ l x _ hlx] at hx
    exact LogBackAt.snoc h x hx

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

-- begin. mine: new empty log. others: frame.
theorem lb_begin {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId} {Ê : Expr} (h : LogBack (events τ) θ) :
    LogBack (events (τ ++ [.ev ⟨α, .begin t⟩])) (update θ i (some (t, Log.empty, Ê))) :=
  lb_enter (lb_snoc h)

-- Get-Log. mine: unchanged. others: frame.
theorem lb_getLog {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {n : Event}
    (h : LogBack (events τ) θ) : LogBack (events (τ ++ [.ev n])) θ :=
  lb_snoc h

-- Get-Mem. mine: (v, v) at l, witnessed by n. others: frame.
theorem lb_getMem {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {v : Nat} {α : EvId}
    (h : LogBack (events τ) θ) (hi : θ i = some (t, Λ, Ê)) :
    LogBack (events (τ ++ [.ev ⟨α, .get l v t⟩]))
      (update θ i (some (t, update Λ l (some (v, v)), Ê))) := by
  have hall := lb_snoc (n := ⟨α, .get l v t⟩) h
  refine lb_mine (fun k t' Λ' Ê' _ hk => hall k t' Λ' Ê' hk) ?_
  rw [events_snoc_ev]
  exact mine_access (h i t Λ Ê hi) rfl (by simp [Label.accesses])

-- Set-Log. mine: (o, v) at l, entry already there. others: frame.
theorem lb_setLog {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {o c v : Nat} {α : EvId}
    (h : LogBack (events τ) θ) (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = some (o, c)) :
    LogBack (events (τ ++ [.ev ⟨α, .set l v t⟩]))
      (update θ i (some (t, update Λ l (some (o, v)), Ê))) := by
  have hall := lb_snoc (n := ⟨α, .set l v t⟩) h
  refine lb_mine (fun k t' Λ' Ê' _ hk => hall k t' Λ' Ê' hk) ?_
  rw [events_snoc_ev]
  exact mine_keep (h i t Λ Ê hi) (by simp [hl])

-- Set-Mem. mine: (u, v) at l, witnessed by n. others: frame.
theorem lb_setMem {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {u v : Nat} {α : EvId}
    (h : LogBack (events τ) θ) (hi : θ i = some (t, Λ, Ê)) :
    LogBack (events (τ ++ [.ev ⟨α, .set l v t⟩]))
      (update θ i (some (t, update Λ l (some (u, v)), Ê))) := by
  have hall := lb_snoc (n := ⟨α, .set l v t⟩) h
  refine lb_mine (fun k t' Λ' Ê' _ hk => hall k t' Λ' Ê' hk) ?_
  rw [events_snoc_ev]
  exact mine_access (h i t Λ Ê hi) rfl (by simp [Label.accesses])

-- Commit / KCas-Retry / Retry. mine: leaves. others: frame.
theorem lb_end {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId} {n : Event}
    (h : LogBack (events τ) θ) : LogBack (events (τ ++ [.ev n])) (update θ i none) :=
  lb_leave (lb_snoc h)

-- Adm. no event, no log changes.
theorem lb_adm {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)}
    (h : LogBack (events τ) θ) : LogBack (events (τ ++ [.adm])) θ := by
  sorry

end Optimistic
