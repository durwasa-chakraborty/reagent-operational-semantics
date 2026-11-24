/-
  Cur: in every live log, `Λ(x) = (o, c)` with `c` the value of the last
  `set` of `t` on `x`, or `c = o` if `t` has not set `x`.

  One step splits into two worlds:
    others' frame   another thread's log is untouched, and the new event is not
                    one of its sets (Lemma B)
    my frame        the stepping thread's own log: entered, left, or updated at
                    one location

  The table (one line per rule) is the Cur field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtFrame

namespace Optimistic

open Reagent (Loc TxId ThId EvId Expr update update_other)

/-! ## The invariant -/

-- Cur at one location: `Λ(x) = (o, c)` with `c` the last `set` of `t` on `x`,
-- or `c = o` if `t` has not set `x`.
def CurVal (es : List Event) (t : TxId) (Λ : Log) (x : Loc) : Prop :=
  ∀ o c, Λ x = some (o, c) → (HasSet es t x → LastSetVal es t x c) ∧ (¬ HasSet es t x → c = o)

-- Cur for every live thread.
def Cur (es : List Event) (θ : ThId → Option (TxId × Log × Expr)) : Prop :=
  ∀ i t Λ Ê, θ i = some (t, Λ, Ê) → ∀ x, CurVal es t Λ x

/-! ## Frame for one log -/

-- If `n` is not a set on `x` by `t`, `CurVal` of `t` at `x` carries over (B4').
theorem CurVal.frame {es : List Event} {n : Event} {t : TxId} {Λ : Log} {x : Loc}
    (hu : UniqueIds (es ++ [n])) (hn : ∀ w, n.label ≠ .set x w t)
    (h : CurVal es t Λ x) : CurVal (es ++ [n]) t Λ x := by
  obtain ⟨hset, hwr⟩ := B4' hu hn
  intro o c hx
  obtain ⟨h1, h2⟩ := h o c hx
  constructor
  · -- t has set x in es': then also in es, and wr is the same
    intro hs
    exact (hwr c).mpr (h1 (hset.mp hs))
  · -- t has not set x in es': then not in es either, so c = o
    intro hs
    exact h2 (fun hs' => hs (hset.mpr hs'))

-- If `t ≠ tag(n)`, `CurVal` of `t` carries over (B4).
theorem cur_other {es : List Event} {n : Event} {t : TxId} {Λ : Log} {x : Loc}
    (hu : UniqueIds (es ++ [n])) (ht : t ≠ n.label.tx)
    (h : CurVal es t Λ x) : CurVal (es ++ [n]) t Λ x :=
  CurVal.frame hu (fun w hw => ht (by rw [hw]; rfl)) h

/-! ## Others' frame -/

-- `n` is not a set: nobody's Cur changes.
theorem cur_noset {τ : Trace} {n : Event} {θ : ThId → Option (TxId × Log × Expr)}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hn : ∀ x w t, n.label ≠ .set x w t)
    (h : Cur (events τ) θ) : Cur (events (τ ++ [.ev n])) θ := by
  simp only [events_snoc_ev] at hu ⊢
  intro i t Λ Ê hi x
  exact CurVal.frame hu (fun w => hn x w t) (h i t Λ Ê hi x)

-- `n` is emitted by thread `i` running `t₀`: every other live thread `k` runs
-- a different tag (D), so its Cur is unchanged.
theorem cur_others {τ : Trace} {n : Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t₀ : TxId} {Λ₀ : Log} {Ê₀ : Expr}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (h : Cur (events τ) θ) (hD : LiveDistinct θ)
    (hi : θ i = some (t₀, Λ₀, Ê₀)) (htag : n.label.tx = t₀) :
    ∀ k t Λ Ê, k ≠ i → θ k = some (t, Λ, Ê) → ∀ x, CurVal (events (τ ++ [.ev n])) t Λ x := by
  simp only [events_snoc_ev] at hu ⊢
  intro k t Λ Ê hki hk x
  have hne : t ≠ n.label.tx := by
    rw [htag]
    intro heq
    subst heq
    exact hki (hD k i t Λ Λ₀ Ê Ê₀ hk hi)
  exact cur_other hu hne (h k t Λ Ê hk x)

/-! ## My frame -/

-- begin: my thread enters with the empty log.
theorem cur_enter {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Ê : Expr}
    (h : Cur es θ) : Cur es (update θ i (some (t, Log.empty, Ê))) := by
  intro k t' Λ Ê' hk x
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
  · -- me: the empty log has no entries
    obtain ⟨rfl, rfl, -⟩ := hv
    intro o c hx
    simp [Log.empty] at hx
  · exact h k t' Λ Ê' hk x

-- end / retry: my thread leaves.
theorem cur_leave {es : List Event} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    (h : Cur es θ) : Cur es (update θ i none) := by
  intro k t Λ Ê hk x
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
  · cases hv
  · exact h k t Λ Ê hk x

-- My log becomes `Λ₁`: others as given, mine as given.
-- NOTE the idea is that after taking one step only my log should cahnge
-- the update function says that after taking a step only log responsible for my thread
-- should change
theorem cur_mine {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Λ₁ : Log} {Ê : Expr}
    (hothers : ∀ k t' Λ Ê', k ≠ i → θ k = some (t', Λ, Ê') → ∀ x, CurVal es t' Λ x)
    (hmine : ∀ x, CurVal es t Λ₁ x) : Cur es (update θ i (some (t, Λ₁, Ê))) := by
  intro k t' Λ Ê' hk x
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
  · obtain ⟨rfl, rfl, -⟩ := hv
    exact hmine x
  · exact hothers k t' Λ Ê' hki hk x

-- A new `set` on `x` tagged `t` is the last one.
theorem LastSetVal.new {es : List Event} {t : TxId} {x : Loc} {v : Nat} {n : Event}
    (hu : UniqueIds (es ++ [n])) (hn : n.label = .set x v t) :
    LastSetVal (es ++ [n]) t x v := by
  refine ⟨n, List.mem_append_right _ (List.mem_singleton_self _), hn, fun b hb _ hnb => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact not_occursBefore_snoc hu hb hnb
  · rw [List.mem_singleton.mp hb] at hnb
    exact OccursBefore.irrefl hu hnb

-- Get-Mem at `l`: my log gets `(v, v)` at `l`. By L, `t` had no access to `l`,
-- so it has not set `l`, and `c = o = v`.
theorem mine_getMem {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {v : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hcur : ∀ x, CurVal (events τ) t Λ x)
    (hL : NoAccess (events τ) t l) (hn : n.label = .get l v t) :
    ∀ x, CurVal (events (τ ++ [.ev n])) t (update Λ l (some (v, v))) x := by
  simp only [events_snoc_ev] at hu ⊢
  intro x
  by_cases hlx : l = x
  · -- at l: the entry is (v, v), and t has no set on l
    subst hlx
    intro o c hx
    simp only [update, if_true, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨fun hs => absurd hs ?_, fun _ => rfl⟩
    rintro ⟨a, ha, w, hw⟩
    rcases List.mem_append.mp ha with ha | ha
    · have := hL a ha (by rw [hw]; rfl)
      rw [hw] at this
      simp [Label.accesses] at this
    · rw [List.mem_singleton.mp ha, hn] at hw
      cases hw
  · -- elsewhere: the log is unchanged, and a get is no set
    intro o c hx
    rw [update_other Λ l x _ hlx] at hx
    exact CurVal.frame hu (fun w hw => by rw [hn] at hw; cases hw) (hcur x) o c hx

-- Set-Log / Set-Mem at `l`: my log gets `(o, v)` at `l`, and `n` is the last set.
theorem mine_set {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {o v : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hcur : ∀ x, CurVal (events τ) t Λ x)
    (hn : n.label = .set l v t) :
    ∀ x, CurVal (events (τ ++ [.ev n])) t (update Λ l (some (o, v))) x := by
  simp only [events_snoc_ev] at hu ⊢
  intro x
  by_cases hlx : l = x
  · -- at l: c = v, the value of the new last set
    subst hlx
    intro o' c' hx
    simp only [update, if_true, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨fun _ => LastSetVal.new hu hn,
      fun hs => absurd ⟨n, List.mem_append_right _ (List.mem_singleton_self _), v, hn⟩ hs⟩
  · -- elsewhere: the log is unchanged, and a set on l is no set on x
    intro o' c' hx
    rw [update_other Λ l x _ hlx] at hx
    exact CurVal.frame hu (fun w hw => by rw [hn] at hw; simp at hw; exact hlx hw.1)
      (hcur x) o' c' hx

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

-- begin. mine: new empty log. others: begin is no set.
theorem cur_begin {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId} {Ê : Expr}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .begin t⟩]))) (h : Cur (events τ) θ) :
    Cur (events (τ ++ [.ev ⟨α, .begin t⟩])) (update θ i (some (t, Log.empty, Ê))) :=
  cur_enter (cur_noset hu (by simp) h)

-- Get-Log. mine: unchanged. others: get is no set.
theorem cur_getLog {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)}
    {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : Cur (events τ) θ) :
    Cur (events (τ ++ [.ev ⟨α, .get l v t⟩])) θ :=
  cur_noset hu (by simp) h

-- Get-Mem. mine: (v, v) at l. others: different tag.
theorem cur_getMem {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : Cur (events τ) θ)
    (hD : LiveDistinct θ) (hL : LogMirrors (events τ) θ)
    (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = none) :
    Cur (events (τ ++ [.ev ⟨α, .get l v t⟩])) (update θ i (some (t, update Λ l (some (v, v)), Ê))) :=
  cur_mine (cur_others hu h hD hi rfl) (mine_getMem hu (h _ _ _ _ hi) ((hL _ _ _ _ hi _).1 hl) rfl)

-- Set-Log / Set-Mem. mine: (o, v) at l. others: different tag.
-- NOTE the proof obligation is that only the current changes the log
-- the update function in the `Cur` invariant is the same as what we saw in the `cur_mine`
theorem cur_set {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {o v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : Cur (events τ) θ)
    (hD : LiveDistinct θ) (hi : θ i = some (t, Λ, Ê)) :
    Cur (events (τ ++ [.ev ⟨α, .set l v t⟩])) (update θ i (some (t, update Λ l (some (o, v)), Ê))) :=
  cur_mine (cur_others hu h hD hi rfl) (mine_set hu (h _ _ _ _ hi) rfl)

-- Commit. mine: leaves. others: end is no set.
theorem cur_commit {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .eend t⟩]))) (h : Cur (events τ) θ) :
    Cur (events (τ ++ [.ev ⟨α, .eend t⟩])) (update θ i none) :=
  cur_leave (cur_noset hu (by simp) h)

-- KCas-Retry / Retry. mine: leaves. others: retry is no set.
theorem cur_retry {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .retry t⟩]))) (h : Cur (events τ) θ) :
    Cur (events (τ ++ [.ev ⟨α, .retry t⟩])) (update θ i none) :=
  cur_leave (cur_noset hu (by simp) h)

-- Adm. no event, no log changes.
theorem cur_adm {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)}
    (h : Cur (events τ) θ) : Cur (events (τ ++ [.adm])) θ := by
  sorry

end Optimistic
