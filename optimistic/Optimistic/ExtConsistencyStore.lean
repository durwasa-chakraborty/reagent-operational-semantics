/-
  Store: for every `x`, `σ(x)` is the value of the last `set` on `x` by the
  latest committed writer of `x`, or `σ₀(x)` if no committed transaction set `x`.

  One step splits into two worlds:
    σ        only Commit changes it, to `Log.apply σ Λ`
    writers  the committed writers of `x` and their last sets; a step adds at
             most one committed transaction (L3), and only Commit does

  The table (one line per rule) is the Store field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtConsistencyCurrent

namespace Optimistic

open Reagent (Loc TxId ThId EvId Expr Store)

/-! ## The invariant -/

-- `c` is the commit event of `t`.
def CommitEv (es : List Event) (t : TxId) (c : Event) : Prop := c ∈ es ∧ c.label = .eend t

-- Store at one location: `σ(x)` is the last `set` value of the latest
-- committed writer of `x`, or `σ₀(x)` if there is none.
def StoreSpec (es : List Event) (σ : Store) (x : Loc) : Prop :=
  (∃ s c, CommitEv es s c ∧ HasSet es s x ∧ LastSetVal es s x (σ x) ∧
      ∀ s' c', CommitEv es s' c' → HasSet es s' x → c' = c ∨ OccursBefore es c' c)
  ∨ ((∀ s c, CommitEv es s c → ¬ HasSet es s x) ∧ σ x = Store.init_store x)

-- Store at every location.
def StoreInv (es : List Event) (σ : Store) : Prop := ∀ x, StoreSpec es σ x

/-! ## Commit events across a step -/

theorem CommitEv.snoc {es : List Event} {t : TxId} {c n : Event}
    (h : CommitEv es t c) : CommitEv (es ++ [n]) t c := by
  sorry

theorem CommitEv.of_snoc {es : List Event} {t : TxId} {c n : Event}
    (h : CommitEv (es ++ [n]) t c) (hn : n.label ≠ .eend t) : CommitEv es t c := by
  rcases List.mem_append.mp h.1 with hc | hc
  · exact ⟨hc, h.2⟩
  · rw [List.mem_singleton.mp hc] at h
    exact absurd h.2 hn

/-! ## Frame for one location -/

-- `σ(x)` unchanged keeps StoreSpec at `x`.
theorem StoreSpec.congr {es : List Event} {σ σ' : Store} {x : Loc}
    (hσ : σ' x = σ x) (h : StoreSpec es σ x) : StoreSpec es σ' x := by
  unfold StoreSpec at *
  rw [hσ]
  exact h

-- Writers unchanged: `n` is no set on `x` by a committed `s` (B4'), and if `n`
-- commits some `s`, that `s` did not set `x`.
theorem StoreSpec.frame {es : List Event} {σ : Store} {x : Loc} {n : Event}
    (hu : UniqueIds (es ++ [n]))
    (hset : ∀ s c, CommitEv es s c → ∀ w, n.label ≠ .set x w s)
    (hend : ∀ s, n.label = .eend s → ¬ HasSet (es ++ [n]) s x)
    (h : StoreSpec es σ x) : StoreSpec (es ++ [n]) σ x := by
  -- a committed writer of es' was already committed in es
  have hold : ∀ s c, CommitEv (es ++ [n]) s c → HasSet (es ++ [n]) s x → CommitEv es s c := by
    intro s c hc hs
    by_cases hn : n.label = .eend s
    · exact absurd hs (hend s hn)
    · exact hc.of_snoc hn
  rcases h with ⟨s, c, hc, hs, hv, hmax⟩ | ⟨hnone, hinit⟩
  · -- the latest committed writer s stays the latest, with the same last set
    obtain ⟨hS, hW⟩ := B4' hu (hset s c hc)
    refine Or.inl ⟨s, c, hc.snoc, hS.mpr hs, (hW _).mpr hv, fun s' c' hc' hs' => ?_⟩
    have hc'old := hold s' c' hc' hs'
    rcases hmax s' c' hc'old ((B4' hu (hset s' c' hc'old)).1.mp hs') with heq | hlt
    · exact Or.inl heq
    · exact Or.inr hlt.snoc_mono
  · -- still no committed writer
    refine Or.inr ⟨fun s c hc hs => ?_, hinit⟩
    have hcold := hold s c hc hs
    exact hnone s c hcold ((B4' hu (hset s c hcold)).1.mp hs)

-- Commit of a writer `t` of `x`: `t` becomes the latest committed writer.
theorem StoreSpec.commit_writer {es : List Event} {σ' : Store} {x : Loc} {n : Event}
    {t : TxId} (hu : UniqueIds (es ++ [n])) (hn : n.label = .eend t)
    (hs : HasSet es t x) (hv : LastSetVal es t x (σ' x)) :
    StoreSpec (es ++ [n]) σ' x := by
  obtain ⟨hS, hW⟩ := B4' (s := t) (x := x) hu (fun w hw => by rw [hn] at hw; cases hw)
  refine Or.inl ⟨t, n, ⟨List.mem_append_right _ (List.mem_singleton_self _), hn⟩,
    hS.mpr hs, (hW _).mpr hv, fun s' c' hc' _ => ?_⟩
  rcases List.mem_append.mp hc'.1 with hc | hc
  · exact Or.inr (OccursBefore.snoc_last hc)
  · exact Or.inl (List.mem_singleton.mp hc)

/-! ## Two worlds -/

-- σ unchanged, writers unchanged: `n` is neither a set nor an end.
theorem store_noset {τ : Trace} {σ : Store} {n : Event}
    (hu : UniqueIds (events (τ ++ [.ev n])))
    (hn₁ : ∀ x w t, n.label ≠ .set x w t) (hn₂ : ∀ t, n.label ≠ .eend t)
    (h : StoreInv (events τ) σ) : StoreInv (events (τ ++ [.ev n])) σ := by
  simp only [events_snoc_ev] at hu ⊢
  intro x
  exact (h x).frame hu (fun _ _ _ w => hn₁ x w _) (fun s hs => absurd hs (hn₂ s))

-- σ unchanged, writers unchanged: `n` is a set by a live `t`, which has not
-- committed, so it is no committed writer.
theorem store_live_set {τ : Trace} {σ : Store} {n : Event} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (htag : n.label.tx = t)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) (hn : ∀ t', n.label ≠ .eend t')
    (h : StoreInv (events τ) σ) : StoreInv (events (τ ++ [.ev n])) σ := by
  simp only [events_snoc_ev] at hu ⊢
  intro x
  refine (h x).frame hu (fun s c hc w hw => ?_) (fun s hs => absurd hs (hn s))
  -- n is a set by s, so s = t, but t has no commit event
  have hst : s = t := by rw [← htag, hw]; rfl
  subst hst
  exact hlive c ⟨hc.1, Or.inl hc.2⟩

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

-- begin. σ: unchanged. writers: begin is no set, no end.
theorem store_begin {τ : Trace} {σ : Store} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .begin t⟩]))) (h : StoreInv (events τ) σ) :
    StoreInv (events (τ ++ [.ev ⟨α, .begin t⟩])) σ :=
  store_noset hu (by simp) (by simp) h

-- Get-Log / Get-Mem. σ: unchanged. writers: get is no set, no end.
theorem store_get {τ : Trace} {σ : Store} {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : StoreInv (events τ) σ) :
    StoreInv (events (τ ++ [.ev ⟨α, .get l v t⟩])) σ :=
  store_noset hu (by simp) (by simp) h

-- Set-Log / Set-Mem. σ: unchanged. writers: t is live, so not committed.
theorem store_set {τ : Trace} {σ : Store} {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : StoreInv (events τ) σ)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    StoreInv (events (τ ++ [.ev ⟨α, .set l v t⟩])) σ :=
  store_live_set hu rfl hlive (by simp) h

-- KCas-Retry / Retry. σ: unchanged. writers: retry is no set, no end.
theorem store_retry {τ : Trace} {σ : Store} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .retry t⟩]))) (h : StoreInv (events τ) σ) :
    StoreInv (events (τ ++ [.ev ⟨α, .retry t⟩])) σ :=
  store_noset hu (by simp) (by simp) h

-- Commit. σ: Log.apply σ Λ. writers: t joins, as the latest one, if it set x.
--   Λ(x) = ⊥                σ'(x) = σ(x); t never set x (L)              frame
--   Λ(x) = (o, c), t set x  σ'(x) = c = t's last set (Cur)               t is the latest
--   Λ(x) = (o, c), no set   σ'(x) = c = o (Cur) = σ(x) (KCasOk)          frame
theorem store_commit {τ : Trace} {σ : Store} {α : EvId} {t : TxId} {Λ : Log}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .eend t⟩]))) (h : StoreInv (events τ) σ)
    (hcur : ∀ x, CurVal (events τ) t Λ x) (hL : ∀ x, MirrorsAt (events τ) t Λ x)
    (hok : KCasOk σ Λ) :
    StoreInv (events (τ ++ [.ev ⟨α, .eend t⟩])) (Log.apply σ Λ) := by
  simp only [events_snoc_ev] at hu ⊢
  intro x
  -- end is no set
  have hns : ∀ s c, CommitEv (events τ) s c → ∀ w,
      (⟨α, .eend t⟩ : Event).label ≠ .set x w s := by
    intro s c hc w hw
    cases hw
  -- if t did not set x before, it has not set x after
  have hend : ¬ HasSet (events τ) t x → ∀ s, (⟨α, .eend t⟩ : Event).label = .eend s →
      ¬ HasSet (events τ ++ [⟨α, .eend t⟩]) s x := by
    intro hn s hs hs'
    cases hs
    exact hn ((B4' hu (fun w hw => by cases hw)).1.mp hs')
  cases hΛ : Λ x with
  | none =>
    have hσ : Log.apply σ Λ x = σ x := by simp [Log.apply, hΛ]
    have hnoset : ¬ HasSet (events τ) t x := by
      rintro ⟨a, ha, w, hw⟩
      have := (hL x).1 hΛ a ha (by rw [hw]; rfl)
      rw [hw] at this
      simp [Label.accesses] at this
    exact ((h x).frame hu hns (hend hnoset)).congr hσ
  | some oc =>
    obtain ⟨o, c⟩ := oc
    have hσ : Log.apply σ Λ x = c := by simp [Log.apply, hΛ]
    obtain ⟨hw, hr⟩ := hcur x o c hΛ
    by_cases hs : HasSet (events τ) t x
    · exact StoreSpec.commit_writer hu rfl hs (by rw [hσ]; exact hw hs)
    · have hσ' : Log.apply σ Λ x = σ x := by
        rw [hσ, hr hs]
        exact (hok x o c hΛ).symm
      exact ((h x).frame hu hns (hend hs)).congr hσ'

-- Adm. no event, σ unchanged.
theorem store_adm {τ : Trace} {σ : Store}
    (h : StoreInv (events τ) σ) : StoreInv (events (τ ++ [.adm])) σ := by
  sorry

end Optimistic
