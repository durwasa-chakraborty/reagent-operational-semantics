/-
  Lemma B (L2, frame): appending an event `n` to `es` does not change
  anything about the events already in `es`.
-/
import Optimistic.ExtStatement

namespace Optimistic

open Reagent (Loc TxId)

/-! ## set and wr -/

-- `t` has a `set` on `x`.
def HasSet (es : List Event) (t : TxId) (x : Loc) : Prop :=
  ∃ a ∈ es, ∃ v, a.label = .set x v t

-- The `po`-last `set` on `x` tagged `t` writes `v`.
def LastSetVal (es : List Event) (t : TxId) (x : Loc) (v : Nat) : Prop :=
  ∃ a ∈ es, a.label = .set x v t ∧
    ∀ b ∈ es, (∃ w, b.label = .set x w t) → ¬ OccursBefore es a b

/-! ## Lemma B (L2, frame): appending `n` does not change old events -/

-- `Ext_es(e)`: `e` is an external read in `es`, a `get(x, v)@t` with no
-- earlier access of `t` to `x`.
def IsExt (es : List Event) (e : Event) : Prop :=
  ∃ x v t, e.label = .get x v t ∧
    ¬ ∃ a ∈ es, a.label.tx = t ∧ a.label.accesses x = true ∧ OccursBefore es a e

-- B1: for `a, b ∈ es`,  `a <_{es'} b  ↔  a <_{es} b`.
theorem B1 {es : List Event} {n a b : Event}
    (hu : UniqueIds (es ++ [n])) (ha : a ∈ es) (hb : b ∈ es) :
    OccursBefore (es ++ [n]) a b ↔ OccursBefore es a b := by
  sorry

-- B2: for `e ∈ es`,  `Ext_{es'}(e)  ↔  Ext_{es}(e)`.
theorem B2 {es : List Event} {n e : Event}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es) :
    IsExt (es ++ [n]) e ↔ IsExt es e := by
  constructor
  · -- (→) an earlier access in es is also one in es'
    rintro ⟨x, v, t, hl, hno⟩
    refine ⟨x, v, t, hl, ?_⟩
    rintro ⟨a, ha, htag, hacc, hae⟩
    exact hno ⟨a, List.mem_append_left _ ha, htag, hacc, hae.snoc_mono⟩
  · -- (←) split es' = es ++ [n]
    rintro ⟨x, v, t, hl, hno⟩
    refine ⟨x, v, t, hl, ?_⟩
    rintro ⟨a, ha, htag, hacc, hae⟩
    rcases List.mem_append.mp ha with ha | ha
    · -- a ∈ es: by B1, a <es e, which es already rules out
      exact hno ⟨a, ha, htag, hacc, (B1 hu ha he).mp hae⟩
    · -- a = n: n <es' e is false, since n is last
      rw [List.mem_singleton.mp ha] at hae
      exact not_occursBefore_snoc hu he hae

-- B3: for `s ≠ tag(n)`,  `Ev_{es'}(s) = Ev_{es}(s)`.
theorem B3 {es : List Event} {n : Event} {s : TxId} (hs : s ≠ n.label.tx) :
    events_of_isAccess (es ++ [n]) s = events_of_isAccess es s := by
  -- unfold Ev and compare the two sides event by event
  funext e
  apply propext
  unfold events_of_isAccess
  constructor
  · rintro ⟨he, htag, hacc⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨he, htag, hacc⟩
    · -- e = n: then tag n = s, contradicting hs
      rw [List.mem_singleton.mp he] at htag
      exact absurd htag.symm hs
  · rintro ⟨he, htag, hacc⟩
    exact ⟨List.mem_append_left _ he, htag, hacc⟩

-- B4: for `s ≠ tag(n)`,  `set_{es'}(s, x) = set_{es}(s, x)`  and
-- `wr_{es'}(s, x, v) ↔ wr_{es}(s, x, v)`.
-- B4 only needs that `n` is not a `set` on `x` tagged `s`. This general form
-- also covers `n` tagged `s` itself when it is not a set on `x` (used by Cur).
theorem B4' {es : List Event} {n : Event} {s : TxId} {x : Loc}
    (hu : UniqueIds (es ++ [n])) (hn : ∀ w, n.label ≠ .set x w s) :
    (HasSet (es ++ [n]) s x ↔ HasSet es s x) ∧
      ∀ v, (LastSetVal (es ++ [n]) s x v ↔ LastSetVal es s x v) := by
  -- a set tagged s that lies in es ++ [n] lies in es
  have hold : ∀ a ∈ es ++ [n], (∃ w, a.label = .set x w s) → a ∈ es := by
    rintro a ha ⟨w, hw⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact ha
    · rw [List.mem_singleton.mp ha] at hw
      exact absurd hw (hn w)
  refine ⟨⟨fun ⟨a, ha, w, hw⟩ => ⟨a, hold a ha ⟨w, hw⟩, w, hw⟩,
           fun ⟨a, ha, w, hw⟩ => ⟨a, List.mem_append_left _ ha, w, hw⟩⟩, fun v => ?_⟩
  constructor
  · -- (→) the last set in es' is in es; a later set in es is a later one in es'
    rintro ⟨a, ha, hl, hmax⟩
    refine ⟨a, hold a ha ⟨v, hl⟩, hl, fun b hb hbs hab => ?_⟩
    exact hmax b (List.mem_append_left _ hb) hbs hab.snoc_mono
  · -- (←) a later set in es' is in es, and by B1 later in es
    rintro ⟨a, ha, hl, hmax⟩
    refine ⟨a, List.mem_append_left _ ha, hl, fun b hb hbs hab => ?_⟩
    have hb' := hold b hb hbs
    exact hmax b hb' hbs ((B1 hu ha hb').mp hab)

theorem B4 {es : List Event} {n : Event} {s : TxId} {x : Loc}
    (hu : UniqueIds (es ++ [n])) (hs : s ≠ n.label.tx) :
    (HasSet (es ++ [n]) s x ↔ HasSet es s x) ∧
      ∀ v, (LastSetVal (es ++ [n]) s x v ↔ LastSetVal es s x v) := by
  -- n is not a set tagged s, since tag n ≠ s
  refine B4' hu (fun w hw => hs ?_)
  rw [hw]
  rfl

-- Lemma B: B1 ∧ B2 ∧ B3 ∧ B4, with `es' = es ++ [n]`.
theorem lemmaB {es : List Event} {n : Event} (hu : UniqueIds (es ++ [n])) :
    (∀ a b, a ∈ es → b ∈ es → (OccursBefore (es ++ [n]) a b ↔ OccursBefore es a b))
    ∧ (∀ e ∈ es, IsExt (es ++ [n]) e ↔ IsExt es e)
    ∧ (∀ s, s ≠ n.label.tx → events_of_isAccess (es ++ [n]) s = events_of_isAccess es s)
    ∧ (∀ s x, s ≠ n.label.tx →
        (HasSet (es ++ [n]) s x ↔ HasSet es s x) ∧
          ∀ v, (LastSetVal (es ++ [n]) s x v ↔ LastSetVal es s x v)) :=
  ⟨fun _ _ ha hb => B1 hu ha hb,
   fun _ he => B2 hu he,
   fun _ hs => B3 hs,
   fun _ _ hs => B4 hu hs⟩

end Optimistic
