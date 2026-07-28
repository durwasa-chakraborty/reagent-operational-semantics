/-
  Consistency of the Reagent semantics (Section "Consistency" of
  `docs/reagent-correctness.tex`).

  The `Int` and `Ext` axioms of the paper are given as computable checks in
  `Reagent/Trace.lean`.  Here we prove the *soundness* property the paper is
  after: every trace produced by the operational semantics is internally
  consistent — for every `get(x,n)@t`, if the transaction `t` already accessed
  `x`, the `po`-latest such earlier access carries `n`.

  The proof is a store-tracking induction: within a transaction the store on `x`
  equals the value of the latest earlier access to `x`, because the single lock
  keeps the transaction isolated and no rollback occurs before its terminator.
-/
import Reagent.Trace

namespace Reagent

/-! ## The same-transaction latest-access fold

    `accStep` keeps the `po`-latest `get`/`set` value on `x` within the current
    transaction, resetting at every transaction boundary (`begin`, `end`,
    `retry`).  Because the single lock makes the segment since the last `begin`
    exactly the current transaction's events, `sameTxLastAccess x pre` is the
    value of `max_po(po⁻¹(e) ∩ HEvent_x)` restricted to the transaction of the
    read `e` — precisely the left-hand side of the paper's `Int` axiom. -/
def accStep (x : Loc) (acc : Option Nat) : Label → Option Nat
  | .begin _   => none
  | .eend _    => none
  | .retry _   => none
  | .get x' v _ => if x' = x then some v else acc
  | .set x' v _ => if x' = x then some v else acc
  | .adm       => acc

@[simp] theorem accStep_begin (x acc t) : accStep x acc (.begin t) = none := rfl
@[simp] theorem accStep_eend  (x acc t) : accStep x acc (.eend t)  = none := rfl
@[simp] theorem accStep_retry (x acc t) : accStep x acc (.retry t) = none := rfl
@[simp] theorem accStep_adm   (x acc)   : accStep x acc .adm       = acc  := rfl
@[simp] theorem accStep_get (x acc l v t) :
    accStep x acc (.get l v t) = (if l = x then some v else acc) := rfl
@[simp] theorem accStep_set (x acc l v t) :
    accStep x acc (.set l v t) = (if l = x then some v else acc) := rfl

def sameTxLastAccess (x : Loc) (pre : List Label) : Option Nat :=
  pre.foldl (accStep x) none

/-- **Internal consistency of a trace** (`Int`).  For every read `get(x,n)@t` in
    the trace, if the same transaction already accessed `x`, the `po`-latest such
    access carries the value `n` that the read observes. -/
def IntConsistent (w : List Label) : Prop :=
  ∀ pre x n t post, w = pre ++ .get x n t :: post →
    ∀ m, sameTxLastAccess x pre = some m → m = n

/-! ## Reading off a `Get` step -/

theorem trans_get_store {C x v t C'} (h : Trans C (.get x v t) C') : C.store x = v := by
  cases h with
  | get _ _ _ hst => exact hst

/-! ## Locating a labelled step inside a trace -/

theorem Trace.locate {C w Cf} (h : Trace C w Cf) :
    ∀ {ℓ : Label} {pre post : List Label}, w = pre ++ ℓ :: post →
      ∃ Dp Dq, Trace C pre Dp ∧ Trans Dp ℓ Dq ∧ Trace Dq post Cf := by
  induction h with
  | nil => intro ℓ pre post heq; cases pre <;> simp at heq
  | @cons C ℓ₀ C₁ w' Cf tr trace ih =>
    intro ℓ pre post heq
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨C, C₁, .nil, tr, trace⟩
    | cons a pre' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, hrest⟩ := heq
      obtain ⟨Dp, Dq, h1, h2, h3⟩ := ih hrest
      exact ⟨Dp, Dq, .cons tr h1, h2, h3⟩

/-! ## Store-tracking soundness of the access fold -/

/-- One transition preserves "the accumulator agrees with the store on `x`". -/
theorem transStore {C ℓ C₁} (x : Loc) (tr : Trans C ℓ C₁) {a0 : Option Nat}
    (ha : ∀ m, a0 = some m → C.store x = m) :
    ∀ m, accStep x a0 ℓ = some m → C₁.store x = m := by
  intro m hf
  cases tr with
  | @get i H l t v hthr hlam htheta hst =>
    simp only [accStep_get] at hf
    split at hf
    · rename_i he; subst he
      simp only [Option.some.injEq] at hf; subst hf; exact hst
    · exact ha m hf
  | @set i H l t n hthr hlam htheta =>
    simp only [accStep_set] at hf
    split at hf
    · rename_i he; subst he
      simp only [Option.some.injEq] at hf; subst hf
      simp [Store.upd]
    · rename_i hne
      show (C.store.upd l n) x = m
      rw [Store.upd_other C.store l x n (fun h => hne h.symm)]
      exact ha m hf
  | begin _ _   => simp only [accStep_begin] at hf; exact absurd hf (by simp)
  | eend _ _ _  => simp only [accStep_eend]  at hf; exact absurd hf (by simp)
  | retry _ _ _ => simp only [accStep_retry] at hf; exact absurd hf (by simp)
  | adm _ _     => simp only [accStep_adm]   at hf; exact ha m hf

/-- Threaded through a trace: if the accumulator agrees with the store on `x` at
    the start, it agrees with the store at the end. -/
theorem accStep_sound {C w C'} (x : Loc) (h : Trace C w C') :
    ∀ {a0 : Option Nat}, (∀ m, a0 = some m → C.store x = m) →
      ∀ {m}, List.foldl (accStep x) a0 w = some m → C'.store x = m := by
  induction h with
  | nil => intro a0 ha m hf; simp only [List.foldl_nil] at hf; exact ha m hf
  | @cons C ℓ C₁ w' Cf tr trace ih =>
    intro a0 ha m hf
    rw [List.foldl_cons] at hf
    exact ih (transStore x tr ha) hf

/-! ## Internal consistency is sound -/

/-- **Every operational trace is internally consistent.**  This is the paper's
    `Int` axiom, discharged for the Reagent semantics. -/
theorem int_sound {E₀ : ThreadMap} {w : List Label} {C : Config}
    (h : Trace (init E₀) w C) : IntConsistent w := by
  intro pre x n t post heq m hlast
  obtain ⟨Dp, Dq, hpre, hget, _⟩ :=
    h.locate (ℓ := .get x n t) (pre := pre) (post := post) heq
  have hv : Dp.store x = n := trans_get_store hget
  have hm : Dp.store x = m :=
    accStep_sound x hpre (a0 := none) (by intro m' hc; simp at hc) hlast
  rw [hv] at hm
  exact hm.symm

end Reagent
