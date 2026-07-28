/-
  Internal consistency for Reagent V1 (Section "Internal consistency").

  We prove that every trace of the operational semantics satisfies `Int`: for
  every read `get(x,n)@t`, if the same transaction already accessed `x`, the
  program-order-latest such access carries `n`.

  Proof: a store-tracking induction.  Within a transaction the store on `x`
  equals the value of the latest earlier access to `x`, because the single lock
  isolates the transaction and (with no `retry`) nothing rolls the store back.
-/
import Reagent.Trace

namespace Reagent

/-- Latest same-transaction access value on `x`, resetting at each transaction
    boundary (`begin`, `end`).  Because the single lock makes the segment since
    the last `begin` exactly the current transaction's events, this is the
    `max_po(po⁻¹(e) ∩ HEvent_x)` value of the paper's `Int`. -/
def accStep (x : Loc) (acc : Option Nat) : Label → Option Nat
  | .begin _    => none
  | .eend _     => none
  | .get x' v _ => if x' = x then some v else acc
  | .set x' v _ => if x' = x then some v else acc

@[simp] theorem accStep_begin (x acc t) : accStep x acc (.begin t) = none := rfl
@[simp] theorem accStep_eend  (x acc t) : accStep x acc (.eend t)  = none := rfl
@[simp] theorem accStep_get (x acc l v t) :
    accStep x acc (.get l v t) = (if l = x then some v else acc) := rfl
@[simp] theorem accStep_set (x acc l v t) :
    accStep x acc (.set l v t) = (if l = x then some v else acc) := rfl

def sameTxLastAccess (x : Loc) (pre : List Label) : Option Nat :=
  pre.foldl (accStep x) none

/-- **Internal consistency of a trace** (`Int`). -/
def IntConsistent (w : List Label) : Prop :=
  ∀ pre x n t post, w = pre ++ .get x n t :: post →
    ∀ m, sameTxLastAccess x pre = some m → m = n

/-- A `Get` transition reads exactly the current store. -/
theorem trans_get_store {C x v t C'} (h : Trans C (.get x v t) C') : C.store x = v := by
  cases h with
  | get _ _ _ hst => exact hst

/-- Locating a labelled step inside a trace. -/
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

/-- One transition preserves "the accumulator agrees with the store on `x`". -/
theorem transStore {C ℓ C₁} (x : Loc) (tr : Trans C ℓ C₁) {a0 : Option Nat}
    (ha : ∀ m, a0 = some m → C.store x = m) :
    ∀ m, accStep x a0 ℓ = some m → C₁.store x = m := by
  intro m hf
  cases tr with
  | @get i l t v e hthr hlam htheta hst =>
    simp only [accStep_get] at hf
    split at hf
    · rename_i he; subst he
      simp only [Option.some.injEq] at hf; subst hf; exact hst
    · exact ha m hf
  | @set i l n t e hthr hlam htheta =>
    simp only [accStep_set] at hf
    split at hf
    · rename_i he; subst he
      simp only [Option.some.injEq] at hf; subst hf
      simp [update]
    · rename_i hne
      show (update C.store l n) x = m
      rw [update_other C.store l x n hne]
      exact ha m hf
  | begin _ _   => simp only [accStep_begin] at hf; exact absurd hf (by simp)
  | eend _ _ _  => simp only [accStep_eend]  at hf; exact absurd hf (by simp)

/-- Threaded through a trace. -/
theorem accStep_sound {C w C'} (x : Loc) (h : Trace C w C') :
    ∀ {a0 : Option Nat}, (∀ m, a0 = some m → C.store x = m) →
      ∀ {m}, List.foldl (accStep x) a0 w = some m → C'.store x = m := by
  induction h with
  | nil => intro a0 ha m hf; simp only [List.foldl_nil] at hf; exact ha m hf
  | @cons C ℓ C₁ w' Cf tr trace ih =>
    intro a0 ha m hf
    rw [List.foldl_cons] at hf
    exact ih (transStore x tr ha) hf

/-- **Every V1 trace is internally consistent.** -/
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
