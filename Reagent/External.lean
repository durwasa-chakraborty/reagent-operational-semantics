/-
  External consistency for Reagent V1 (Section "External consistency").

  An external get — a transaction's first access to `x` is a read — must return
  the value the `AR`-latest committed setter left in `x`, or the initial `0` if
  there is none.  We track that committed value with a forward fold `lcs`
  (last-committed-setter): a `set` on `x` is tentative until the transaction's
  `end` commits it; a transaction that never ends never contributes.  We prove
  the operational store agrees with this fold, and hence an external read returns
  the committed value.

  (With no `retry`, a transaction can only fail to commit by being *pending*.
  While it is pending it holds the lock, so no other transaction runs — an
  external read therefore never sees an uncommitted write.)
-/
import Reagent.Consistency

namespace Reagent

/-- Fold state `(c, cur)`: `c` is the committed value of `x`; `cur` is the
    current transaction's last set of `x` (`none` if it has not set `x`, or
    outside a transaction).  `end` commits `cur`; `begin` clears it. -/
def lcsStep (x : Loc) (s : Nat × Option Nat) : Label → Nat × Option Nat
  | .begin _    => (s.1, none)
  | .set x' v _ => if x' = x then (s.1, some v) else s
  | .eend _     => match s.2 with
                   | some v => (v, none)
                   | none   => (s.1, none)
  | .get _ _ _  => s

/-- The committed value of `x` after the trace `w` (the value left by the
    `AR`-latest committed setter of `x`, or `0`). -/
def lcs (x : Loc) (w : List Label) : Nat := (w.foldl (lcsStep x) (0, none)).1

/-- The fold state a configuration should carry:
    `σ(x)` equals `cur` if the live transaction has written `x`, else the
    committed value `c`; and outside a transaction there is no pending `cur`. -/
def lenc (C : Config) (x : Loc) (s : Nat × Option Nat) : Prop :=
  C.store x = s.2.getD s.1 ∧ (C.lam = none → s.2 = none)

/-- One transition updates the fold state exactly as `lenc` prescribes. -/
theorem lcstep_enc {C ℓ C₁ x} {s : Nat × Option Nat} (tr : Trans C ℓ C₁)
    (h : lenc C x s) : lenc C₁ x (lcsStep x s ℓ) := by
  obtain ⟨c, cur⟩ := s
  obtain ⟨hstore, hlamnone⟩ := h
  cases tr with
  | @begin i t e hthr hlam =>
    have hcur : cur = none := hlamnone hlam
    subst hcur
    refine ⟨?_, ?_⟩
    · simpa [lcsStep] using hstore
    · intro _; rfl
  | @get i l t v e hthr hlam htheta hst =>
    exact ⟨hstore, hlamnone⟩
  | @set i l n t e hthr hlam htheta =>
    by_cases hlx : l = x
    · subst hlx
      refine ⟨?_, ?_⟩
      · simp [lcsStep, update]
      · intro hnone; rw [hlam] at hnone; exact absurd hnone (by simp)
    · refine ⟨?_, ?_⟩
      · simp only [lcsStep, if_neg hlx]
        show (update C.store l n) x = cur.getD c
        rw [update_other C.store l x n hlx]; exact hstore
      · intro hnone; rw [hlam] at hnone; exact absurd hnone (by simp)
  | @eend i t e hthr hlam htheta =>
    refine ⟨?_, ?_⟩
    · cases cur with
      | none   => simpa [lcsStep] using hstore
      | some v => simpa [lcsStep] using hstore
    · intro _; cases cur <;> rfl

/-- `lenc` holds at the initial configuration with the empty fold state. -/
theorem lenc_init (E₀ : ThreadMap) (x : Loc) : lenc (init E₀) x (0, none) := by
  refine ⟨?_, ?_⟩
  · simp [init, Store.init_store]
  · intro _; rfl

/-- `lenc` is preserved along a trace. -/
theorem lenc_fold {C w C'} (x : Loc) (h : Trace C w C') :
    ∀ s, lenc C x s → lenc C' x (List.foldl (lcsStep x) s w) := by
  induction h with
  | nil => intro s hs; exact hs
  | @cons C ℓ C₁ w' Cf tr trace ih =>
    intro s hs
    rw [List.foldl_cons]
    exact ih _ (lcstep_enc tr hs)

/-- **External consistency of a trace** (`Ext`).  An external get — one whose
    transaction has not yet written `x` (`(fold pre).2 = none`) — returns the
    committed value `lcs x pre`: the value left by the `AR`-latest committed
    setter of `x`, or `0`. -/
def ExtConsistent (w : List Label) : Prop :=
  ∀ pre x n t post, w = pre ++ .get x n t :: post →
    (List.foldl (lcsStep x) (0, none) pre).2 = none →
    n = lcs x pre

/-- **Every V1 trace is externally consistent.** -/
theorem ext_sound {E₀ : ThreadMap} {w : List Label} {C : Config}
    (h : Trace (init E₀) w C) : ExtConsistent w := by
  intro pre x n t post heq hext
  obtain ⟨Dp, Dq, hpre, hget, _⟩ :=
    h.locate (ℓ := .get x n t) (pre := pre) (post := post) heq
  have hn : Dp.store x = n := trans_get_store hget
  obtain ⟨hst, _⟩ := lenc_fold x hpre _ (lenc_init E₀ x)
  rw [hext] at hst
  simp only [Option.getD_none] at hst
  rw [hn] at hst
  exact hst

/-! ## What the committed value is made of

    A structural fact pinning down `lcs`: a committed attempt
    `begin@t · body · end@t` (with `body` a boundary-free block — no nested
    `begin`/`end`) sets the committed value of `x` to the block's `po`-last write
    to `x` (`0` if it never writes `x`).  This is what makes `lcs x pre` in
    `ext_sound` genuinely "the committed setter's value". -/

/-- A block with no transaction boundaries (a transaction body). -/
def Boundaryless (body : List Label) : Prop :=
  ∀ ℓ ∈ body, ℓ.isBegin = false ∧ ℓ.isEnd = false

/-- The pending-set component after a boundary-free block: the block's last write
    to `x`, starting from `cur`. -/
def curFold (x : Loc) (cur : Option Nat) : List Label → Option Nat
  | []                  => cur
  | .set x' v _ :: rest => curFold x (if x' = x then some v else cur) rest
  | _ :: rest           => curFold x cur rest

/-- Folding a boundary-free block keeps the committed value `c` and tracks its
    last write to `x` in the pending component. -/
theorem lcs_body (x : Loc) :
    ∀ (body : List Label), Boundaryless body → ∀ (c : Nat) (cur : Option Nat),
      List.foldl (lcsStep x) (c, cur) body = (c, curFold x cur body) := by
  intro body
  induction body with
  | nil => intro _ c cur; rfl
  | cons ℓ rest ih =>
    intro hb c cur
    obtain ⟨hbeg, hend⟩ := hb ℓ (List.mem_cons_self ..)
    have hb' : Boundaryless rest := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    cases ℓ with
    | begin t => simp [Label.isBegin] at hbeg
    | eend t  => simp [Label.isEnd]  at hend
    | get l v t => simpa [lcsStep, curFold] using ih hb' c cur
    | set l v t =>
      by_cases hlx : l = x
      · subst hlx; simpa [lcsStep, curFold] using ih hb' c (some v)
      · simpa [lcsStep, curFold, hlx] using ih hb' c cur

/-- **A committed transaction commits its `po`-last write.**  The committed value
    of `x` after `begin@t · body · end@t` is the block's last write to `x`, or
    the prior committed value `0` if it never writes `x`. -/
theorem lcs_commit (x : Loc) (t : TxId) (body : List Label) (hb : Boundaryless body) :
    lcs x (.begin t :: (body ++ [.eend t])) = (curFold x none body).getD 0 := by
  simp only [lcs, List.foldl_cons, List.foldl_append]
  have hbegin : lcsStep x (0, none) (.begin t) = (0, none) := rfl
  rw [hbegin, lcs_body x body hb 0 none]
  cases h : curFold x none body with
  | none   => simp [lcsStep]
  | some v => simp [lcsStep]

end Reagent
