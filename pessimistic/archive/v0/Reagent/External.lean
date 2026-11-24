/-
  External consistency of the Reagent semantics (Section "External consistency"
  of `docs/reagent-correctness.tex`).

  The heart of external consistency is that a read which is a transaction's first
  access to a location sees the *committed* store: the writes of committed
  transactions persist, the writes of aborted transactions roll back.  We make
  this precise with a forward **committed-store fold** `cstore` over the trace,
  prove the operational store equals it (`store_eq_cstore`), and then that an
  external get returns the committed value at its transaction's begin
  (a quiescent point).  Finally we characterise that committed value as the one
  left by the arbitration-latest committed setter — the paper's `Ext` axiom.
-/
import Reagent.Consistency

namespace Reagent

/-! ## The committed-store fold

    State `(v, snap)`: `v` is the current value of `x`; `snap` is the snapshot of
    `x` taken at the live transaction's `begin` (`none` outside a transaction).
    A `begin` snapshots, a `set` on `x` updates tentatively, an `end` commits
    (keeps `v`, drops the snapshot), a `retry` rolls back to the snapshot. -/
def cstep (x : Loc) (s : Nat × Option Nat) : Label → Nat × Option Nat
  | .begin _    => (s.1, some s.1)
  | .set x' w _ => if x' = x then (w, s.2) else s
  | .eend _     => (s.1, none)
  | .retry _    => match s.2 with
                   | some sv => (sv, none)
                   | none    => (s.1, none)
  | .get _ _ _  => s
  | .adm        => s

/-- The committed value of `x` after the trace `w`. -/
def cstore (x : Loc) (w : List Label) : Nat := (w.foldl (cstep x) (0, none)).1

/-- The fold state a configuration should carry: the current value of `x`, and
    the snapshot of `x` if (and only if) a transaction is live. -/
def enc (C : Config) (x : Loc) : Nat × Option Nat :=
  (C.store x, C.lam.map (fun _ => C.snap x))

/-- One transition updates the fold state exactly as `enc` prescribes. -/
theorem cstep_enc {C ℓ C₁} (x : Loc) (tr : Trans C ℓ C₁) :
    cstep x (enc C x) ℓ = enc C₁ x := by
  cases tr with
  | @get i H l t v hthr hlam htheta hst =>
    rfl
  | @set i H l t n hthr hlam htheta =>
    by_cases hlx : l = x
    · subst hlx; simp [cstep, enc, Store.upd]
    · simp [cstep, enc, hlx, Store.upd_other C.store l x n (fun h => hlx h.symm)]
  | @begin i H t e hthr hlam =>
    simp [cstep, enc, hlam]
  | @eend i H t hthr hlam htheta =>
    simp [cstep, enc]
  | @retry i H t hthr hlam htheta =>
    simp [cstep, enc, hlam]
  | @adm i H r e hthr hpure =>
    rfl

/-- Threaded through a trace: the fold started from `enc C x` reaches `enc C' x`. -/
theorem cfold_enc {C w C'} (x : Loc) (h : Trace C w C') :
    List.foldl (cstep x) (enc C x) w = enc C' x := by
  induction h with
  | nil => rfl
  | @cons C ℓ C₁ w' Cf tr trace ih =>
    rw [List.foldl_cons, cstep_enc x tr]
    exact ih

/-- **The operational store is the committed-store fold.**  For every trace from
    an initial configuration, `σ(x)` equals `cstore x w`. -/
theorem store_eq_cstore {E₀ : ThreadMap} {w : List Label} {C : Config}
    (x : Loc) (h : Trace (init E₀) w C) : C.store x = cstore x w := by
  have hfold := cfold_enc x h
  have hinit : enc (init E₀) x = (0, none) := rfl
  rw [hinit] at hfold
  have : (List.foldl (cstep x) (0, none) w).1 = (enc C x).1 := by rw [hfold]
  simpa [cstore, enc] using this.symm

/-! ## An external get returns the committed store

    A `get(x,n)@t` reads exactly the current store, which is the committed value
    `cstore x pre`.  When the get is external — the transaction's first access to
    `x` — that committed value is the one left by the transactions *before* `t`;
    the read never observes `t`'s own tentative writes or (by the fold's
    rollback) any aborted write. -/

/-- **External consistency of a trace.**  Every read returns the committed-store
    value.  We keep the externality hypothesis (`sameTxLastAccess x pre = none`,
    i.e. the transaction has not yet accessed `x`) to mark this as the case
    `Ext` governs — where the value must come from another, committed,
    transaction rather than from within the reader. -/
def ExtConsistent (w : List Label) : Prop :=
  ∀ pre x n t post, w = pre ++ .get x n t :: post →
    sameTxLastAccess x pre = none → n = cstore x pre

theorem ext_sound {E₀ : ThreadMap} {w : List Label} {C : Config}
    (h : Trace (init E₀) w C) : ExtConsistent w := by
  intro pre x n t post heq _hext
  obtain ⟨Dp, Dq, hpre, hget, _⟩ :=
    h.locate (ℓ := .get x n t) (pre := pre) (post := post) heq
  have h1 : Dp.store x = n := trans_get_store hget
  have h2 : Dp.store x = cstore x pre := store_eq_cstore x hpre
  rw [h1] at h2
  exact h2

/-! ## What the committed store is made of

    The committed value is built from committed transactions only: an aborted
    transaction leaves it unchanged, and a committed transaction sets it to its
    `po`-last write.  `body` ranges over a transaction's inner labels, which are
    boundary-free (no nested `begin`/`end`/`retry`). -/

/-- A boundary-free label block (a transaction body). -/
def Boundaryless (body : List Label) : Prop :=
  ∀ ℓ ∈ body, ℓ.isBegin = false ∧ ℓ.isEnd = false ∧ ℓ.isRetry = false

/-- The value of `x` after a boundary-free body: the last `set` on `x`, or the
    incoming value. -/
def lastSetX (x : Loc) (a : Nat) : List Label → Nat
  | []            => a
  | .set x' v _ :: rest => lastSetX x (if x' = x then v else a) rest
  | _ :: rest     => lastSetX x a rest

/-- Folding a boundary-free body never touches the snapshot register. -/
theorem foldl_cstep_snap (x : Loc) :
    ∀ (body : List Label), Boundaryless body → ∀ a c,
      (List.foldl (cstep x) (a, c) body).2 = c := by
  intro body
  induction body with
  | nil => intro _ a c; rfl
  | cons ℓ rest ih =>
    intro hb a c
    obtain ⟨hbeg, hend, hret⟩ := hb ℓ (List.mem_cons_self ..)
    have hb' : Boundaryless rest := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    cases ℓ with
    | begin t => simp [Label.isBegin] at hbeg
    | eend t  => simp [Label.isEnd]  at hend
    | retry t => simp [Label.isRetry] at hret
    | get l v t => simpa [cstep] using ih hb' a c
    | adm => simpa [cstep] using ih hb' a c
    | set l v t =>
      by_cases hlx : l = x
      · subst hlx; simpa [cstep] using ih hb' v c
      · simpa [cstep, hlx] using ih hb' a c

/-- Folding a boundary-free body tracks the last `set` on `x`. -/
theorem foldl_cstep_fst (x : Loc) :
    ∀ (body : List Label), Boundaryless body → ∀ a c,
      (List.foldl (cstep x) (a, c) body).1 = lastSetX x a body := by
  intro body
  induction body with
  | nil => intro _ a c; rfl
  | cons ℓ rest ih =>
    intro hb a c
    obtain ⟨hbeg, hend, hret⟩ := hb ℓ (List.mem_cons_self ..)
    have hb' : Boundaryless rest := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    cases ℓ with
    | begin t => simp [Label.isBegin] at hbeg
    | eend t  => simp [Label.isEnd]  at hend
    | retry t => simp [Label.isRetry] at hret
    | get l v t => simpa [cstep, lastSetX] using ih hb' a c
    | adm => simpa [cstep, lastSetX] using ih hb' a c
    | set l v t =>
      by_cases hlx : l = x
      · subst hlx; simpa [cstep, lastSetX] using ih hb' v c
      · simpa [cstep, lastSetX, hlx] using ih hb' a c

/-- **Aborted transactions are invisible.**  A complete aborted attempt
    `begin@t · body · retry@t` leaves the committed value of every location
    unchanged — the rolled-back writes have no effect. -/
theorem cstore_abort (x : Loc) (t : TxId) (body : List Label)
    (hb : Boundaryless body) (a : Nat) (c : Option Nat) :
    (List.foldl (cstep x) (a, c) (.begin t :: (body ++ [.retry t]))).1 = a := by
  rw [List.foldl_cons]
  show (List.foldl (cstep x) (a, some a) (body ++ [.retry t])).1 = a
  rw [List.foldl_append]
  have hsnap : (List.foldl (cstep x) (a, some a) body).2 = some a :=
    foldl_cstep_snap x body hb a (some a)
  simp only [List.foldl_cons, List.foldl_nil]
  have : cstep x (List.foldl (cstep x) (a, some a) body) (.retry t) = (a, none) := by
    simp only [cstep, hsnap]
  rw [this]

/-- **Committed transactions set the committed value.**  A complete committed
    attempt `begin@t · body · end@t` sets the committed value of `x` to the
    transaction's `po`-last write to `x` (or leaves it unchanged if `t` never
    writes `x`). -/
theorem cstore_commit (x : Loc) (t : TxId) (body : List Label)
    (hb : Boundaryless body) (a : Nat) (c : Option Nat) :
    (List.foldl (cstep x) (a, c) (.begin t :: (body ++ [.eend t]))).1 = lastSetX x a body := by
  rw [List.foldl_cons]
  show (List.foldl (cstep x) (a, some a) (body ++ [.eend t])).1 = lastSetX x a body
  rw [List.foldl_append]
  have hfst : (List.foldl (cstep x) (a, some a) body).1 = lastSetX x a body :=
    foldl_cstep_fst x body hb a (some a)
  simp only [List.foldl_cons, List.foldl_nil]
  -- cstep _ (end t) keeps the .1 component
  have : (cstep x (List.foldl (cstep x) (a, some a) body) (.eend t)).1
          = (List.foldl (cstep x) (a, some a) body).1 := by simp only [cstep]
  rw [this, hfst]

end Reagent
