/-
  The Reagent language: abstract syntax and configurations.

  This mechanizes Section "Abstract syntax" and Section "Semantics" of
  `docs/reagent-correctness.tex`.  A configuration is the six-tuple

        C = ⟨ σ , λ , θ , E , σ̂ , Ê ⟩

  of that document, where `λ` names the *thread* that holds the lock and `θ`
  the live *transaction* id.
-/

namespace Reagent

/-- Shared mutable locations `l ∈ Loc`. -/
abbrev Loc : Type := Nat
/-- Transaction identifiers `t ∈ TxId` (the token of the live transaction). -/
abbrev TxId : Type := Nat
/-- Thread identifiers `i ∈ ThId` (the scheduled thread). -/
abbrev ThId : Type := Nat

/-- Values: naturals, unit, and booleans (`v ::= n ∣ () ∣ true ∣ false`). -/
inductive Val where
  | nat  : Nat → Val
  | unit : Val
  | bool : Bool → Val
deriving DecidableEq, Repr

/-- Expressions and commands of the Reagent language.

    Commands (`get`, `set`, `begin`, `end`, `retry`) are folded into the
    expression grammar exactly as in the paper: a command is an expression,
    not a separate control-flow syntactic class. -/
inductive Expr where
  | val   : Val → Expr                        -- values v
  | var   : String → Expr                     -- immutable let-bound variables x
  | add   : Expr → Expr → Expr                -- e₁ + e₂
  | eq    : Expr → Expr → Expr                -- e₁ == e₂
  | lett  : String → Expr → Expr → Expr       -- let x = e₁ in e₂
  | seq   : Expr → Expr → Expr                -- e₁ ; e₂
  | ite   : Expr → Expr → Expr → Expr         -- if e then e else e
  | get   : Loc → Expr                        -- get(l)
  | set   : Loc → Expr → Expr                 -- set(l, e)
  | begin : Expr                              -- begin
  | eend  : Expr                              -- end
  | retry : Expr                              -- retry
deriving DecidableEq, Repr

namespace Expr

/-- Capture-avoiding substitution `e[x ↦ v]`.  Values are closed, so plain
    structural substitution suffices; `let` shadows its own binder. -/
def subst : Expr → String → Val → Expr
  | .val w,      _, _ => .val w
  | .var y,      x, v => if y = x then .val v else .var y
  | .add a b,    x, v => .add (a.subst x v) (b.subst x v)
  | .eq a b,     x, v => .eq (a.subst x v) (b.subst x v)
  | .lett y a b, x, v => .lett y (a.subst x v) (if y = x then b else b.subst x v)
  | .seq a b,    x, v => .seq (a.subst x v) (b.subst x v)
  | .ite a b c,  x, v => .ite (a.subst x v) (b.subst x v) (c.subst x v)
  | .get l,      _, _ => .get l
  | .set l a,    x, v => .set l (a.subst x v)
  | .begin,      _, _ => .begin
  | .eend,       _, _ => .eend
  | .retry,      _, _ => .retry

end Expr

/-- A store `σ : Loc → ℕ` maps each shared location to a natural number. -/
abbrev Store : Type := Loc → Nat

namespace Store

/-- The all-zero initial store `σ₀`. -/
def zero : Store := fun _ => 0

/-- Point update `σ[l ↦ n]`. -/
def upd (σ : Store) (l : Loc) (n : Nat) : Store :=
  fun l' => if l' = l then n else σ l'

@[simp] theorem upd_same (σ : Store) (l : Loc) (n : Nat) : upd σ l n l = n := by
  simp [upd]

@[simp] theorem upd_other (σ : Store) (l l' : Loc) (n : Nat) (h : l' ≠ l) :
    upd σ l n l' = σ l' := by
  simp [upd, h]

end Store

/-- A thread map `E : ThId ⇀ Expr` sending each active thread to the
    expression it is currently evaluating.  A missing thread is `none`. -/
abbrev ThreadMap : Type := ThId → Option Expr

namespace ThreadMap

/-- Point update `E[i ↦ e]`. -/
def upd (E : ThreadMap) (i : ThId) (e : Expr) : ThreadMap :=
  fun j => if j = i then some e else E j

@[simp] theorem upd_same (E : ThreadMap) (i : ThId) (e : Expr) : upd E i e i = some e := by
  simp [upd]

@[simp] theorem upd_other (E : ThreadMap) (i j : ThId) (e : Expr) (h : j ≠ i) :
    upd E i e j = E j := by
  simp [upd, h]

end ThreadMap

/-- A configuration is the six-tuple `⟨σ, λ, θ, E, σ̂, Ê⟩`:

    * `store`  – shared store `σ`;
    * `lam`    – the *thread* `i` that currently holds the lock / owns the live
      transaction (`none` is `⊥`, no owner).  Every transactional rule requires
      `λ = i` for the acting thread `i`, so only the owner may step inside its
      transaction;
    * `theta`  – the *transaction* id `θ` of the live transaction, minted fresh
      by each `begin` (`none` is `⊥`).  It supplies the tag on emitted actions;
    * `threads`– thread map `E`;
    * `snap`   – snapshot `σ̂` of the store taken when the transaction began;
    * `saved`  – saved body `Ê` from which a `retry` resumes.

    Invariant maintained by the rules: `λ = ⊥ ↔ θ = ⊥` (owner and live
    transaction are set together by `begin` and cleared together by
    `end`/`retry`). -/
structure Config where
  store   : Store
  lam     : Option ThId
  theta   : Option TxId
  threads : ThreadMap
  snap    : Store
  saved   : Expr

/-- The termination condition of the paper: every active thread is at `()`.
    (We keep it as a predicate; there is no distinguished terminal state.) -/
def Config.terminated (C : Config) (dom : List ThId) : Prop :=
  ∀ i ∈ dom, C.threads i = some (.val .unit)

end Reagent
