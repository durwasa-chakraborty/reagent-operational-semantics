/-
  Reagent — full core language.

  Abstract syntax, evaluation contexts, and configurations, following
  `docs/reagent-correctness.tex` §Abstract syntax and §Evaluation contexts.

  Commands are expressions (`e ::= … | c`), so there is no separate `Cmd` type:
  `set(l, e)` takes an *expression* argument, which the context `set(l, ECtx)`
  evaluates to a value before `Set` may fire.

  Configurations are the document's six-tuple `⟨σ, λ, θ, E, σ̂, Ê⟩` — `retry`
  needs the snapshot `σ̂` to roll the store back and the saved body `Ê` to
  re-run — together with the counter that mints fresh transaction ids.
-/

namespace Reagent

/-- Shared mutable locations. -/
abbrev Loc  : Type := Nat
/-- Transaction identifiers. -/
abbrev TxId : Type := Nat
/-- Thread identifiers. -/
abbrev ThId : Type := Nat
/-- Immutable, `let`-bound variables. -/
abbrev Var  : Type := Nat
/-- The shared store `σ : Loc → ℕ`. -/
abbrev Store : Type := Loc → Nat

/-- Values `v ::= n | () | true | false`. -/
inductive Val where
  | num  : Nat → Val
  | unit : Val
  | bool : Bool → Val
deriving DecidableEq, Repr

/-- Expressions

`e ::= v | x | e₁ + e₂ | e₁ == e₂ | let x = e₁ in e₂ | if e then e₁ else e₂
     | e₁ ; e₂ | get(l) | set(l,e) | begin | end | retry`

The last five are the commands `c`, which the grammar folds into `e`. The store
is ℕ-valued, so only a `num` may be written by `set`. -/
inductive Expr where
  | val   : Val → Expr                    -- v
  | var   : Var → Expr                    -- x
  | add   : Expr → Expr → Expr            -- e₁ + e₂
  | eqv   : Expr → Expr → Expr            -- e₁ == e₂
  | letx  : Var → Expr → Expr → Expr      -- let x = e₁ in e₂
  | ite   : Expr → Expr → Expr → Expr     -- if e then e₁ else e₂
  | seq   : Expr → Expr → Expr            -- e₁ ; e₂
  | getc  : Loc → Expr                    -- get(l)
  | setc  : Loc → Expr → Expr             -- set(l, e)
  | begin : Expr                          -- begin
  | eend  : Expr                          -- end
  | retry : Expr                          -- retry
deriving DecidableEq, Repr

/-- Substitution `e[v/x]`, used by the `let` reduction. Substituting a *value*
means there is nothing to capture, so the only care needed is shadowing: a
`let` that rebinds `x` stops the substitution in its body. -/
def Expr.subst (x : Var) (v : Val) : Expr → Expr
  | .val w      => .val w
  | .var y      => if y = x then .val v else .var y
  | .add a b    => .add (a.subst x v) (b.subst x v)
  | .eqv a b    => .eqv (a.subst x v) (b.subst x v)
  | .letx y a b => .letx y (a.subst x v) (if y = x then b else b.subst x v)
  | .ite c a b  => .ite (c.subst x v) (a.subst x v) (b.subst x v)
  | .seq a b    => .seq (a.subst x v) (b.subst x v)
  | .getc l     => .getc l
  | .setc l a   => .setc l (a.subst x v)
  | .begin      => .begin
  | .eend       => .eend
  | .retry      => .retry

/-- Evaluation contexts

`ECtx ::= [·] | ECtx ; e | let x = ECtx in e | ECtx + e | v + ECtx | ECtx == e | v == ECtx
     | if ECtx then e else e | set(l, ECtx)`

an expression with a single hole marking where the next reduction happens.
Named `Ctx`, kept deliberately apart from `E : ThreadMap` — the two are distinct
objects. The `v + ECtx` and `v == ECtx` forms are what make evaluation left-to-right:
the right operand is reached only once the left is a value. -/
inductive Ctx where
  | hole  : Ctx                           -- [·]
  | seq   : Ctx → Expr → Ctx              -- ECtx ; e
  | letx  : Var → Ctx → Expr → Ctx        -- let x = ECtx in e
  | addL  : Ctx → Expr → Ctx              -- ECtx + e
  | addR  : Val → Ctx → Ctx               -- v + ECtx
  | eqL   : Ctx → Expr → Ctx              -- ECtx == e
  | eqR   : Val → Ctx → Ctx               -- v == ECtx
  | ite   : Ctx → Expr → Expr → Ctx       -- if ECtx then e₁ else e₂
  | setc  : Loc → Ctx → Ctx               -- set(l, ECtx)
deriving DecidableEq, Repr

/-- `ECtx[e]`: plug `e` into the hole. -/
def Ctx.plug : Ctx → Expr → Expr
  | .hole,        e => e
  | .seq K e',    e => .seq (K.plug e) e'
  | .letx x K e', e => .letx x (K.plug e) e'
  | .addL K e',   e => .add (K.plug e) e'
  | .addR v K,    e => .add (.val v) (K.plug e)
  | .eqL K e',    e => .eqv (K.plug e) e'
  | .eqR v K,     e => .eqv (.val v) (K.plug e)
  | .ite K e₁ e₂, e => .ite (K.plug e) e₁ e₂
  | .setc l K,    e => .setc l (K.plug e)

/-- A thread map `E : ThId → Expr`. -/
abbrev ThreadMap : Type := ThId → Expr

/-- Pointwise update `f[a ↦ b]`. -/
def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a' = a then b else f a'

@[simp] theorem update_other {α β : Type} [DecidableEq α] (f : α → β) (a a' : α)
    (b : β) (hne : a ≠ a') : update f a b a' = f a' := by
  simp [update, hne.symm]

/-- The all-zero initial store `σ₀`. -/
def Store.init_store : Store := fun _ => 0

/-- A configuration `⟨σ, λ, θ, E, σ̂, Ê⟩` together with the freshness counter:

* `store`        – the shared store `σ`;
* `activeThread` – `λ`, the thread holding the lock (`none` is `⊥`);
* `activeTx`     – `θ`, the live transaction id (`none` is `⊥`);
* `threadMap`    – the thread map `E`;
* `snapshot`     – `σ̂`, the store as it was when the live transaction began;
* `savedBody`    – `Ê`, the body to re-run after an abort;
* `nextTx`       – the id `Begin` mints next.

The rules maintain `activeThread = ⊥ ↔ activeTx = ⊥`. `Begin` records `σ̂` and
`Ê`; `Retry` rolls the store back to `σ̂` and re-arms the thread as `begin ; Ê`.

`nextTx` is how the `t_fresh` premise of `Begin` is realised: no id is ever
reused. That is not decoration — internal consistency is false without it, since
a reused id would splice two unrelated attempts into one "transaction" whose
read contradicts its own earlier write. It is also what keeps a retried attempt
a *separate* transaction from the attempt it replaces. -/
structure Config where
  store        : Store          -- σ
  activeThread : Option ThId    -- λ
  activeTx     : Option TxId    -- θ
  threadMap    : ThreadMap      -- E
  snapshot     : Store          -- σ̂
  savedBody    : Expr           -- Ê
  nextTx       : TxId

end Reagent
