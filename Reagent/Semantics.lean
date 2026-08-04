/-
  Operational semantics of Reagent (Figure "Semantics of Reagent commands",
  §Local (pure) reductions, and §Lifting local reductions).

  Every rule fires on the redex the active thread's evaluation context `ECtx`
  locates, and rewrites it in place, framing the rest of the thread map. The
  transactional rules (Get / Set / End / Retry) carry `λ = i` — only the thread
  that owns the live transaction may step inside it — and `θ = t`, which
  supplies the tag on the emitted label.

  The pure forms (`+`, `==`, `let`, `if`, and discarding a leading `()`) never
  touch the store or the transaction state. They are given as a separate
  relation `⇝` on redexes and lifted into the transition system by `Local`,
  which labels them `ℓ_adm`.
-/
import Reagent.Syntax

namespace Reagent

/-- Transition labels: the events a transaction performs. -/
inductive Label where
  | begin : TxId → Label
  | get   : Loc → Nat → TxId → Label
  | set   : Loc → Nat → TxId → Label
  | eend  : TxId → Label
  | retry : TxId → Label
deriving DecidableEq, Repr

/-- A trace label is *either* a transition label *or* an administrative step
`ℓ_adm` (Definition "Trace"). The distinction matters downstream: administrative
steps are trace labels but **not** events, so they are not members of any
transaction's `E`. -/
inductive TLabel where
  | ev  : Label → TLabel
  | adm : TLabel
deriving DecidableEq, Repr

/-- Local (pure) reductions `r ⇝ e` on redexes, independent of the six-tuple
(§Local (pure) reductions, §Administrative reductions).

`eqv` is the one rule the document does not state: it gives evaluation contexts
`ECtx == e` and `v == ECtx` and uses `==` in its worked example, but lists no
reduction for it, so the obvious one is supplied here. -/
inductive Local : Expr → Expr → Prop where
  | add {n₁ n₂} :
      Local (.add (.val (.num n₁)) (.val (.num n₂))) (.val (.num (n₁ + n₂)))
  | eqv {v₁ v₂} :
      Local (.eqv (.val v₁) (.val v₂)) (.val (.bool (decide (v₁ = v₂))))
  | letv {x v e} :
      Local (.letx x (.val v) e) (e.subst x v)
  | ifTrue {e₁ e₂} :
      Local (.ite (.val (.bool true)) e₁ e₂) e₁
  | ifFalse {e₁ e₂} :
      Local (.ite (.val (.bool false)) e₁ e₂) e₂
  | seqUnit {e} :
      Local (.seq (.val .unit) e) e

/-- The command rules in context form, together with `Local`.

`Begin`'s redex is `begin ; e`: the `begin` becomes `()` in place, leaving
`ECtx[() ; e]`, and the continuation `e` is saved as `Ê` — exactly the body
`Retry` reinstates. It mints `C.nextTx` as the document's `t_fresh`, bumps the
counter, and snapshots the store.

`Get` reduces to the value read, `ECtx[v]`, so a surrounding `let x = get(l) in …`
can consume it. `Set`'s redex is `set(l,v)` with `v` already a value — the
context `set(l, ECtx)` is what evaluates the argument — and it reduces to `()`.

`Retry` is lock releasing: it rolls the store back to `σ̂`, clears `λ` and `θ`
so another thread may `begin`, and re-arms the thread as `ECtx[begin ; Ê]`, so the
retried attempt must re-acquire the lock and runs under a *fresh* id.

`Local` lifts `⇝` to an `ℓ_adm`-labelled step. It leaves `σ`, `λ`, `θ`, `σ̂`
and `Ê` untouched and carries no `λ = i` premise: any thread may take a pure
step, inside a transaction or not. -/
inductive Trans : Config → TLabel → Config → Prop where
  | begin {C i e} {K : Ctx} :
      C.threadMap i = K.plug (.seq .begin e) →
      C.activeThread = none →
      Trans C (.ev (.begin C.nextTx))
        { C with activeThread := some i, activeTx := some C.nextTx,
                 nextTx := C.nextTx + 1,
                 snapshot := C.store, savedBody := e,
                 threadMap := update C.threadMap i (K.plug (.seq (.val .unit) e)) }
  | get {C i l v t} {K : Ctx} :
      C.threadMap i = K.plug (.getc l) →
      C.activeThread = some i →
      C.activeTx = some t →
      C.store l = v →
      Trans C (.ev (.get l v t))
        { C with threadMap := update C.threadMap i (K.plug (.val (.num v))) }
  | set {C i l v t} {K : Ctx} :
      C.threadMap i = K.plug (.setc l (.val (.num v))) →
      C.activeThread = some i →
      C.activeTx = some t →
      Trans C (.ev (.set l v t))
        { C with store := update C.store l v,
                 threadMap := update C.threadMap i (K.plug (.val .unit)) }
  | eend {C i t} {K : Ctx} :
      C.threadMap i = K.plug .eend →
      C.activeThread = some i →
      C.activeTx = some t →
      Trans C (.ev (.eend t))
        { C with activeThread := none, activeTx := none,
                 threadMap := update C.threadMap i (K.plug (.val .unit)) }
  | retry {C i t} {K : Ctx} :
      C.threadMap i = K.plug .retry →
      C.activeThread = some i →
      C.activeTx = some t →
      Trans C (.ev (.retry t))
        { C with store := C.snapshot, activeThread := none, activeTx := none,
                 threadMap :=
                   update C.threadMap i (K.plug (.seq .begin C.savedBody)) }
  | adm {C i r e} {K : Ctx} :
      C.threadMap i = K.plug r →
      Local r e →
      Trans C .adm
        { C with threadMap := update C.threadMap i (K.plug e) }

/-- A trace: the sequence of labels emitted along a run, administrative steps
included. -/
inductive Trace : Config → List TLabel → Config → Prop where
  | nil  {C} : Trace C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Trace C' w C'' → Trace C (ℓ :: w) C''

/-- The initial configuration `⟨σ₀, ⊥, ⊥, E₀, σ₀, ()⟩`, minting ids from `0`. -/
def initConfig (E₀ : ThreadMap) : Config :=
  { store := Store.init_store, activeThread := none, activeTx := none,
    threadMap := E₀, snapshot := Store.init_store, savedBody := .val .unit,
    nextTx := 0 }

end Reagent
