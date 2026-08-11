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
`ℓ_adm` (Definition "Trace").  -/
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

/-- The command rules on a *redex*, together with `Local`.

`Head i C r ℓ C' r'` reads: thread `i`, with the machine in state `C`, rewrites
the redex `r` to `r'`, emitting `ℓ` and leaving state `C'`. No evaluation
context appears — locating the redex and framing the rest of the thread map is
`Trans.ctx`'s job, stated once below. The thread map component of `C` is carried
through untouched for the same reason.

The premises the document states as side conditions are here instead written
into the input configuration: `λ = ⊥` for `Begin`, and `λ = i` together with
`θ = t` for the transactional rules, which is what binds `i` and `t`.

`Begin`'s redex is `begin ; e`: the `begin` becomes `()` in place, and the
continuation `e` is saved as `Ê` — exactly the body `Retry` reinstates. It mints
`nextTx` as the document's `t_fresh`, bumps the counter, and snapshots the store.

`Get` reduces to the value read, so a surrounding `let x = get(l) in …` can
consume it. `Set`'s redex is `set(l,v)` with `v` already a value — the context
`set(l, ECtx)` is what evaluates the argument — and it reduces to `()`.

`Retry` is lock releasing: it rolls the store back to `σ̂`, clears `λ` and `θ`
so another thread may `begin`, and re-arms the thread as `begin ; Ê`, so the
retried attempt must re-acquire the lock and runs under a *fresh* id.

`adm` lifts `⇝` to an `ℓ_adm`-labelled step. It leaves the configuration
entirely alone and carries no `λ = i` premise: any thread may take a pure step,
inside a transaction or not. -/
inductive Head : ThId → Config → Expr → TLabel → Config → Expr → Prop where
  | begin {σ θ E snap body n i e} :
      Head i ⟨σ, none, θ, E, snap, body, n⟩ (.seq .begin e)
        (.ev (.begin n))
        ⟨σ, some i, some n, E, σ, e, n + 1⟩ (.seq (.val .unit) e)
  | get {σ i t E snap body n l v} :
      σ l = v →
      Head i ⟨σ, some i, some t, E, snap, body, n⟩ (.getc l)
        (.ev (.get l v t))
        ⟨σ, some i, some t, E, snap, body, n⟩ (.val (.num v))
  | set {σ i t E snap body n l v} :
      Head i ⟨σ, some i, some t, E, snap, body, n⟩ (.setc l (.val (.num v)))
        (.ev (.set l v t))
        ⟨update σ l v, some i, some t, E, snap, body, n⟩ (.val .unit)
  | eend {σ i t E snap body n} :
      Head i ⟨σ, some i, some t, E, snap, body, n⟩ .eend
        (.ev (.eend t))
        ⟨σ, none, none, E, snap, body, n⟩ (.val .unit)
  | retry {σ i t E snap body n} :
      Head i ⟨σ, some i, some t, E, snap, body, n⟩ .retry
        (.ev (.retry t))
        ⟨snap, none, none, E, snap, body, n⟩ (.seq .begin body)
  | adm {C i r e} :
      Local r e → Head i C r .adm C e

/-- Lifting a redex step into the transition system: the *only* rule that
mentions an evaluation context. It locates thread `i`'s redex with `ECtx`,
rewrites it in place, and frames the rest of the thread map. -/
inductive Trans : Config → TLabel → Config → Prop where
  | ctx {C C' i r r' ℓ} {K : Ctx} :
      C.threadMap i = K.plug r →
      Head i C r ℓ C' r' →
      Trans C ℓ { C' with threadMap := update C.threadMap i (K.plug r') }

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
