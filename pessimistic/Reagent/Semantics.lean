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

structure Event where
  -- NOTE id is strictly for identifier and does not harbor monotonic increasing or decreasing properties
  id : EvId
  label : Label
deriving DecidableEq, Repr

/-- A trace label is *either* an event *or* an administrative step `ℓ_adm`
(Definition "Trace").

An event, not a bare `Label`: the id is minted by the rule that emits it, so it
travels in the trace from the start. Nothing downstream has to invent names for
events afterwards. -/
inductive TLabel where
  | ev  : Event → TLabel
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

NOTE Every rule that emits an event also mints an id: it picks an α for userIds and records it.
     The relation is non-deterministic in α and all a runknows about its ids is that they are pairwise distinct.


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
-- NOTE the α ∉ List of ID is what is saving us from a fresh ID; rest everything remains the same
--      we are emitting the α (that is the whole point of the exercise)
inductive Head : ThId → Config → Expr → TLabel → Config → Expr → Prop where
  | begin {σ θ E snap body n u i e α} :
      α ∉ u →
      Head i ⟨σ, none, θ, E, snap, body, n, u⟩ (.seq .begin e)
        (.ev ⟨α, .begin n⟩)
        ⟨σ, some i, some n, E, σ, e, n + 1, α :: u⟩ (.seq (.val .unit) e)
  | get {σ i t E snap body n u l v α} :
      α ∉ u →
      σ l = v →
      Head i ⟨σ, some i, some t, E, snap, body, n, u⟩ (.getc l)
        (.ev ⟨α, .get l v t⟩)
        ⟨σ, some i, some t, E, snap, body, n, α :: u⟩ (.val (.num v))
  | set {σ i t E snap body n u l v α} :
      α ∉ u →
      Head i ⟨σ, some i, some t, E, snap, body, n, u⟩ (.setc l (.val (.num v)))
        (.ev ⟨α, .set l v t⟩)
        ⟨update σ l v, some i, some t, E, snap, body, n, α :: u⟩ (.val .unit)
  | eend {σ i t E snap body n u α} :
      α ∉ u →
      Head i ⟨σ, some i, some t, E, snap, body, n, u⟩ .eend
        (.ev ⟨α, .eend t⟩)
        ⟨σ, none, none, E, snap, body, n, α :: u⟩ (.val .unit)
  | retry {σ i t E snap body n u α} :
      α ∉ u →
      Head i ⟨σ, some i, some t, E, snap, body, n, u⟩ .retry
        (.ev ⟨α, .retry t⟩)
        ⟨snap, none, none, E, snap, body, n, α :: u⟩ (.seq .begin body)
  | adm {C i r e} :
      Local r e → Head i C r .adm C e

/-- Every redex a rule fires on really is one, in `split`'s sense. -/
theorem Local.isRedex {r e : Expr} (h : Local r e) : r.IsRedex := by
  cases h <;> rfl

theorem Head.isRedex {i : ThId} {C C' : Config} {r r' : Expr} {ℓ : TLabel}
    (h : Head i C r ℓ C' r') : r.IsRedex := by
  cases h with
  | adm hloc => exact hloc.isRedex
  | _ => rfl

/-- Lifting a redex step into the transition system.

No evaluation context appears. `split` locates thread `i`'s redex and `replace`
puts the result back where it was found — the context is *computed* from the
thread's expression rather than guessed, which is legitimate because
`Expr.split_of_plug` shows the decomposition is unique. `Trans.of_plug` below
recovers the context-explicit form. -/
inductive Trans : Config → TLabel → Config → Prop where
  | ctx {C C' i r r' ℓ} :
      (C.threadMap i).redex = some r →
      Head i C r ℓ C' r' →
      Trans C ℓ
        { C' with threadMap := update C.threadMap i ((C.threadMap i).replace r') }

/-- The context-explicit introduction rule, recovered. Nothing was lost by
dropping `K`: any decomposition of the thread's expression into a context and a
redex a rule fires on gives a transition, with the result plugged back into that
same context. -/
theorem Trans.of_plug {C C' : Config} {i : ThId} {r r' : Expr} {ℓ : TLabel}
    {K : Ctx} (he : C.threadMap i = K.plug r) (hh : Head i C r ℓ C' r') :
    Trans C ℓ { C' with threadMap := update C.threadMap i (K.plug r') }
    := by
  have hr : r.IsRedex := hh.isRedex
  have h1 : (C.threadMap i).redex = some r := by rw [he]; exact Expr.redex_plug hr
  have h2 : (C.threadMap i).replace r' = K.plug r' := by
    rw [he]; exact Expr.replace_plug hr r'
  rw [← h2]
  exact Trans.ctx h1 hh

end Reagent
