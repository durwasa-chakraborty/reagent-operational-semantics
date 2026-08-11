# The Reagent Language — mechanized semantics and consistency

A Lean 4 mechanization of **Reagent**, a small transactional (STM-like) language,
built **incrementally** per [`prompt.md`](prompt.md): *inch by inch it's a cinch;
yard by yard it's hard.*

Reference spec: [`docs/reagent-correctness.tex`](docs/reagent-correctness.tex).
An earlier mechanization is preserved under [`archive/v0/`](archive/v0/).

The development covers the whole pipeline of the paper for the full core
language:

1. **Operational semantics** — the six-tuple configuration `⟨σ, λ, θ, E, σ̂, Ê⟩`
   (plus a freshness counter, see below), evaluation contexts, the five command
   rules, and the pure/administrative reductions under `ℓ_adm`. Every
   transactional rule carries `λ = i` (owner) and `θ = t` (live transaction).
2. **The declarative model** — from a run's **trace** it reads off
   **transactions** `(E, po)`, `min_po` / `max_po`, **committed** /
   **uncommitted** status, **arbitration** `AR`, and the **history**
   `H = (𝐓, AR)`.
3. **The two axioms, proven** — **`int_historyOf`** (every trace is internally
   consistent) and **`ext_historyOf`** (an external read returns the committed
   value), for **all** programs.

No `sorry`. `make axioms` shows the theorems rest only on Lean's standard
axioms: `propext`, `Classical.choice`, `Quot.sound`.

This is a **proof-only** development: it is a specification (the `Trans`
relation) and its proofs. There is no executable interpreter — the runs in
`Examples.lean` are proof terms built by applying the rules, not computations.
Everything is checked by the Lean kernel.

## Layout

| File | Contents |
|------|----------|
| `Reagent/Syntax.lean`         | `Val`, `Expr` (expressions and the five commands), substitution, evaluation contexts `Ctx` and `Ctx.plug`, stores, thread maps, the configuration `Config`. |
| `Reagent/Semantics.lean`      | Labels and trace labels (`ℓ_adm`), the pure reductions `Local`, the redex rules `Head`, the context-lifting rule `Trans.ctx`, traces (`Trace`), initial configs. |
| `Reagent/Trace.lean`          | The declarative model: `traceEvents` (events and their trace positions), `Transaction` `(E, po)`, `minPo`/`maxPo`, `Committed`/`Uncommitted`, arbitration `AR`, and `History`. |
| `Reagent/IntConsistency.lean` | `Transaction.Int` and **`int_historyOf`**: every trace satisfies `Int`. |
| `Reagent/ExtConsistency.lean` | The committed-value fold `cv`, the judgements `SetVal`/`GetVal`, `History.Ext`, and **`ext_historyOf`**. |
| `Reagent/Examples.lean`       | Concrete runs built by applying the rules — evidence that they fire, and a machine-checked witness for the `retry` gap below. |
| `docs/`                       | Spec: `reagent-correctness.tex`, `notes.org`. |
| `archive/v0/`                 | An earlier mechanization, kept for reference. |

### Shape of the semantics

`Semantics.lean` splits the transition relation in two, mirroring the document's
own split between the rule figure and §"The command rules in context form":

```lean
-- what each rule does to a redex; no evaluation context anywhere
inductive Head : ThId → Config → Expr → TLabel → Config → Expr → Prop

-- the only rule that mentions a context: locate the redex, rewrite in
-- place, frame the rest of the thread map
inductive Trans : Config → TLabel → Config → Prop where
  | ctx {C C' i r r' ℓ} {K : Ctx} :
      C.threadMap i = K.plug r →
      Head i C r ℓ C' r' →
      Trans C ℓ { C' with threadMap := update C.threadMap i (K.plug r') }
```

The document's side conditions are written into `Head`'s input configuration
rather than carried as separate premises — `λ = ⊥` for `Begin`, and `λ = i`,
`θ = t` for the transactional rules, which is also what binds `i` and `t`.

### Deviations from the document

* **A seventh configuration component.** `Config` carries `nextTx`, the counter
  `Begin` mints from. This realises the document's `θ fresh` side condition,
  which a relation between two configurations cannot otherwise express. It is
  never read by any rule but `Begin`. Freshness is load-bearing: `Int` is false
  without it, since a reused identifier would splice an aborted attempt and its
  replacement into one "transaction" whose read contradicts its own earlier
  write.
* **`AR` is terminator order, not commit order.** The document orders only
  *committed* transactions, by `end@s` before `begin@t`. Here `S <_AR T` holds
  whenever `S`'s `po`-last event is a terminator — `end` **or** `retry` — before
  `T`'s `begin`. `Ext` restricts its setters to committed transactions
  separately, so an aborted write is still never observed.
* **`Committed` also requires a `begin`.** The document asks only that the
  `po`-greatest event be an `end`; `Transaction.Committed` additionally requires
  the `po`-least to be a `begin`. The two agree on transactions arising from a
  real trace (`uncommitted_iff_not_committed`).
* **The initial store is all-zero.** `initConfig` fixes `σ₀ = λ_. 0`, where the
  document quantifies over initial stores. `Ext`'s "or the initial value 0"
  matches.
* **Runs are canonically numbered.** Because `Begin` mints from a counter, the
  generated runs are exactly those with identifiers `0, 1, 2, …`, where the
  document permits any unused identifier. `Int` and `Ext` are invariant under
  renaming of transaction identifiers, so this is without loss of generality —
  but that argument is prose here, not a lemma.
* **`==` has no reduction in the document.** It gives the contexts `ECtx == e`
  and `v == ECtx` and uses `==` in a worked example, but states no rule.
  `Local.eqv` supplies the obvious one.

## Building

Requires the Lean toolchain in `lean-toolchain` (Lean 4.31.0, via
[`elan`](https://github.com/leanprover/elan)):

```sh
make          # build & check the whole mechanization
make axioms   # show the theorems rest only on Lean's standard axioms
make pdf      # typeset docs/reagent-correctness.pdf
```

## The two theorems

From `Reagent/IntConsistency.lean` and `Reagent/ExtConsistency.lean`:

```lean
theorem int_historyOf (h : Trace (initConfig E₀) ℓs C) : (historyOf ℓs).Int
theorem ext_historyOf (h : Trace (initConfig E₀) ℓs C) : (historyOf ℓs).Ext
```

- **`Int`** — the paper's internal consistency: for every read `get(x,n)@t`, if
  the same transaction already accessed `x`, its `po`-latest earlier access
  carries `n`. Proof: a store-tracking induction (`inv_store`) — within a
  transaction the single lock isolates the store, and since `retry` releases the
  lock as it rolls back, no rollback ever happens *inside* a live transaction.
- **`Ext`** — an external read (one whose transaction has not yet accessed `x`)
  returns the value left by the `AR`-latest **committed** setter of `x`, or `0`
  if there is none. The proof has two halves: a fold `cv` over the trace tracks
  `(committed value of x, pending write of the live transaction)`, and
  `StoreEnc` ties it to the store through every rule (`ext_get_value`); then
  `cv_fst_spec` characterises the fold's first component declaratively, and
  `ar_of_termPos_lt` identifies terminator order with `AR`.

Administrative steps appear in traces but are **not** events: `traceEvents`
drops them while still counting their positions, so an event's identifier stays
its index in the full trace and `po` remains `<` on identifiers. They are
therefore members of no transaction's `E`, and both proofs carry them as no-ops.

## Known gaps

* **`retry` loses the surrounding context.** `Begin` saves only the continuation
  `e` from the redex `begin ; e`, and `Retry` re-arms the thread as
  `ECtx[begin ; Ê]` using the context *at the point of the retry*. When those
  two contexts differ the enclosing continuation is dropped. `Examples.lean`
  proves it: for `let x = (begin ; get l) in retry`, `retry_drops_context` shows
  the thread is re-armed as `begin ; get l` — the `let` is gone — and
  `retry_deadlocks` continues the run to a value still holding the lock
  (`λ = 0`, `θ = t₁`, no `end` reachable), so no thread can ever `begin` again.
  The document is itself ambiguous here (its figure plugs into `ECtx` while
  §"The command rules in context form" sets `Ê = ECtx[()]`), so this needs a
  decision in the spec before it can be fixed in Lean. Neither theorem is
  affected — `Int` and `Ext` do not constrain which continuation a retry
  resumes.
* **Example coverage is thin.** `Examples.lean` exhibits one program's runs.
  Because `Trans` quantifies existentially over thread, context and redex, a
  rule that matched nothing would leave both theorems provable and vacuously
  true, so more worked runs — especially multi-thread ones — are the cheapest
  insurance available.

## Roadmap

- More worked runs, especially multi-thread ones, to rule out vacuity.
- Resolve the `retry` continuation question in `docs/reagent-correctness.tex`,
  then align `Semantics.lean`.
- Generalize `initConfig` to an arbitrary initial store.
