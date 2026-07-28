# The Reagent Language — mechanized semantics and consistency (V1)

A Lean 4 mechanization of **Reagent**, a small transactional (STM-like) language,
built **incrementally** per [`prompt.md`](prompt.md): *inch by inch it's a cinch;
yard by yard it's hard.* This is **Version 1 — the minimal core**: the four
commands `begin` / `get` / `set` / `end`, with `retry`, administrative reductions,
and expression forms (`let`/`if`/`+`) deferred to later versions.

Reference spec: [`docs/reagent-correctness.tex`](docs/reagent-correctness.tex).
The fuller (six-tuple, `retry`) mechanization from before is preserved under
[`archive/v0/`](archive/v0/); V1 is a clean rebuild.

V1 covers the whole pipeline of the paper for the minimal core:

1. **Operational semantics** — the four-tuple configuration `⟨σ, λ, θ, E⟩`
   (dropping the retry-only snapshot `σ̂` and saved body `Ê`), and the four
   command rules, each transactional rule carrying `λ = i` (owner) and `θ = t`
   (live transaction). No evaluation contexts (commands have no sub-expressions)
   and no `ℓ_adm` labels.
2. **The declarative model** — from a run's **trace** it reads off
   **transactions** `(E, po)`, `min_po` / `max_po`, **committed** /
   **uncommitted** status, **arbitration** `AR`, and the **history** `H = (𝐓, AR)`.
3. **The two axioms, proven** — **`int_sound`** (every trace is internally
   consistent) and **`ext_sound`** (an external read returns the committed value),
   for **all** V1 programs.

No `sorry`; the theorems rest only on `propext` (`make axioms`).

This is a **proof-only** development: it is a specification (the `Trans`
relation) and its proofs. There is no executable interpreter and no computed
examples — nothing "runs". Everything is checked by the Lean kernel.

## Layout

| File | Contents |
|------|----------|
| `Reagent/Syntax.lean`      | `Expr` (the four commands + sequencing), stores, thread maps, the four-tuple `Config`. |
| `Reagent/Semantics.lean`   | Labels, the four transition rules (`Trans`), traces (`Trace`), initial configs. |
| `Reagent/Trace.lean`       | The declarative model: `txEvents` (a transaction `(E, po)`), `minPo`/`maxPo`, `committed`/`uncommitted`, `arb` (arbitration `AR`), `History`, the setter judgement `setJudg`, external gets `externalGet`, and the setter set `W_x` (`committedSetters` / `arCandidates` / `arMax`). |
| `Reagent/Consistency.lean` | `IntConsistent` and **`int_sound`**: every V1 trace satisfies `Int`. |
| `Reagent/External.lean`    | The committed-value fold `lcs`, **`ext_sound`** (external reads return it), and **`lcs_commit`** (a committed transaction commits its `po`-last write). |
| `docs/`                    | Spec: `reagent-correctness.tex`, `notes.org`. |
| `archive/v0/`              | The previous six-tuple / `retry` mechanization, kept for reference. |

## Building

Requires the Lean toolchain in `lean-toolchain` (Lean 4.31.0, via
[`elan`](https://github.com/leanprover/elan)):

```sh
make          # build & check the whole mechanization
make axioms   # show the theorems rest only on `propext`
make pdf      # typeset docs/reagent-correctness.pdf
```

## The two theorems

From `Reagent/Consistency.lean` and `Reagent/External.lean`:

```lean
theorem int_sound (h : Trace (init E₀) w C) : IntConsistent w
theorem ext_sound (h : Trace (init E₀) w C) : ExtConsistent w
```

- **`IntConsistent w`** — the paper's `Int`: for every read `get(x,n)@t`, if the
  same transaction already accessed `x`, its `po`-latest earlier access carries
  `n`. Proof: a store-tracking induction — within a transaction the single lock
  isolates the store, so `σ(x)` equals the latest earlier access value.
- **`ExtConsistent w`** — the essence of `Ext`: an external read (whose
  transaction has not yet written `x`) returns `lcs x pre`, the **committed
  value** — the value the `AR`-latest committed setter left in `x`, or `0`.
  `lcs` is a forward fold that commits a write only at its transaction's `end`;
  `lcs_commit` proves a committed transaction commits its `po`-last write. Since
  a pending transaction holds the lock, an external read never sees an
  uncommitted write.

## Roadmap (next versions)

- **V2** — concurrency: more threads, serialized by the lock.
- **V3** — expressions & administrative reductions (`let`/`if`/`+`, the `Local`
  rule, `ℓ_adm` labels).
- **V4** — `retry`: reintroduce `σ̂` / `Ê` (back to the six-tuple), aborted
  transactions, and store rollback; re-prove `Int` and `Ext`.
