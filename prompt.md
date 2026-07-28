# Reagent — Incremental Mechanization Plan

**Guiding principle.** *Inch by inch it's a cinch; yard by yard it's hard.*
Build the smallest correct core first, prove the two consistency axioms for it
end-to-end in Lean, and only then grow the language one feature at a time. Do not
attempt the whole language in one shot.

**Reference document.** `~/reports/reagents_verification/reagent-correctness.tex`
(the authoritative spec). Every object we build must match its definitions:
configuration, operational rules, trace, transaction, program order, `min`/`max`,
committed/uncommitted, arbitration, history, and the `Int`/`Ext` axioms.

**Ultimate goal.** Mechanize Reagent in Lean 4 and prove that **for every program
`P`, every history it produces satisfies Internal consistency (`Int`) and External
consistency (`Ext`)**. We reach it in versions; this document specifies **Version 1**
and the expansion order after it.

---

## Housekeeping before starting

- The folder already contains a fuller mechanization (six-tuple config, `retry`,
  administrative reductions, `Int`/`Ext`). **Do not build on top of it.** Move it
  aside first: archive the existing `Reagent/` modules into `archive/v0/` (or a
  git branch) so V1 starts from a clean slate.
- Keep the archived work as reference — we will pull the `retry`/six-tuple
  machinery back in during later versions. Nothing is deleted, only deferred.

---

## Version 1 — the minimal core

### Scope: what is in, what is out

**In.** Exactly four commands: `begin`, `get(l)`, `set(l, n)`, `end`, sequenced
with `;`. A single shared store over a fixed finite set of locations.

**Out (deferred to later versions).**
- `retry` — no aborts, no rollback, no re-runs.
- Administrative / local reductions — no `let`, no `if`, no arithmetic (`+`),
  hence no `ℓ_adm` label and no `Local` rule.
- Anything requiring bound variables or values beyond store contents.

### What dropping `retry` buys us

Because `retry` is the *only* rule that reads the snapshot `σ̂` and the saved body
`Ê`, removing it lets us **shrink the six-tuple**
`⟨σ, λ, θ, E, σ̂, Ê⟩` down to the four-tuple

```
C = ⟨ σ , λ , θ , E ⟩
```

- `σ : Loc → ℕ`   — the shared store.
- `λ ∈ ThId ∪ {⊥}` — the thread that holds the lock (owner of the live transaction).
- `θ ∈ TxId ∪ {⊥}` — the live transaction id (tags emitted labels).
- `E : ThId → Expr` — the per-thread program.

(This is what "we can do with a triple" in the notes points at — the exact count
is four once we keep both `λ` and `θ`, but the two *retry-only* fields `σ̂`, `Ê`
are gone. Keep a comment recording that they return with `retry`.)

Two more consequences worth stating up front:
- With no administrative steps, **every trace label is a transition label**
  (`begin@t`, `get(l,v)@t`, `set(l,v)@t`, `end@t`) — there are no `ℓ_adm` labels.
- With no `retry`, **a transaction can only terminate by `end`**. So every
  *finished* transaction is committed; the only uncommitted transactions are
  *pending* ones (the trace stops before their `end`).

### Syntax (V1)

```
n  ∈ ℕ                       -- literal store values
l  ∈ Loc                     -- shared locations
c  ::= begin | get(l) | set(l, n) | end        -- commands
e  ::= () | c | e ; e                          -- programs (sequenced commands)
```

No variables, no `let`, no `if`, no `+`. `get(l)`'s read value is only recorded in
its label (there is no binder to consume it); `set(l, n)` writes a literal.
Evaluation contexts collapse to the single sequencing frame `[·] ; e`.

### Operational semantics (V1): four rules

Small-step labelled relation `C --ℓ--> C'` on the four-tuple, faithful to
Figure "Semantics of Reagent commands" of the `.tex` with `retry` and the
snapshot/saved-body updates removed. The active thread is `i`, its redex `r`.

- **Begin.** `E(i) = H[begin ; e]`, `λ = ⊥`, fresh `t`
  → `λ := i`, `θ := t`, `E(i) := H[() ; e]`; label `begin@t`.
- **Get.** `E(i) = H[get(l)]`, `λ = i`, `θ = t`, `σ(l) = v`
  → `E(i) := H[v]`; label `get(l,v)@t`. Store unchanged.
- **Set.** `E(i) = H[set(l, n)]`, `λ = i`, `θ = t`
  → `σ(l) := n`, `E(i) := H[()]`; label `set(l,n)@t`.
- **End.** `E(i) = H[end]`, `λ = i`, `θ = t`
  → `λ := ⊥`, `θ := ⊥`, `E(i) := H[()]`; label `end@t`.

Every transactional rule keeps the premise `λ = i` (only the owner may step) and
`θ = t` (a transaction is live, supplying the tag). Well-formedness is therefore
structural: an ill-formed `get`/`set`/`end` (reached with `λ ≠ i`) simply has no
rule and the run gets stuck — never assumed as a side condition.

### Declarative model to define (mirror the `.tex` exactly)

From a run's **trace** (the sequence of labels) build, in this order:

1. **Trace** — the list of labels of `C₀ --ℓ₁--> ⋯ --ℓₖ--> Cₖ` (Definition
   "Trace"). In V1 every `ℓ` is a transition label.
2. **Event** — a label paired with a unique identifier; carries a tag `t`.
3. **Transaction** `T = (E, po)` — the events sharing one tag `t`, with `po` the
   program order (their order in the trace), a *total order* on `E`.
4. **Program order** `po`, and **`min_po` / `max_po`** of a finite event set (the
   `po`-least and `po`-greatest events).
5. **Committed transaction** — `min_po(E)` is a `begin@t` and `max_po(E)` is an
   `end@t`. `Committed(T)` is the set of committed transactions.
6. **Uncommitted transaction** — `max_po(E)` is not an `end@t`;
   `Uncommitted(T) = T \ Committed(T)`. (In V1: exactly the pending ones.)
7. **Arbitration** `AR` — a total order on transactions: `S <_AR T` iff `S`'s
   terminator precedes `begin@T` in the trace.
8. **History** `H = (T, AR)` — the set of all transactions with the arbitration
   order.

Make these **computable** where possible (so concrete traces can be checked by
`decide`/`#eval`), and provide the corresponding `Prop` forms used in the theorems.

### The two axioms (state them precisely, per the `.tex`)

- **Internal consistency `Int`.** For every transaction `(E, po)` and every get
  event `e = get(x,n)` with a non-empty set of earlier same-transaction accesses
  to `x`, the `po`-latest such access is a get-or-set of `n` on `x`:
  `max_po(po⁻¹(e) ∩ HEvent_x) = _(x,n)`.
- **External consistency `Ext`.** For every external get `T ⊢ Get x : n` (the
  transaction's `po`-first access to `x` is a get returning `n`): either there is
  no committed setter of `x` arbitrated before `T` and `n = 0`, or the
  `AR`-latest committed setter of `x` before `T` satisfies `⊢ Set x : n`.

### The theorem to prove (V1)

> For every program `P` in the V1 subset and every trace `τ` it produces from an
> initial configuration, the induced history `H = (T, AR)` satisfies **`Int`** and
> **`Ext`**.

### Starting even smaller (V1 sub-scope knobs)

Begin with the least general case that still exercises both axioms, then relax:

- **V1a:** one thread, a *single* transaction (`begin ; … ; end`). This already
  forces `Int` (a get after an earlier same-`x` access) and the "external get →
  initial value `0`" case of `Ext`.
- **V1b:** one thread, *sequential* transactions `begin;…;end ; begin;…;end`
  (fresh tids, non-overlapping). This exercises the committed-setter case of
  `Ext` (a later transaction reads an earlier committed write) and `AR`.

Note the two shapes the notes call out as **out of V1's initial scope** — they are
handled either by construction or in a later version:

- `begin@t₁ begin@t₂` (a second `begin` with no intervening `end`) — **impossible
  by construction**: `Begin` requires `λ = ⊥`, so the single lock already forbids
  overlap. V1 relies on this rather than proving around it.
- tid **re-use / re-runs** (the `begin@t · … · retry@t · begin@t' · …` pattern) —
  only arises with `retry`; **deferred to the version that adds `retry`**.

### Deliverables & quality bar (V1)

- Lean 4 project; `lake build` clean; **no `sorry`**.
- Declarative model as computable definitions **plus** the `Prop` statements.
- Both soundness theorems proven (`Int` and `Ext` for all V1 traces).
- A few worked examples reproducing the `.tex`'s own traces (e.g. the
  "committed setter is visible → get = value" and "no committed setter → get = 0"
  scenarios) checked by evaluation.
- An axiom audit (`#print axioms`) showing the theorems rest only on standard
  Lean axioms.

---

## Expansion order after V1

Each version adds one feature, re-uses the V1 definitions, and re-proves `Int`/`Ext`.

- **V2 — concurrency under the lock.** Two (or more) threads. The lock (`λ = i`,
  `Begin` needs `λ = ⊥`) serialises transactions; show `Int`/`Ext` still hold and
  that a thread cannot act inside another's transaction (well-formedness example).
- **V3 — expressions & administrative reductions.** Add `let`, `if`, `+`, the
  `();e` step: the pure relation `e ⇝ e'` and the `Local` rule emitting `ℓ_adm`.
  Traces now interleave `ℓ_adm` labels; transactions still exclude them from `E`.
- **V4 — `retry`.** Reintroduce the snapshot `σ̂` and saved body `Ê` (back to the
  six-tuple), the `Retry` rule (rollback, lock release, `begin ; Ê` re-arm), tid
  re-runs, and genuinely *aborted* (uncommitted) transactions. Re-prove `Int`
  (unchanged — it needs no commit) and `Ext` (aborted writes must stay invisible;
  the store rollback is what makes this true).

Keep every V1 definition stable across versions so the growth is additive, and
carry forward comments noting where the deferred `retry`/six-tuple machinery plugs
back in.
