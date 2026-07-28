/-
  Reagent — Version 1 (minimal core).

  Syntax and configurations for the four-command language `begin / get / set /
  end`, following `docs/reagent-correctness.tex` with `retry`, administrative
  reductions, and expression forms (`let`/`if`/`+`) removed.

  Because `retry` is gone, the six-tuple `⟨σ, λ, θ, E, σ̂, Ê⟩` of the document
  loses its two retry-only fields (the snapshot `σ̂` and saved body `Ê`) and
  shrinks to the four-tuple `⟨σ, λ, θ, E⟩`.  (Those two fields return in the
  version that reintroduces `retry`.)
-/

namespace Reagent

/-- Shared mutable locations. -/
abbrev Loc  : Type := Nat
/-- Transaction identifiers. -/
abbrev TxId : Type := Nat
/-- Thread identifiers. -/
abbrev ThId : Type := Nat
/-- Store Loc → ℕ -/
abbrev Store : Type := Loc → Nat

/-- Programs of the V1 language.

    A program is a right-nested sequence of commands ending in `unit`
    (e.g. `begin ; get l ; set l 1 ; end ; unit`).  Commands carry no
    sub-expressions — `get` reads a location, `set` writes a literal `n` — so
    there is nothing to evaluate *inside* a command and hence no need for
    evaluation contexts: the redex is always the head command of a thread's
    sequence.  `get`'s read value is recorded only in its trace label (there is
    no binder to consume it), so it is discarded here. -/
inductive Expr where
  | unit : Expr                    -- the finished program ()
  | seq  : Expr → Expr → Expr      -- c ; e
  | getc : Loc → Expr              -- get(l)
  | setc : Loc → Nat → Expr        -- set(l, n)
  | begin : Expr                   -- begin
  | eend : Expr                    -- end
deriving DecidableEq, Repr


def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β): α → β :=
  fun a' => if a' = a then b else f a'

@[simp] theorem update_same{α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β)
: update f a b a = b := by
  simp [update]

@[simp] theorem update_other{α β : Type} [DecidableEq α] (f : α → β) (a a': α) (b : β)
(ih : a ≠ a')
: update f a b a' = f a' := by
  simp [update, ih.symm]



namespace Store

/-- The all-zero initial store `σ₀`. -/
def init_store : Store := fun _ => 0

end Store

/-- A thread map `E : ThId → Expr`. -/
abbrev ThreadMap : Type := ThId → Expr

/-- A configuration is the four-tuple `⟨σ, λ, θ, E⟩`:

    * `store`  – shared store `σ`;
    * `lam`    – the thread `i` that holds the lock (`none` is `⊥`);
 -/
/-* `theta`  – the live transaction id `θ` (`none` is `⊥`);
    * `threads`– the thread map `E`.

    Invariant kept by the rules: `λ = ⊥ ↔ θ = ⊥`. -/
structure Config where
  store   : Store
  lam     : Option ThId
  theta   : Option TxId
  threadMap : ThreadMap

/-- TODO : We don't know if this is correct but for now. -/
/-Termination condition: every active thread is at `unit`. -/
def Config.terminated (C : Config) (dom : List ThId) : Prop :=
  ∀ i ∈ dom, C.threadMap i = .unit

end Reagent
