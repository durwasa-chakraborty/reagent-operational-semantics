/-
  Operational semantics of Reagent V1 (four rules).

  The labelled transition relation `C --ℓ--> C'` fires on the head command of a
  thread's sequence.  Every transactional rule (Get/Set/End) carries the premise
  `λ = i` (only the owner thread may step) and `θ = t` (a transaction is live,
  supplying the tag).  There are no evaluation contexts (commands have no
  sub-expressions) and no administrative reductions: each command rule advances
  the sequence `c ; e` directly to its continuation `e`.
-/
import Reagent.Syntax

namespace Reagent

/-- Visible labels.  V1 has only transition labels — no `ℓ_adm`. -/
inductive Label where
  | begin : TxId → Label
  | get   : Loc → Nat → TxId → Label
  | set   : Loc → Nat → TxId → Label
  | eend  : TxId → Label
deriving DecidableEq, Repr

/-- The four command rules (Figure "Semantics of Reagent commands", restricted).

    `E` is a total map (`ThId → Expr`), so a thread's program is `C.threadMap i`
    directly — no `some`/`none`. -/
inductive Trans : Config → Label → Config → Prop where
  | begin {C i t e} :
      C.threadMap i = .seq .begin e →
      C.lam = none →
      Trans C (.begin t)
        { C with lam := some i, theta := some t, threadMap := update C.threadMap i e }
  | get {C i l t v e} :
      C.threadMap i = .seq (.getc l) e →
      C.lam = some i →
      C.theta = some t →
      C.store l = v →
      Trans C (.get l v t)
        { C with threadMap := update C.threadMap i e }
  | set {C i l n t e} :
      C.threadMap i = .seq (.setc l n) e →
      C.lam = some i →
      C.theta = some t →
      Trans C (.set l n t)
        { C with store := update C.store l n, threadMap := update C.threadMap i e }
  | eend {C i t e} :
      C.threadMap i = .seq .eend e →
      C.lam = some i →
      C.theta = some t →
      Trans C (.eend t)
        { C with lam := none, theta := none, threadMap := update C.threadMap i e }

/-- A trace: the sequence of labels along a run (Definition "Trace"). -/
inductive Trace : Config → List Label → Config → Prop where
  | nil  {C} : Trace C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Trace C' w C'' → Trace C (ℓ :: w) C''

/-- Reachability. -/
def Reaches (C C' : Config) : Prop := ∃ w, Trace C w C'

/-- Concatenation of traces. -/
theorem Trace.append {C w₁ C' w₂ C''} (h₁ : Trace C w₁ C') (h₂ : Trace C' w₂ C'') :
    Trace C (w₁ ++ w₂) C'' := by
  induction h₁ with
  | nil => exact h₂
  | cons tr _ ih => exact .cons tr (ih h₂)

/-- An initial configuration `⟨σ₀, ⊥, ⊥, E₀⟩` with the zero store. -/
def init (E₀ : ThreadMap) : Config :=
  { store := Store.init_store, lam := none, theta := none, threadMap := E₀ }

end Reagent
