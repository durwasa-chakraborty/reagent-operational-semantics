/-
  Optimistic (k-CAS) semantics of Reagent, following
  `optimistic/docs/reagent-correctness-kcas.tex` §Configurations and rules.

  Syntax, evaluation contexts and the pure reductions `Local` are shared with
  the lock-based development; only the configuration and the command rules
  change.
-/
import Reagent.Semantics

namespace Optimistic

open Reagent (Loc TxId ThId EvId Store Expr Ctx Local ThreadMap update)

/-- Event labels. A failed k-CAS at `end` is labelled `retry`. -/
inductive Label where
  | begin : TxId → Label
  | get   : Loc → Nat → TxId → Label
  | set   : Loc → Nat → TxId → Label
  | eend  : TxId → Label
  | retry : TxId → Label
deriving DecidableEq, Repr

structure Event where
  id : EvId
  label : Label
deriving DecidableEq, Repr

inductive TLabel where
  | ev  : Event → TLabel
  | adm : TLabel
deriving DecidableEq, Repr

abbrev Log : Type := Loc → Option (Nat × Nat)

def Log.empty : Log := fun _ => none

-- AI The KCas Ok and Failed are still employed by AI
def KCasOk (σ : Store) (Λ : Log) : Prop :=
  ∀ l o c, Λ l = some (o, c) → σ l = o

-- AI Premise of `KCas-Fail`: some expected value does not match.
def KCasFail (σ : Store) (Λ : Log) : Prop :=
  ∃ l o c, Λ l = some (o, c) ∧ σ l ≠ o

-- NOTE This is new addition to the definition
def Log.apply (σ : Store) (Λ : Log) : Store :=
  fun l => match Λ l with
    | some (_, c) => c
    | none        => σ l

structure Config where
  store     : Store
  threadMap : ThreadMap
  txs       : ThId → Option (TxId × Log × Expr)
  nextTx    : TxId
  usedIds   : List EvId

-- NOTE We did discuss something around `abort` and `retry` this is just a placeholder
--      I am keeping this around for time being.
inductive Head : ThId → Config → Expr → TLabel → Config → Expr → Prop where
  | begin {C i e α} :
      C.txs i = none → α ∉ C.usedIds →
      Head i C (.seq .begin e) (.ev ⟨α, .begin C.nextTx⟩)
        { C with txs := update C.txs i (some (C.nextTx, Log.empty, C.threadMap i)),
                 nextTx := C.nextTx + 1, usedIds := α :: C.usedIds }
        (.seq (.val .unit) e)
  | getLog {C i t Λ Ê l o v α} :
      C.txs i = some (t, Λ, Ê) → Λ l = some (o, v) → α ∉ C.usedIds →
      Head i C (.getc l) (.ev ⟨α, .get l v t⟩)
        { C with usedIds := α :: C.usedIds }
        (.val (.num v))
  | getMem {C i t Λ Ê l v α} :
      C.txs i = some (t, Λ, Ê) → Λ l = none → C.store l = v → α ∉ C.usedIds →
      Head i C (.getc l) (.ev ⟨α, .get l v t⟩)
        { C with txs := update C.txs i (some (t, update Λ l (some (v, v)), Ê)),
                 usedIds := α :: C.usedIds }
        (.val (.num v))
  | setLog {C i t Λ Ê l o c v α} :
      C.txs i = some (t, Λ, Ê) → Λ l = some (o, c) → α ∉ C.usedIds →
      Head i C (.setc l (.val (.num v))) (.ev ⟨α, .set l v t⟩)
        { C with txs := update C.txs i (some (t, update Λ l (some (o, v)), Ê)),
                 usedIds := α :: C.usedIds }
        (.val .unit)
  | setMem {C i t Λ Ê l u v α} :
      C.txs i = some (t, Λ, Ê) → Λ l = none → C.store l = u → α ∉ C.usedIds →
      Head i C (.setc l (.val (.num v))) (.ev ⟨α, .set l v t⟩)
        { C with txs := update C.txs i (some (t, update Λ l (some (u, v)), Ê)),
                 usedIds := α :: C.usedIds }
        (.val .unit)
  | commit {C i t Λ Ê α} :
      C.txs i = some (t, Λ, Ê) → KCasOk C.store Λ → α ∉ C.usedIds →
      Head i C .eend (.ev ⟨α, .eend t⟩)
        { C with store := Log.apply C.store Λ, txs := update C.txs i none,
                 usedIds := α :: C.usedIds }
        (.val .unit)
  | adm {C i r e} :
      Local r e → Head i C r .adm C e

inductive Trans : Config → TLabel → Config → Prop where
  | ctx {C C' i r r' ℓ} :
      (C.threadMap i).redex = some r →
      Head i C r ℓ C' r' →
      Trans C ℓ
        { C' with threadMap := update C.threadMap i ((C.threadMap i).replace r') }
  | kcasRetry {C i t Λ Ê α} :
      (C.threadMap i).redex = some .eend →
      C.txs i = some (t, Λ, Ê) → KCasFail C.store Λ → α ∉ C.usedIds →
      Trans C (.ev ⟨α, .retry t⟩)
        { C with threadMap := update C.threadMap i Ê, txs := update C.txs i none,
                 usedIds := α :: C.usedIds }
  | retry {C i t Λ Ê α} :
      (C.threadMap i).redex = some .retry →
      C.txs i = some (t, Λ, Ê) → α ∉ C.usedIds →
      Trans C (.ev ⟨α, .retry t⟩)
        { C with threadMap := update C.threadMap i Ê, txs := update C.txs i none,
                 usedIds := α :: C.usedIds }

abbrev Trace : Type := List TLabel

/-- `⟨σ₀, E₀, ⊥⟩` with the all-zero store. -/
def initConfig (E₀ : ThreadMap) : Config :=
  { store := Reagent.Store.init_store, threadMap := E₀, txs := fun _ => none,
    nextTx := 0, usedIds := [] }

inductive Run : Config → Trace → Config → Prop where
  | nil  {C} : Run C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Run C' w C'' → Run C (ℓ :: w) C''

end Optimistic
