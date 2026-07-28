/-
  The declarative model of a run (Section "Traces, Transactions, and Histories"
  of `docs/reagent-correctness.tex`), for V1.

  From a run's trace (a `List Label`) we read off, in the order the document
  develops them:  transactions `(E, po)`, `min`/`max` under program order,
  committed / uncommitted transactions, the arbitration order `AR`, the history
  `H = (T, AR)`, and the two consistency checks `intCheck` / `extCheck`.

  Program order `po` is the order of a transaction's events in the trace; the
  whole trace list is the total program order it restricts.  All definitions are
  computable so concrete traces can be checked; the soundness proofs are in
  `Reagent/Consistency.lean` (Int) and `Reagent/External.lean` (Ext).
-/
import Reagent.Semantics

namespace Reagent

namespace Label

/-- The transaction id a label carries. -/
def tag : Label → TxId
  | .begin t   => t
  | .get _ _ t => t
  | .set _ _ t => t
  | .eend t    => t

def isBegin : Label → Bool | .begin _ => true | _ => false
def isEnd   : Label → Bool | .eend _  => true | _ => false

/-- The value a `get`/`set` on `x` carries (`HEvent_x`), if any. -/
def accVal (x : Loc) : Label → Option Nat
  | .get x' v _ => if x' = x then some v else none
  | .set x' v _ => if x' = x then some v else none
  | _           => none

/-- The value a `set` on `x` carries, if any (`T ⊢ Set x : n`). -/
def setVal (x : Loc) : Label → Option Nat
  | .set x' v _ => if x' = x then some v else none
  | _           => none

def isAccessOn (x : Loc) (ℓ : Label) : Bool := (ℓ.accVal x).isSome

end Label

/-! ## Transactions `(E, po)` -/

/-- The events of transaction `t`, in program order. -/
def txEvents (w : List Label) (t : TxId) : List Label :=
  w.filter (fun ℓ => ℓ.tag == t)

/-- The transaction identifiers occurring in the trace (with repeats). -/
def tagsOf (w : List Label) : List TxId := w.map Label.tag

/-- The locations touched in the trace. -/
def locsOf (w : List Label) : List Loc :=
  w.filterMap (fun ℓ => match ℓ with
    | .get x _ _ => some x
    | .set x _ _ => some x
    | _          => none)

/-! ## `min` / `max` under program order

    Since `po` is list order, `min_po` is the head event and `max_po` the last. -/

def minPo (w : List Label) (t : TxId) : Option Label := (txEvents w t).head?
def maxPo (w : List Label) (t : TxId) : Option Label := (txEvents w t).getLast?

/-! ## Committed / uncommitted -/

/-- `T` is committed when `min_po` is a `begin@t` and `max_po` is an `end@t`. -/
def committed (w : List Label) (t : TxId) : Bool :=
  minPo w t == some (.begin t) && maxPo w t == some (.eend t)

def uncommitted (w : List Label) (t : TxId) : Bool := !committed w t

/-! ## Arbitration `AR` -/

/-- The terminator of `t` (its `max_po` event). -/
def terminator (w : List Label) (t : TxId) : Option Label := maxPo w t

/-- The first position of a label in the trace. -/
def idxOf (w : List Label) (ℓ : Label) : Option Nat := w.findIdx? (· == ℓ)

/-- `S <_AR T`: `S`'s terminator precedes `begin@T` in the trace. -/
def arb (w : List Label) (s t : TxId) : Bool :=
  match terminator w s, idxOf w (.begin t) with
  | some term, some bi =>
      match idxOf w term with
      | some ti => decide (ti < bi)
      | none    => false
  | _, _ => false

/-! ## History `H = (𝐓, AR)` -/

structure History where
  txs : List TxId
  ar  : TxId → TxId → Bool

def historyOf (w : List Label) : History := ⟨tagsOf w, arb w⟩

/-! ## Setter / external-getter judgements -/

/-- `T ⊢ Set x : n` — `T`'s `po`-last set of `x`. -/
def setJudg (w : List Label) (t : TxId) (x : Loc) : Option Nat :=
  ((txEvents w t).filterMap (Label.setVal x)).getLast?

/-- `T ⊢ Get x : n` — the external-get value: `T`'s first access to `x` is a
    `get` returning `n`. -/
def externalGet (w : List Label) (t : TxId) (x : Loc) : Option Nat :=
  match (txEvents w t).find? (Label.isAccessOn x) with
  | some (.get x' v _) => if x' = x then some v else none
  | _                  => none

/-! ## The setter set `W_x` and `AR`-restricted candidates

    The declarative pieces the paper's `Ext` axiom quantifies over: the committed
    setters of `x`, those arbitrated before a transaction, and the `AR`-greatest
    among them. -/

/-- The committed setters of `x` (`W_x`). -/
def committedSetters (w : List Label) (x : Loc) : List TxId :=
  (tagsOf w).filter (fun s => committed w s && (setJudg w s x).isSome)

/-- `AR⁻¹(T) ∩ W_x`. -/
def arCandidates (w : List Label) (t : TxId) (x : Loc) : List TxId :=
  (committedSetters w x).filter (fun s => arb w s t)

/-- The `AR`-greatest of a candidate list. -/
def arMax (w : List Label) : List TxId → Option TxId :=
  List.foldl (fun acc s =>
    match acc with
    | none   => some s
    | some a => if arb w a s then some s else some a) none

end Reagent
