/-
  The declarative model of a run (Section "Traces, Transactions, and Histories"
  and Section "Consistency" of `docs/reagent-correctness.tex`).

  A run's *trace* is the `List Label` produced by the operational semantics.
  From it we read off, exactly as the paper does:

    * the events of a transaction `t`     (`txEvents`, the pair `(E, po)`);
    * whether a transaction is committed   (`committed`) or uncommitted;
    * the arbitration order                (`arb`, the total order `AR`);
    * the history                          (`History = (T, AR)`);
    * the two consistency axioms           (`intCheck`, `extCheck`).

  Program order `po` is the order of a transaction's events in the trace list;
  the global list order is the total program order it restricts.  The checks are
  computable `Bool` functions, so they can be run on concrete traces
  (see `Reagent/Examples.lean`); the *proof* that every operational trace
  satisfies `Int` is in `Reagent/Consistency.lean`.
-/
import Reagent.Semantics

namespace Reagent

/-! ## Reading a label -/

namespace Label

/-- The transaction identifier a label carries; `none` for `ℓ_adm`. -/
def tag : Label → Option TxId
  | .begin t   => some t
  | .get _ _ t => some t
  | .set _ _ t => some t
  | .eend t    => some t
  | .retry t   => some t
  | .adm       => none

def isBegin : Label → Bool | .begin _ => true | _ => false
def isEnd   : Label → Bool | .eend _  => true | _ => false
def isRetry : Label → Bool | .retry _ => true | _ => false

/-- The value a `get`/`set` on location `x` carries (`HEvent_x`), if any. -/
def accVal (x : Loc) : Label → Option Nat
  | .get x' v _ => if x' = x then some v else none
  | .set x' v _ => if x' = x then some v else none
  | _           => none

/-- The value a `set` on `x` carries, if any (used for `T ⊢ Set x : n`). -/
def setVal (x : Loc) : Label → Option Nat
  | .set x' v _ => if x' = x then some v else none
  | _           => none

/-- Is this an access (`get` or `set`) on `x`? -/
def isAccessOn (x : Loc) (ℓ : Label) : Bool := (ℓ.accVal x).isSome

end Label

/-! ## Transactions (Definition "Transaction")

    A transaction `T = (E, po)` is the events sharing one tag `t`, in program
    (list) order; `po` is that order, automatically a total order. -/

/-- The events `E` of transaction `t`, in program order. -/
def txEvents (w : List Label) (t : TxId) : List Label :=
  w.filter (fun ℓ => ℓ.tag == some t)

/-- Every transaction identifier occurring in the trace (with repeats — the
    checks below are insensitive to repetition). -/
def tagsOf (w : List Label) : List TxId :=
  w.filterMap Label.tag

/-- Every location touched by a `get`/`set` in the trace. -/
def locsOf (w : List Label) : List Loc :=
  w.filterMap (fun ℓ => match ℓ with
    | .get x _ _ => some x
    | .set x _ _ => some x
    | _          => none)

/-! ## Committed / uncommitted (Definitions "Committed"/"Uncommitted transaction")

    `T` is committed when `min(T)` is a `begin@t` and `max(T)` is an `end@t`;
    since `po` is list order, that is: first event `begin@t`, last event
    `end@t`.  Otherwise `T` is uncommitted. -/

def committed (w : List Label) (t : TxId) : Bool :=
  (txEvents w t).head? == some (.begin t) && (txEvents w t).getLast? == some (.eend t)

def uncommitted (w : List Label) (t : TxId) : Bool := !committed w t

/-! ## Arbitration (Definition "Arbitration AR")

    `S <_AR T` iff `S`'s terminator (`end@S` or `retry@S`, i.e. its last event)
    precedes `begin@T` in the trace. -/

/-- The terminator event of transaction `t` (its `po`-greatest event). -/
def terminator (w : List Label) (t : TxId) : Option Label :=
  (txEvents w t).getLast?

/-- The first position of a label in the trace. -/
def idxOf (w : List Label) (ℓ : Label) : Option Nat :=
  w.findIdx? (· == ℓ)

def arb (w : List Label) (s t : TxId) : Bool :=
  match terminator w s, idxOf w (.begin t) with
  | some term, some bi =>
      match idxOf w term with
      | some ti => decide (ti < bi)
      | none    => false
  | _, _ => false

/-! ## History (Definition "History")

    `H = (T, AR)`: the set of all transactions and the arbitration order. -/

structure History where
  txs : List TxId          -- fst(H) = 𝐓, the transactions (by identifier)
  ar  : TxId → TxId → Bool  -- snd(H) = AR

def historyOf (w : List Label) : History := ⟨tagsOf w, arb w⟩

/-! ## The setter/getter judgements (Section "External consistency")

    `T ⊢ Set x : n`  — `T`'s `po`-last set of `x` has value `n`.
    `T ⊢ Get x : n`  — `T`'s `po`-first access to `x` is a get returning `n`
                       (an *external* get). -/

/-- `T ⊢ Set x : n`, as an `Option` giving `n` when `T` sets `x`. -/
def setJudg (w : List Label) (t : TxId) (x : Loc) : Option Nat :=
  ((txEvents w t).filterMap (Label.setVal x)).getLast?

/-- The external-get value of `x` by `T`: if `T`'s first access to `x` is a
    `get` returning `n`, that `n`; otherwise `none` (no access, or first access
    is a `set` — an internal read handled by `Int`). -/
def externalGet (w : List Label) (t : TxId) (x : Loc) : Option Nat :=
  match (txEvents w t).find? (Label.isAccessOn x) with
  | some (.get x' v _) => if x' = x then some v else none
  | _                  => none

/-! ## Small association helper -/

def assoc {α : Type} [BEq α] {β : Type} (k : α) : List (α × β) → Option β
  | []            => none
  | (a, b) :: rest => if a == k then some b else assoc k rest

/-! ## The internal-consistency check `Int` (Section "Internal consistency")

    For every `get(x,n)@t`, if the same transaction `t` has an earlier access to
    `x`, that `po`-latest earlier access carries `n`.  We fold left-to-right,
    keeping the last access value per `(t,x)`; at a `get` we require the stored
    value (if any) to match. -/

def intCheck (w : List Label) : Bool :=
  (w.foldl
    (fun (st : List ((TxId × Loc) × Nat) × Bool) ℓ =>
      match ℓ with
      | .get x v t =>
          let ok' := match assoc (t, x) st.1 with
                     | some p => st.2 && (p == v)
                     | none   => st.2
          (((t, x), v) :: st.1, ok')
      | .set x v t => (((t, x), v) :: st.1, st.2)
      | _          => st)
    (([] : List ((TxId × Loc) × Nat)), true)).2

/-! ## The external-consistency check `Ext` (Section "External consistency")

    An external `get` of `x` by `T` returns the value set by the `AR`-latest
    committed setter of `x` arbitrated before `T`, or `0` if there is none. -/

/-- Committed transactions that set `x` (the setter set `W_x`). -/
def committedSetters (w : List Label) (x : Loc) : List TxId :=
  (tagsOf w).filter (fun s => committed w s && (setJudg w s x).isSome)

/-- Members of `W_x` arbitrated before `t`  (`AR⁻¹(T) ∩ W_x`). -/
def arCandidates (w : List Label) (t : TxId) (x : Loc) : List TxId :=
  (committedSetters w x).filter (fun s => arb w s t)

/-- The `AR`-greatest of a candidate list (arbitration is a total order). -/
def arMax (w : List Label) : List TxId → Option TxId :=
  List.foldl (fun acc s =>
    match acc with
    | none   => some s
    | some a => if arb w a s then some s else some a) none

def extCheck (w : List Label) : Bool :=
  (tagsOf w).all (fun t => (locsOf w).all (fun x =>
    match externalGet w t x with
    | some n =>
        match arMax w (arCandidates w t x) with
        | some s => setJudg w s x == some n
        | none   => n == 0
    | none => true))

end Reagent
