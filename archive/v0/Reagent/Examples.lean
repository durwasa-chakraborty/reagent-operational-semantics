/-
  Worked examples of `docs/reagent-correctness.tex`, executed by the reference
  interpreter and checked against the paper.

    * Well-formedness is structural (Section "Worked example"):
      an ill-formed `get` cannot fire; a thread cannot act in another's
      transaction.
    * The declarative pipeline (Section "Traces, Transactions, and Histories"):
      the paper's running trace τ, its transactions, committed/uncommitted
      status, and arbitration.
    * The two consistency axioms (Section "Consistency") on real runs:
      a committed setter is visible (`get` forced to 7); an aborted setter is
      not (`get` forced to 0).

  Bool checks are discharged by `native_decide`, i.e. by *running* the compiled
  interpreter and the declarative checks of `Reagent/Trace.lean`.  The general
  theorem `int_sound` (every trace is internally consistent) is in
  `Reagent/Consistency.lean`.
-/
import Reagent.External

namespace Reagent
namespace Examples

/-- The single shared location `l`. -/
def l : Loc := 0

/-- `{1 : e}` and `{1 : e₁, 2 : e₂}`. -/
def emp : ThreadMap := fun _ => none
def mk1 (e : Expr) : ThreadMap := ThreadMap.upd emp 1 e
def mk2 (e₁ e₂ : Expr) : ThreadMap := ThreadMap.upd (ThreadMap.upd emp 1 e₁) 2 e₂

/-! ### Well-formedness is structural -/

-- An ill-formed `get(l)` with no enclosing `begin` cannot fire (λ = ⊥ ≠ 1).
example : machineStep (init (mk1 (.get l))) 0 1 = none := by native_decide

/-- `E₀ = {1 : begin ; (get(l) ; end),  2 : get(l)}`. -/
def E₀wf : ThreadMap := mk2 (.seq .begin (.seq (.get l) .eend)) (.get l)

-- Thread 1's `begin` makes it the owner: λ = 1 (a *thread* id).
example : (machineStep (init E₀wf) 0 1).map (fun x => x.1.lam) = some (some 1) := by native_decide

-- With λ = 1, thread 2's `get(l)` is not enabled — it cannot read inside thread
-- 1's transaction.
example :
    (do let (C₁, f₁, _) ← machineStep (init E₀wf) 0 1
        machineStep C₁ f₁ 2) = none := by native_decide

/-! ### Program encodings -/

/-- `begin ; (set(l,v) ; end)` — a committing setter. -/
def setEnd (v : Nat) : Expr := .seq .begin (.seq (.set l (.val (.nat v))) .eend)
/-- `begin ; (set(l,v) ; retry)` — an aborting setter. -/
def setRetry (v : Nat) : Expr := .seq .begin (.seq (.set l (.val (.nat v))) .retry)
/-- `begin ; (let z = get(l) in end)` — an external reader of `l`. -/
def readEnd : Expr := .seq .begin (.lett "z" (.get l) .eend)
/-- `begin ; (let x = get(l) in set(l, x+1)) ; end)` — an increment. -/
def incr : Expr :=
  .seq .begin (.seq (.lett "x" (.get l) (.set l (.add (.var "x") (.val (.nat 1))))) .eend)

/-! ### Internal consistency on a real run

    A single increment: `get(l,0)` then `set(l,1)`.  The read has no earlier
    access, so `Int` is vacuous on it; the trace is internally consistent and
    ends at `σ(l) = 1`. -/
def incrRun : List Label := (runPhases (init (mk1 incr)) 0 [1]).2.2

example : intCheck incrRun = true := by native_decide
example : (runPhases (init (mk1 incr)) 0 [1]).1.store l = 1 := by native_decide

/-! ### External consistency: a committed setter is visible

    Thread 1 commits `set(l,7)`; thread 2 then reads `l` externally and must see
    `7`.  (Transaction ids: thread 1 opens `t0`, thread 2 opens `t1`.) -/
def extRun1 : List Label := (runPhases (init (mk2 (setEnd 7) readEnd)) 0 [1, 2]).2.2

-- Thread 2's external get of l returns 7 …
example : externalGet extRun1 1 l = some 7 := by native_decide
-- … thread 1's transaction t0 is committed and sets l to 7 …
example : committed extRun1 0 = true := by native_decide
example : setJudg extRun1 0 l = some 7 := by native_decide
-- … it is arbitrated before t1 …
example : arb extRun1 0 1 = true := by native_decide
-- … and both consistency axioms hold on the run.
example : extCheck extRun1 = true := by native_decide
example : intCheck extRun1 = true := by native_decide

/-! ### External consistency: an aborted setter is not visible

    Thread 1 does `set(l,2)` then `retry` (rolled back, uncommitted); thread 2
    then reads `l` externally and must see the initial `0`. -/
def extRun2 : List Label := (runPhases (init (mk2 (setRetry 2) readEnd)) 0 [1, 2]).2.2

-- Thread 1's transaction t0 is uncommitted (its terminator is a retry) …
example : committed extRun2 0 = false := by native_decide
-- … so thread 2's external get of l falls back to the initial value 0 …
example : externalGet extRun2 1 l = some 0 := by native_decide
-- … and external consistency still holds.
example : extCheck extRun2 = true := by native_decide

/-! ### The general external-consistency lemmas, applied

    Not `native_decide`: these use the proven `cstore_commit` / `cstore_abort`
    of `Reagent/External.lean` on the doc's two Ext scenarios.  A committed
    `set(l,7)` makes the committed value `7`; an aborted `set(l,2)` (rolled back
    on `retry`) leaves the committed value at its prior `0`. -/

example : cstore l (.begin 0 :: ([.adm, .set l 7 0, .adm] ++ [.eend 0])) = 7 := by
  rw [cstore, cstore_commit l 0 [.adm, .set l 7 0, .adm] (by unfold Boundaryless; decide) 0 none]
  decide

example : cstore l (.begin 0 :: ([.adm, .set l 2 0, .adm] ++ [.retry 0])) = 0 := by
  rw [cstore, cstore_abort l 0 [.adm, .set l 2 0, .adm] (by unfold Boundaryless; decide) 0 none]

/-! ### The paper's running trace τ (Section "Traces, Transactions, and Histories")

    τ = begin@t₁ · get(l,0)@t₁ · ℓ_adm · ℓ_adm · set(l,1)@t₁ · end@t₁
        · begin@t₂ · get(l,1)@t₂ · retry@t₂. -/
def tau : List Label :=
  [.begin 1, .get l 0 1, .adm, .adm, .set l 1 1, .eend 1,
   .begin 2, .get l 1 2, .retry 2]

-- Transaction t₁ is committed (min = begin, max = end); t₂ is uncommitted
-- (max = retry).
example : committed tau 1 = true := by native_decide
example : committed tau 2 = false := by native_decide
example : uncommitted tau 2 = true := by native_decide
-- Arbitration: end@t₁ precedes begin@t₂, so t₁ <_AR t₂.
example : arb tau 1 2 = true := by native_decide
-- τ is internally consistent.
example : intCheck tau = true := by native_decide

/-! ### `Int` needs no commit, and actually constrains

    Both transactions below abort/pend, yet `Int` pins both reads: `get(x,2)`
    must match the earlier `set(x,2)`, and `get(x,5)` the earlier `set(x,5)`. -/
def intNoCommit : List Label :=
  [.begin 1, .set l 2 1, .get l 2 1, .retry 1, .begin 2, .set l 5 2, .get l 5 2]

example : intCheck intNoCommit = true := by native_decide

-- If the second read reported the wrong value (3 instead of 5), `Int` rejects it:
def intBad : List Label :=
  [.begin 1, .set l 2 1, .get l 2 1, .retry 1, .begin 2, .set l 5 2, .get l 3 2]

example : intCheck intBad = false := by native_decide

/-! ### Human-readable output -/

def Label.pretty : Label → String
  | .begin t   => s!"begin@t{t}"
  | .eend t    => s!"end@t{t}"
  | .retry t   => s!"retry@t{t}"
  | .get l v t => s!"get({l},{v})@t{t}"
  | .set l v t => s!"set({l},{v})@t{t}"
  | .adm       => "adm"

#eval extRun1.map Label.pretty
#eval extRun2.map Label.pretty
#eval (txEvents tau 1).map Label.pretty  -- events of transaction t₁
#eval (txEvents tau 2).map Label.pretty  -- events of transaction t₂

end Examples
end Reagent
