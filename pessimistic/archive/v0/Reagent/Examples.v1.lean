/-
  Worked examples for Reagent V1, executed by the reference interpreter and
  checked against the paper.

    * Well-formedness is structural (an ill-formed `get` cannot fire; a thread
      cannot act inside another thread's transaction).
    * V1a — one thread, one transaction: `Int` and the `Ext` "no committed
      setter ⇒ read 0" case.
    * V1b — sequential / concurrent transactions: the `Ext` "committed setter is
      visible ⇒ read its value" case, with the transaction/committed/AR machinery.

  Run checks use `native_decide` (they *run* the compiled interpreter and the
  declarative checks); the general theorems `int_sound` / `ext_sound` are proved
  in `Reagent/Consistency.lean` and `Reagent/External.lean`.
-/
import Reagent.External

namespace Reagent
namespace Examples

/-- The single shared location `l`. -/
def l : Loc := 0

/-- Build a program from a command list, ending in `unit`. -/
def cmds (cs : List Expr) : Expr := cs.foldr Expr.seq .unit

def emp : ThreadMap := fun _ => .unit
def mk1 (e : Expr) : ThreadMap := update emp 1 e
def mk2 (e₁ e₂ : Expr) : ThreadMap := update (update emp 1 e₁) 2 e₂

/-! ### Well-formedness is structural -/

-- An ill-formed `get(l)` with no enclosing `begin` cannot fire (λ = ⊥ ≠ 1).
example : machineStep (init (mk1 (cmds [.getc l]))) 0 1 = none := by native_decide

/-- `{1 : begin ; get(l) ; end,  2 : get(l)}`. -/
def E₀wf : ThreadMap := mk2 (cmds [.begin, .getc l, .eend]) (cmds [.getc l])

-- Thread 1's `begin` makes it the owner: λ = 1.
example : (machineStep (init E₀wf) 0 1).map (fun x => x.1.lam) = some (some 1) := by native_decide

-- With λ = 1, thread 2's bare `get(l)` is not enabled.
example :
    (do let (C₁, f₁, _) ← machineStep (init E₀wf) 0 1
        machineStep C₁ f₁ 2) = none := by native_decide

/-! ### V1a — one thread, one transaction

    `begin ; get(l) ; set(l,1) ; end`. The read is external (first access to `l`)
    and there is no committed setter, so `Ext` forces it to `0`; then `Int`
    governs nothing further and the store ends at `1`. -/
def run1 : List Label := (runPhases (init (mk1 (cmds [.begin, .getc l, .setc l 1, .eend]))) 0 [1]).2.2

example : run1 = [.begin 0, .get l 0 0, .set l 1 0, .eend 0] := by native_decide
example : (runPhases (init (mk1 (cmds [.begin, .getc l, .setc l 1, .eend]))) 0 [1]).1.store l = 1 := by native_decide
-- transaction t0 is committed; its terminator is end@t0.
example : committed run1 0 = true := by native_decide
example : maxPo run1 0 = some (.eend 0) := by native_decide
example : minPo run1 0 = some (.begin 0) := by native_decide
-- both axioms hold on the run.
example : intCheck run1 = true := by native_decide
example : extCheck run1 = true := by native_decide

/-! ### V1b — a committed setter is visible

    Thread 1 commits `set(l,7)`; thread 2 then reads `l` externally and must see
    `7`. (Transaction ids: t0 for thread 1, t1 for thread 2.) -/
def run2 : List Label :=
  (runPhases (init (mk2 (cmds [.begin, .setc l 7, .eend]) (cmds [.begin, .getc l, .eend]))) 0 [1, 2]).2.2

example : run2 = [.begin 0, .set l 7 0, .eend 0, .begin 1, .get l 7 1, .eend 1] := by native_decide
-- thread 2's external get of l returns 7 …
example : externalGet run2 1 l = some 7 := by native_decide
-- … t0 is a committed setter of l with value 7, arbitrated before t1 …
example : committed run2 0 = true := by native_decide
example : setJudg run2 0 l = some 7 := by native_decide
example : arb run2 0 1 = true := by native_decide
-- … and both axioms hold.
example : intCheck run2 = true := by native_decide
example : extCheck run2 = true := by native_decide

/-! ### `Int` actually constrains

    If a read reported a value inconsistent with an earlier same-transaction
    access, `intCheck` rejects it. -/
def intBad : List Label := [.begin 0, .set l 5 0, .get l 3 0, .eend 0]
example : intCheck intBad = false := by native_decide

/-! ### The committed value, via the general lemma (not `native_decide`)

    `lcs_commit`: a committed `set(l,7)` makes the committed value of `l` be 7. -/
example : lcs l (.begin 0 :: ([.set l 7 0] ++ [.eend 0])) = 7 := by
  rw [lcs_commit l 0 [.set l 7 0] (by intro ℓ h; rw [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl⟩)]
  rfl

/-! ### Human-readable traces -/

def Label.pretty : Label → String
  | .begin t   => s!"begin@t{t}"
  | .eend t    => s!"end@t{t}"
  | .get l v t => s!"get({l},{v})@t{t}"
  | .set l v t => s!"set({l},{v})@t{t}"

#eval run1.map Label.pretty
#eval run2.map Label.pretty
#eval (txEvents run2 0).map Label.pretty  -- events of transaction t0
#eval (txEvents run2 1).map Label.pretty  -- events of transaction t1

end Examples
end Reagent
