/-
  Worked runs against the operational semantics.

  These are not tests of the two theorems — they are evidence that the rules
  can *fire*. `Trans` is a `Prop` with existentially quantified thread, context
  and redex, so a rule that accidentally matched nothing would leave `Int` and
  `Ext` provable and vacuously true. Every example below therefore exhibits a
  concrete run, built by applying the constructors.

  The runs here document the `retry` continuation gap recorded in `README.md`:
  `Begin` saves only the continuation `e` from the redex `begin ; e`, while
  `Retry` re-arms the thread as `ECtx[begin ; Ê]` using the context at the
  *retry* site. When those two contexts differ, the enclosing continuation is
  silently discarded.

  (The document is itself ambiguous here: its rule figure plugs into `ECtx`,
  while §"The command rules in context form" sets `Ê = ECtx[()]`. Resolving
  that is a decision for `docs/reagent-correctness.tex`, not for Lean.)
-/
import Reagent.ExtConsistency

namespace Reagent
namespace Examples

/-- Thread `0` runs `let x = (begin ; get 0) in retry`.

The `retry` sits inside `let x = □ in _`, but the `begin` that armed the
transaction sits inside the *same* `let` — so at the moment `Retry` fires the
surrounding context is already gone. -/
def P : ThreadMap := fun _ => .letx 0 (.seq .begin (.getc 0)) .retry

/-- `begin`, discard the unit, read `0`, substitute for `x`, `retry`. -/
def retrySteps : List TLabel :=
  [.ev (.begin 0), .adm, .ev (.get 0 0 0), .adm, .ev (.retry 0)]

/-- **The gap.** After the `retry`, thread `0` is `begin ; get 0` — the
`let x = □ in retry` continuation has been dropped, so the retried attempt can
no longer reach a `retry` at all. The lock is correctly released. -/
theorem retry_drops_context :
    ∃ C, Trace (initConfig P) retrySteps C ∧
         C.threadMap 0 = .seq .begin (.getc 0) ∧
         C.activeThread = none := by
  refine ⟨_,
    Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl Head.begin)
      (Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl
          (Head.adm Local.seqUnit))
        (Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl (Head.get rfl))
          (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl (Head.adm Local.letv))
            (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl Head.retry) Trace.nil)))),
    ?_, ?_⟩
  · rfl
  · rfl

/-- The same run, continued: the re-armed body opens a *fresh* transaction and
runs to a value. -/
def deadlockSteps : List TLabel :=
  retrySteps ++ [.ev (.begin 1), .adm, .ev (.get 0 0 1)]

/-- **The consequence.** Thread `0` finishes as the value `0` while still
holding the lock: `λ = 0` and `θ = t₁`, with no `end` left anywhere in its
expression to release them. No other thread can ever `begin` again.

Note this is a property of the *run*, not of the axioms — `Int` and `Ext` say
nothing about which continuation a `retry` resumes, so both still hold here. -/
theorem retry_deadlocks :
    ∃ C, Trace (initConfig P) deadlockSteps C ∧
         C.threadMap 0 = .val (.num 0) ∧
         C.activeThread = some 0 ∧ C.activeTx = some 1 := by
  refine ⟨_,
    Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl Head.begin)
      (Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl
          (Head.adm Local.seqUnit))
        (Trace.cons (Trans.ctx (i := 0) (K := .letx 0 .hole .retry) rfl (Head.get rfl))
          (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl (Head.adm Local.letv))
            (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl Head.retry)
              (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl Head.begin)
                (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl (Head.adm Local.seqUnit))
                  (Trace.cons (Trans.ctx (i := 0) (K := .hole) rfl (Head.get rfl))
                    Trace.nil))))))),
    ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-! ### The declarative model on that run

Read off `retrySteps`, transaction `t₀` runs `begin · get · retry`. The two
administrative steps consume positions `1` and `3` but are not events, so the
identifiers are `0`, `2`, `4`. -/

example : traceEvents retrySteps =
    [⟨0, .begin 0⟩, ⟨2, .get 0 0 0⟩, ⟨4, .retry 0⟩] := rfl

example : txIds retrySteps = [0] := rfl

/-- `t₀` opened with a `begin` … -/
example : (transactionOf retrySteps 0).minPo = some ⟨0, .begin 0⟩ := rfl

/-- … and its `po`-greatest event is the `retry`, so it is **not** committed. -/
example : (transactionOf retrySteps 0).maxPo = some ⟨4, .retry 0⟩ := rfl

example : ¬ (transactionOf retrySteps 0).Committed := by
  refine not_committed_of_maxPo (e := ⟨4, .retry 0⟩) rfl ?_
  rfl

end Examples
end Reagent
