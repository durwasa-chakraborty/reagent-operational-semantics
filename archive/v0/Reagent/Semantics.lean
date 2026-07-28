/-
  Operational semantics of the Reagent language
  (Section "Semantics", "Evaluation contexts", "Administrative reductions",
  and "Local (pure) reductions / Lifting" of `docs/reagent-correctness.tex`).

  Every transition carries a label.  The five command rules Get/Set/Begin/End/
  Retry emit their transition labels; the `Local` rule lifts a pure redex
  reduction and emits the administrative label `ℓ_adm`.  A trace is then the
  sequence of *all* labels along a run — transition labels and administrative
  labels alike — matching the paper's Definition (Trace).
-/
import Reagent.Syntax

namespace Reagent

/-! ## Visible labels

    A label is either a *transition* label (`begin@t`, `get(l,v)@t`,
    `set(l,v)@t`, `end@t`, `retry@t`) or the *administrative* label `ℓ_adm`
    of an internal reduction. -/
inductive Label where
  | begin : TxId → Label
  | get   : Loc → Nat → TxId → Label
  | set   : Loc → Nat → TxId → Label
  | eend  : TxId → Label
  | retry : TxId → Label
  | adm   : Label
deriving DecidableEq, Repr

/-! ## Evaluation contexts -/

/-- Evaluation contexts `H`:
      H ::= [·] ∣ H;e ∣ let x = H in e ∣ H+e ∣ v+H
          ∣ H==e ∣ v==H ∣ if H then e else e ∣ set(l,H). -/
inductive Ctx where
  | hole : Ctx
  | seqL : Ctx → Expr → Ctx
  | lett : String → Ctx → Expr → Ctx
  | addL : Ctx → Expr → Ctx
  | addR : Val → Ctx → Ctx
  | eqL  : Ctx → Expr → Ctx
  | eqR  : Val → Ctx → Ctx
  | ite  : Ctx → Expr → Expr → Ctx
  | setR : Loc → Ctx → Ctx

/-- Plug an expression into the hole, `H[e]`. -/
def plug : Ctx → Expr → Expr
  | .hole,        e => e
  | .seqL c e2,   e => .seq (plug c e) e2
  | .lett x c e2, e => .lett x (plug c e) e2
  | .addL c e2,   e => .add (plug c e) e2
  | .addR v c,    e => .add (.val v) (plug c e)
  | .eqL c e2,    e => .eq (plug c e) e2
  | .eqR v c,     e => .eq (.val v) (plug c e)
  | .ite c e1 e2, e => .ite (plug c e) e1 e2
  | .setR l c,    e => .set l (plug c e)

/-! ## Local (pure) reductions `e ⇝ e'`

    Addition, equality, `let`, `();e`, and `if` never touch the store or the
    transaction state (Section "Local (pure) reductions").  `();e ⇝ e` and the
    `==` step are included from the administrative-reductions list, since the
    worked examples need them. -/
inductive Pure : Expr → Expr → Prop where
  | add  {a b}   : Pure (.add (.val (.nat a)) (.val (.nat b))) (.val (.nat (a + b)))
  | eq   {a b}   : Pure (.eq (.val (.nat a)) (.val (.nat b))) (.val (.bool (a == b)))
  | lett {x v e} : Pure (.lett x (.val v) e) (e.subst x v)
  | seq  {e}     : Pure (.seq (.val .unit) e) e
  | iteT {e₁ e₂} : Pure (.ite (.val (.bool true)) e₁ e₂) e₁
  | iteF {e₁ e₂} : Pure (.ite (.val (.bool false)) e₁ e₂) e₂

/-! ## The labelled transition relation

    The five command rules of the Figure plus the `Local` lifting rule.  Every
    transactional rule (Get, Set, End, Retry) requires `λ = i` (only the owner
    thread may step) and `θ = t` (a transaction is live, supplying the tag). -/
inductive Trans : Config → Label → Config → Prop where
  | get {C i H l t v} :
      C.threads i = some (plug H (.get l)) →
      C.lam = some i →
      C.theta = some t →
      C.store l = v →
      Trans C (.get l v t)
        { C with threads := C.threads.upd i (plug H (.val (.nat v))) }
  | set {C i H l t n} :
      C.threads i = some (plug H (.set l (.val (.nat n)))) →
      C.lam = some i →
      C.theta = some t →
      Trans C (.set l n t)
        { C with store := C.store.upd l n,
                 threads := C.threads.upd i (plug H (.val .unit)) }
  | begin {C i H t e} :
      C.threads i = some (plug H (.seq .begin e)) →
      C.lam = none →
      Trans C (.begin t)
        { C with lam := some i,
                 theta := some t,
                 threads := C.threads.upd i (plug H (.seq (.val .unit) e)),
                 snap := C.store,
                 saved := e }
  | eend {C i H t} :
      C.threads i = some (plug H .eend) →
      C.lam = some i →
      C.theta = some t →
      Trans C (.eend t)
        { C with lam := none,
                 theta := none,
                 threads := C.threads.upd i (plug H (.val .unit)) }
  | retry {C i H t} :
      C.threads i = some (plug H .retry) →
      C.lam = some i →
      C.theta = some t →
      Trans C (.retry t)
        { C with store := C.snap,
                 lam := none,
                 theta := none,
                 threads := C.threads.upd i (.seq .begin C.saved) }
  | adm {C i H r e} :
      C.threads i = some (plug H r) →
      Pure r e →
      Trans C .adm
        { C with threads := C.threads.upd i (plug H e) }

/-! ## Traces (Definition "Trace")

    A trace of a run `C₀ --ℓ₁--> C₁ --ℓ₂--> ⋯ --ℓₖ--> Cₖ` is the sequence of
    labels `ℓ₁ ℓ₂ ⋯ ℓₖ` between the configurations. -/
inductive Trace : Config → List Label → Config → Prop where
  | nil  {C} : Trace C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Trace C' w C'' → Trace C (ℓ :: w) C''

/-- Reachability. -/
def Reaches (C C' : Config) : Prop := ∃ w, Trace C w C'

/-- Append two traces. -/
theorem Trace.append {C w₁ C' w₂ C''} (h₁ : Trace C w₁ C') (h₂ : Trace C' w₂ C'') :
    Trace C (w₁ ++ w₂) C'' := by
  induction h₁ with
  | nil => exact h₂
  | cons tr _ ih => exact .cons tr (ih h₂)

/-! ## Initial configurations (Section "Initial configuration and termination") -/

/-- An initial configuration `⟨σ₀, ⊥, ⊥, E₀, σ₀, ()⟩` with the zero store
    (the paper's `σ₀(l) = 0`). -/
def init (E₀ : ThreadMap) : Config :=
  { store := Store.zero, lam := none, theta := none, threads := E₀,
    snap := Store.zero, saved := .val .unit }

/-! ## Executable stepper (the runnable machinery)

    An executable image of `Trans`: reduce the acting thread `i` once, emitting
    the same label the relation would.  Pure redexes emit `ℓ_adm`. -/

structure ER where
  expr  : Expr
  store : Store
  lam   : Option ThId
  theta : Option TxId
  snap  : Store
  saved : Expr
  fresh : Nat
  label : Label

def stepE (i : ThId) (σ : Store) (lam : Option ThId) (theta : Option TxId)
    (snap : Store) (saved : Expr) (fresh : Nat) : Expr → Option ER
  | .get l =>
      match lam, theta with
      | some j, some t =>
          if j = i then some ⟨.val (.nat (σ l)), σ, lam, theta, snap, saved, fresh, .get l (σ l) t⟩
          else none
      | _, _ => none
  | .set l a =>
      match a with
      | .val (.nat n) =>
          match lam, theta with
          | some j, some t =>
              if j = i then some ⟨.val .unit, σ.upd l n, lam, theta, snap, saved, fresh, .set l n t⟩
              else none
          | _, _ => none
      | .val _ => none
      | a      => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .set l r.expr })
  | .eend =>
      match lam, theta with
      | some j, some t => if j = i then some ⟨.val .unit, σ, none, none, snap, saved, fresh, .eend t⟩ else none
      | _, _ => none
  | .retry =>
      match lam, theta with
      | some j, some t => if j = i then some ⟨.seq .begin saved, snap, none, none, snap, saved, fresh, .retry t⟩ else none
      | _, _ => none
  | .seq a b =>
      match a with
      | .begin =>
          match lam with
          | none   => some ⟨.seq (.val .unit) b, σ, some i, some fresh, σ, b, fresh + 1, .begin fresh⟩
          | some _ => none
      | .val .unit => some ⟨b, σ, lam, theta, snap, saved, fresh, .adm⟩
      | .val _     => none
      | a          => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .seq r.expr b })
  | .lett x a b =>
      match a with
      | .val v => some ⟨b.subst x v, σ, lam, theta, snap, saved, fresh, .adm⟩
      | a      => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .lett x r.expr b })
  | .add a b =>
      match a, b with
      | .val (.nat n₁), .val (.nat n₂) => some ⟨.val (.nat (n₁ + n₂)), σ, lam, theta, snap, saved, fresh, .adm⟩
      | .val w, b => (stepE i σ lam theta snap saved fresh b).map (fun r => { r with expr := .add (.val w) r.expr })
      | a, b      => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .add r.expr b })
  | .eq a b =>
      match a, b with
      | .val (.nat n₁), .val (.nat n₂) => some ⟨.val (.bool (n₁ == n₂)), σ, lam, theta, snap, saved, fresh, .adm⟩
      | .val w, b => (stepE i σ lam theta snap saved fresh b).map (fun r => { r with expr := .eq (.val w) r.expr })
      | a, b      => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .eq r.expr b })
  | .ite a b c =>
      match a with
      | .val (.bool true)  => some ⟨b, σ, lam, theta, snap, saved, fresh, .adm⟩
      | .val (.bool false) => some ⟨c, σ, lam, theta, snap, saved, fresh, .adm⟩
      | .val _ => none
      | a      => (stepE i σ lam theta snap saved fresh a).map (fun r => { r with expr := .ite r.expr b c })
  | .begin =>
      match lam with
      | none   => some ⟨.val .unit, σ, some i, some fresh, σ, .val .unit, fresh + 1, .begin fresh⟩
      | some _ => none
  | .val _ => none
  | .var _ => none

/-- One machine step of thread `i`; `Retry` discards the aborted attempt's
    context (re-arming `begin ; Ê`), as the relational rule specifies. -/
def machineStep (C : Config) (fresh : Nat) (i : ThId) :
    Option (Config × Nat × Label) :=
  match C.threads i with
  | none   => none
  | some e =>
    match stepE i C.store C.lam C.theta C.snap C.saved fresh e with
    | none   => none
    | some r =>
        let newExpr :=
          match r.label with
          | .retry _ => Expr.seq .begin r.saved
          | _        => r.expr
        some ({ store := r.store, lam := r.lam, theta := r.theta,
                threads := C.threads.upd i newExpr,
                snap := r.snap, saved := r.saved }, r.fresh, r.label)

/-- Run thread `i` (up to `fuel` steps) until it yields the lock — it blocks,
    finishes, or emits `end@t`/`retry@t` — collecting all labels (incl. `ℓ_adm`). -/
def runYield : Nat → Config → Nat → ThId → Config × Nat × List Label
  | 0,       C, f, _ => (C, f, [])
  | fuel + 1, C, f, i =>
    match machineStep C f i with
    | none => (C, f, [])
    | some (C', f', lbl) =>
      match lbl with
      | .retry _ => (C', f', [lbl])
      | .eend _  => (C', f', [lbl])
      | _ =>
        let (C'', f'', ls) := runYield fuel C' f' i
        (C'', f'', lbl :: ls)

/-- Drive the machine through a list of scheduling *phases*: run each listed
    thread until it yields the lock. -/
def runPhases : Config → Nat → List ThId → Config × Nat × List Label
  | C, f, []      => (C, f, [])
  | C, f, i :: is =>
    let (C', f', ls)   := runYield 1000 C f i
    let (C'', f'', ls') := runPhases C' f' is
    (C'', f'', ls ++ ls')

end Reagent
