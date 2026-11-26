/-
  What the main theorem talks about: the witness history, Int, and Ext.
  Definitions only, plus the two facts we assume for now (HistoryOf, Int).
-/
import Optimistic.Trace

namespace Optimistic

open Reagent (Loc TxId ThreadMap Store)

/-! ## The witness history -/

-- `fin S`: the trace contains a terminator of `S`.
def Finished (es : List Event) (t : TxId) : Prop := ∃ a, Terminates es t a

-- The witness `AR`: finished transactions by their terminators, finished
-- before pending, pending by their `begin`.
def finishOrder (es : List Event) (S T : Transaction) : Prop :=
  (∃ a b, Terminates es S.txid a ∧ Terminates es T.txid b ∧ OccursBefore es a b)
  ∨ (Finished es S.txid ∧ ¬ Finished es T.txid)
  ∨ (¬ Finished es S.txid ∧ ¬ Finished es T.txid ∧
      ∃ a b, Begins es S.txid a ∧ Begins es T.txid b ∧ OccursBefore es a b)

-- `H := (txs(τ), AR)`, built from `τ` and nothing else.
def witness (τ : Trace) : History := ⟨txsOfTrace τ, finishOrder (events τ)⟩

/-! ## Int -/

-- `HEvent_x`: the label is a `get` or a `set` on `x`.
def Label.accesses (x : Loc) : Label → Bool
  | .get l _ _ => l == x
  | .set l _ _ => l == x
  | _          => false

-- The value a `get` or a `set` carries.
def Label.accessVal : Label → Option Nat
  | .get _ v _ => some v
  | .set _ v _ => some v
  | _          => none

-- `a ∈ P_x(e) = po⁻¹(e) ∩ HEvent_x`.
def Transaction.PriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.po a e ∧ a.val.label.accesses x = true

-- `a = max_po P_x(e)`.
def Transaction.MaxPriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.PriorAccess x a e ∧ ∀ b, T.PriorAccess x b e → b = a ∨ T.po b a

-- `e = get(x,n) ∧ P_x(e) ≠ ∅ → max_po P_x(e) = op(x,n)`.
def Transaction.Int (T : Transaction) : Prop :=
  ∀ (e : Subtype T.E) (x n : Nat) (t : TxId),
    e.val.label = .get x n t →
    ∀ a : Subtype T.E, T.MaxPriorAccess x a e → a.val.label.accessVal = some n

def History.Int (H : History) : Prop := ∀ T, H.txs T → T.Int

/-! ## Ext, part (a): committed readers -/

-- `T ⊢ Read(x, n)`: a `get(x, n)` with `po⁻¹(e) ∩ HEvent_x = ∅`.
def Transaction.ReadsExt (T : Transaction) (x : Loc) (n : Nat) : Prop :=
  ∃ e : Subtype T.E, (∃ t, e.val.label = .get x n t) ∧ ¬ ∃ a, T.PriorAccess x a e

-- `T ⊢ Write(x, n)`: the `po`-last `set` on `x` in `T` writes `n`.
def Transaction.WritesVal (T : Transaction) (x : Loc) (n : Nat) : Prop :=
  ∃ a : Subtype T.E, (∃ t, a.val.label = .set x n t) ∧
    ∀ b : Subtype T.E, (∃ t w, b.val.label = .set x w t) → ¬ T.po a b

-- `S ∈ W_x(T)`.
def History.InW (H : History) (x : Loc) (T S : Transaction) : Prop :=
  H.txs S ∧ S.status = .Committed ∧ S ≠ T ∧ H.ar S T ∧ ∃ v, S.WritesVal x v

-- `S = max_AR W_x(T)`.
def History.MaxW (H : History) (x : Loc) (T S : Transaction) : Prop :=
  H.InW x T S ∧ ∀ U, H.InW x T U → U = S ∨ H.ar U S

-- `Ext_c`: Cerone's Ext with `VIS = AR`, for committed readers.
def History.ExtC (H : History) : Prop :=
  ∀ T, H.txs T → T.status = .Committed → ∀ x n, T.ReadsExt x n →
    ((¬ ∃ S, H.InW x T S) ∧ n = Store.init_store x)
    ∨ ∃ S, H.MaxW x T S ∧ S.WritesVal x n

-- `P(τ)`: the witness history of `τ` satisfies `Ext_c`.
def ExtP (τ : Trace) : Prop := (witness τ).ExtC

/-! ## Ext, part (b): uncommitted readers -/

-- `VIS(S, e)`: `S` committed and its `end` comes before `e` in `es`.
def visOf (es : List Event) (S : Transaction) (e : Event) : Prop :=
  S.status = .Committed ∧ ∃ c ∈ es, c.label = .eend S.txid ∧ OccursBefore es c e

-- `S ∈ W_e`: `S` is visible to `e` and writes `x`.
def History.InVis (H : History) (VIS : Transaction → Event → Prop) (x : Loc) (e : Event)
    (S : Transaction) : Prop :=
  H.txs S ∧ VIS S e ∧ ∃ v, S.WritesVal x v

-- `S = max_AR W_e`.
def History.MaxVis (H : History) (VIS : Transaction → Event → Prop) (x : Loc) (e : Event)
    (S : Transaction) : Prop :=
  H.InVis VIS x e S ∧ ∀ U, H.InVis VIS x e U → U = S ∨ H.ar U S

-- `Ext_u`: every external read of an uncommitted `T` returns the value of
-- `max_AR W_e`, or `σ₀(x)` if `W_e = ∅`.
def History.ExtU (H : History) (VIS : Transaction → Event → Prop) : Prop :=
  ∀ T, H.txs T → T.status ≠ .Committed → ∀ x v (e : Subtype T.E), (∃ t, e.val.label = .get x v t) →
    (¬ ∃ a, T.PriorAccess x a e) →
    ((¬ ∃ S, H.InVis VIS x e.val S) ∧ v = Store.init_store x)
    ∨ ∃ S, H.MaxVis VIS x e.val S ∧ S.WritesVal x v

/-! ## Assumed for now -/

-- (1) The witness is a history of the run.
theorem witness_historyOf {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (hrun : Run (initConfig E₀) τ C) : HistoryOf τ (witness τ) := by
  sorry

-- (2) Int holds for every history of the run.
theorem int_of_run {E₀ : ThreadMap} {τ : Trace} {C : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C) (hH : HistoryOf τ H) : H.Int := by
  sorry

end Optimistic
