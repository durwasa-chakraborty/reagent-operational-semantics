/-
  The statement of External Consistency, part (a): `Ext_c` for committed
  readers, and `P(τ)`, the witness history of `τ` satisfies `Ext_c`.
-/
import Optimistic.IntConsistency

namespace Optimistic

open Reagent (Loc TxId Store)

/-! ## Statement -/

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

/-! ## Part (b): uncommitted transactions -/

-- `VIS(S, e)`: per operation. `S` committed and its `end` comes before `e` in
-- the trace `es`.
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

-- `Ext_op`: every external read `e = get(x, v)` of every `T` returns the value of
-- `max_AR W_e`, or `σ₀(x)` if `W_e = ∅`.
def History.ExtOp (H : History) (VIS : Transaction → Event → Prop) : Prop :=
  ∀ T, H.txs T → ∀ x v (e : Subtype T.E), (∃ t, e.val.label = .get x v t) →
    (¬ ∃ a, T.PriorAccess x a e) →
    ((¬ ∃ S, H.InVis VIS x e.val S) ∧ v = Store.init_store x)
    ∨ ∃ S, H.MaxVis VIS x e.val S ∧ S.WritesVal x v

-- `Ext_u`: `Ext_op` for uncommitted (retried or pending) `T`.
def History.ExtU (H : History) (VIS : Transaction → Event → Prop) : Prop :=
  ∀ T, H.txs T → T.status ≠ .Committed → ∀ x v (e : Subtype T.E), (∃ t, e.val.label = .get x v t) →
    (¬ ∃ a, T.PriorAccess x a e) →
    ((¬ ∃ S, H.InVis VIS x e.val S) ∧ v = Store.init_store x)
    ∨ ∃ S, H.MaxVis VIS x e.val S ∧ S.WritesVal x v

-- `Ext_u` is `Ext_op` restricted to uncommitted `T`.
theorem History.extU_of_extOp {H : History} {VIS : Transaction → Event → Prop}
    (h : H.ExtOp VIS) : H.ExtU VIS := by
  sorry

end Optimistic
