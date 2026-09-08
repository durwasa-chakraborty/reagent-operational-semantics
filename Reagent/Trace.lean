/-
  Reagent — runs.

  A run is a chain of `Trans` steps; its *trace* is the list of labels those
  steps emit, in order, administrative steps included.
-/
import Reagent.Semantics

namespace Reagent

/-- A trace: the sequence of labels emitted along a run, administrative steps
included. -/
inductive Trace : Config → List TLabel → Config → Prop where
  | nil  {C} : Trace C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Trace C' w C'' → Trace C (ℓ :: w) C''

/-- The initial configuration `⟨σ₀, ⊥, ⊥, E₀, σ₀, ()⟩`, minting ids from `0`. -/
def initConfig (E₀ : ThreadMap) : Config :=
  { store := Store.init_store, activeThread := none, activeTx := none,
    threadMap := E₀, snapshot := Store.init_store, savedBody := .val .unit,
    nextTx := 0 }

/-- How a transaction ended. -/
inductive Status where
  | Committed
  | Uncommitted
  | Retried
deriving DecidableEq, Repr

class IsTotalOrder {α : Type u} (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a
  antisymm : ∀ {a b}, r a b → r b a → a = b
  trans : ∀ {a b c}, r a b -> r b c -> r a c
  total : ∀ a b, r a b ∨ r b a

/-- Event -/
structure Event where
  id : Nat
  label : Label
deriving DecidableEq, Repr

-- TODO personally don't know what to make of this class as I would need an instance of
-- this type and for that the α would need to become E for say `PO` but I still can't compare
-- E so I have to rely on ℕ. Either way I had a list of Events and an `id` so not sure what this
-- will lead to but okay we now have a type IsTotalOrder. Also this could have been a
-- structure but then that would mean refl antisymm trans and total are all records.

structure Transaction where
  -- NOTE I have a feeling this will make the proof easier and maybe as we go ahead
  --  tx : TxId would be needed as AR won't be a total order anymore
  E : Event → Prop
  po : Subtype E →  Subtype E → Prop
  status : Status
  [isOrder : IsTotalOrder po]

structure History where
  txs : Transaction → Prop
  ar : Subtype txs → Subtype txs → Prop

-- NOTE the following section is KC sir's function that takes a trace and gives us History
-- NOTE I need a helper to know where the begin sits
def Label.tx : Label → TxId
  | .begin t   => t
  | .get _ _ t => t
  | .set _ _ t => t
  | .eend t    => t
  | .retry t   => t

-- NOTE the way the INT and EXT work we only need to worry about get and sets rest everything including adm
-- will be filtered out and the only thing that makes up H will only have get set
def Label.isAccess : Label → Bool
  | .get ..  => true
  | .set ..  => true
  | _         => false

def eventsOf (ℓs : List TLabel) (t : TxId) : Event → Prop :=
  fun e => ℓs[e.id]? = some (.ev e.label) ∧ e.label.tx = t ∧ e.label.isAccess = true

def poOf (ℓs : List TLabel) (t : TxId) : Subtype (eventsOf ℓs t) → Subtype (eventsOf ℓs t ) → Prop :=
  fun a b => a.val.id ≤ b.val.id

def statusOf (ℓs : List TLabel) (t : TxId) : Status :=
    if ℓs.contains (.ev (.eend t)) then .Committed
    else if ℓs.contains (.ev (.retry t)) then .Retried
    else .Uncommitted

theorem poOf_isOrder (ℓs : List TLabel) (t : TxId) : IsTotalOrder (poOf ℓs t) := sorry
def transactionOf (ℓs : List TLabel) (t : TxId) : Transaction where
    E       := eventsOf ℓs t
    po      := poOf ℓs t
    status  := statusOf ℓs t
    isOrder := poOf_isOrder ℓs t

def beginPos (ℓs : List TLabel) (t: TxId) (i : Nat) : Prop := ℓs[i]? = some (.ev (.begin t))
def termPos  (ℓs : List TLabel) (t: TxId) (i : Nat) : Prop := ℓs[i]? = some (.ev (.eend t)) ∨ ℓs[i]? = some (.ev (.retry t))

def arId     (ℓs : List TLabel) (s t : TxId) : Prop := s = t ∨ ∃ i j, termPos ℓs s i ∧ beginPos ℓs t j ∧ i < j
def txOccurs (ℓs : List TLabel) ( t : TxId) : Prop := ∃ ℓ, TLabel.ev ℓ ∈ ℓs ∧ ℓ.tx = t
def txsOf (ℓs : List TLabel) : Transaction → Prop := fun T => ∃ t, txOccurs ℓs t ∧ T = transactionOf ℓs t

-- NOTE The following section takes care HistoryOf  -----------------------------------------------------------------
-- NOTE We are deliberately using Tx without a TxId
-- TODO Discuss the gotchas of txid

-- Some event that carries the tag t
def HasTx (T : Transaction) (t : TxId) : Prop := ∃ e, T.E e ∧ e.label.tx = t
-- Did e occur in τ
def OccursIn (τ : List TLabel) (e : Event) : Prop := τ[e.id]? = some (.ev e.label)

-- Helper Methods for HasBegin HasEnd HasRetry
def HasBegin (τ : List TLabel) (t : TxId) : Prop := TLabel.ev (.begin t) ∈ τ
def HasEnd   (τ : List TLabel) (t : TxId) : Prop := TLabel.ev (.eend t) ∈ τ
def HasRetry (τ : List TLabel) (t : TxId) : Prop := TLabel.ev (.retry t) ∈ τ

structure HistoryOf (τ : List TLabel) (H : History) : Prop where
  -- NOTE Axiom A-B Txs is exactly the transactions of τ
  no_spurios : ∀ T, H.txs T → ∀ t, HasTx T t → HasBegin τ t
  no_missing : ∀ t, HasBegin τ t → ∃ T, H.txs T ∧ HasTx T t

  -- NOTE Axiom C-D-E-F Status is a termininator
  committed : ∀ T, H.txs T → ∀ t, HasTx T t → HasEnd τ t → T.status = .Committed
  retried : ∀ T, H.txs T → ∀ t, HasTx T t → HasRetry τ t → T.status = .Retried
  uncommitted : ∀ T, H.txs T → ∀ t, HasTx T t → ¬ HasEnd τ t → ¬ HasRetry τ t →  T.status = .Uncommitted
  unique_terminator : ∀ t, ¬ (HasEnd τ t ∧ HasRetry τ t)




end Reagent
