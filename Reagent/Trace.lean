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

/-- An event: an opaque identifier paired with an operation — Cerone's `(i, op)`.

`id` exists for exactly one reason: to tell two *identical* operations apart, so
that `begin@t · get(x,5)@t · get(x,5)@t` has two events and not one.  It is a
name, never an order.  Nothing outside `HistoryOf` may compare two `id`s; the
only thing that orders events is `po`, and the only thing that locates them in a
trace is the placement `pos` carried by `HistoryOf`. -/
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
  po :  Subtype E →  Subtype E → Prop
  status : Status
  [isOrder : IsTotalOrder po]

structure History where
  txs : Transaction → Prop
  ar : Subtype txs → Subtype txs → Prop
  -- TODO add ar to be total order

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
-- TODO refine type
def Label.isAccess : Label → Bool
  | .get ..  => true
  | .set ..  => true
  | _         => false

/-- Two events with the same id and the same label are the same event. -/
theorem Event.eq_of_fields {e f : Event} (hi : e.id = f.id) (hl : e.label = f.label) :
    e = f := by
  cases e; cases f; simp_all

def eventsOf (ℓs : List TLabel) (t : TxId) : Event → Prop :=
  fun e => ℓs[e.id]? = some (.ev e.label) ∧ e.label.tx = t ∧ e.label.isAccess = true

def poOf (ℓs : List TLabel) (t : TxId) : Subtype (eventsOf ℓs t) → Subtype (eventsOf ℓs t ) → Prop :=
  fun a b => a.val.id ≤ b.val.id

def statusOf (ℓs : List TLabel) (t : TxId) : Status :=
    if ℓs.contains (.ev (.eend t)) then .Committed
    else if ℓs.contains (.ev (.retry t)) then .Retried
    else .Uncommitted

/-- `refl`, `trans` and `total` are just `≤` on `Nat`.  `antisymm` is the one
with content: two events of `eventsOf` with the same id are the *same event*,
because `eventsOf` pins each event's label to `ℓs[id]`, and a list holds one
label at a position.  Placement buys injectivity; nothing has to assume it. -/
theorem poOf_isOrder (ℓs : List TLabel) (t : TxId) : IsTotalOrder (poOf ℓs t) where
  refl a := Nat.le_refl _
  trans hab hbc := Nat.le_trans hab hbc
  total a b := Nat.le_total _ _
  antisymm {a b} hab hba := by
    have hid : a.val.id = b.val.id := Nat.le_antisymm hab hba
    have ha := a.property.1
    have hb := b.property.1
    rw [hid] at ha
    have hlab : a.val.label = b.val.label := by simpa using ha.symm.trans hb
    exact Subtype.ext (Event.eq_of_fields hid hlab)
def transactionOf (ℓs : List TLabel) (t : TxId) : Transaction where
    E       := eventsOf ℓs t
    po      := poOf ℓs t
    status  := statusOf ℓs t
    isOrder := poOf_isOrder ℓs t

def beginPos (ℓs : List TLabel) (t: TxId) (i : Nat) : Prop := ℓs[i]? = some (.ev (.begin t))
def termPos  (ℓs : List TLabel) (t: TxId) (i : Nat) : Prop := ℓs[i]? = some (.ev (.eend t)) ∨ ℓs[i]? = some (.ev (.retry t))

/-- Real-time order: `s` terminates in `ℓs` strictly before `t` begins. -/
def rtOrder  (ℓs : List TLabel) (s t : TxId) : Prop :=
  ∃ i j, termPos ℓs s i ∧ beginPos ℓs t j ∧ i < j

/-- `rtOrder` reflexively closed.  No longer the *definition* of `ar` — see
`HistoryOf.ar_order` / `HistoryOf.ar_realtime` — but still the intended witness
in `exists_historyOf`, where begin-order discharges totality. -/
def arId     (ℓs : List TLabel) (s t : TxId) : Prop := s = t ∨ rtOrder ℓs s t
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

/-- `H` reads `τ` faithfully.

This is the whole faithfulness relation, not a set of fields sized to whichever
theorem is in progress.  `Int` happens to consume only `placed`, `events_tagged`
and `one_per_tag` — it is intra-transactional and never inspects `status` or
`ar`.  `Ext` is not intra-transactional and will need the rest, so the rest stay.

The only things commented out below are the ones `placed` genuinely *subsumes*:
redundant, not deferred.

Note that `Event.id` is opaque (see `Event`).  All knowledge of where an event
sits in `τ` is carried by the placement `pos` inside `placed`, and nowhere else.
`Int` never sees it. -/
structure HistoryOf (τ : List TLabel) (H : History) : Prop where
  -- Every event of H sits somewhere in τ and po is just the order in which they sit in
  -- That calls for four axioms
  -- (a) hat every element of H sits at a position in τ holding its label and it is get or set
  -- (b) hcov no access position of τ is empty
  -- (c) hinj injective property :: no two events sit in the same position
  -- (d) hpo po e f exactly when e sits at or before f

  placed : ∃ pos : Event → Nat, -- TODO the ℍ can be declared as a function
  -- TODO many AR that satisfies a trace so AR can be declarative
  -- TODO keep po as a definition
      (∀ T, H.txs T → ∀ e, T.E e →
          τ[pos e]? = some (.ev e.label) ∧ e.label.isAccess = true)
    ∧ (∀ e f, pos e = pos f → e = f)
    ∧ (∀ i (ℓ : Label), τ[i]? = some (.ev ℓ) → ℓ.isAccess = true →
          ∃ T e, H.txs T ∧ T.E e ∧ pos e = i)
    ∧ (∀ T, H.txs T → ∀ e f : Subtype T.E, T.po e f ↔ pos e.val ≤ pos f.val)

  /-- All of a transaction's events carry one tag. -/
  events_tagged : ∀ T, H.txs T → ∀ e₁ e₂, T.E e₁ → T.E e₂ → e₁.label.tx = e₂.label.tx

  /-- A tag names at most one transaction: `H` may not split `t`'s accesses
  across two transactions.  `no_missing` gave only `∃ T`, never a unique one.

  With `events_tagged` this also yields the old `disjoint` — a shared event
  forces a shared tag, hence a single transaction — and, with `placed` (iii), the
  old `events_complete`: an access of `t` sitting in `τ` is placed in *some*
  transaction, that transaction carries tag `t`, so it is this one. -/
  one_per_tag : ∀ T₁ T₂, H.txs T₁ → H.txs T₂ → ∀ t, HasTx T₁ t → HasTx T₂ t → T₁ = T₂

  -- ── Absorbed into `placed`; do not restore ─────────────────────────────────
  -- These were phrased against `e.id`-as-position, which the opaque-`id`
  -- reading forbids.  `placed` says all three, and says them once.
  --
  -- po_order_agrees  : ∀ T, H.txs T → ∀ e f : Subtype T.E, e.val.id ≤ f.val.id → T.po e f
  -- po_order_agrees₁ : ∀ T, H.txs T → ∀ e f : Subtype T.E, T.po e f → e.val.id < f.val.id
  -- sound            : ∀ T, H.txs T → ∀ e, T.E e → OccursIn τ e
  -- complete         : ∀ i (ℓ : Label), τ[i]? = some (.ev ℓ) → ℓ.isAccess = true →
  --                      ∃ T, H.txs T ∧ T.E ⟨i, ℓ⟩
  -- events_occur     : ∀ T, H.txs T → ∀ e, T.E e → OccursIn τ e ∧ e.label.isAccess = true
  -- events_complete  : ∀ T, H.txs T → ∀ t, HasTx T t → ∀ e, eventsOf τ t e → T.E e

  -- ── Txs is exactly the transactions of τ ───────────────────────────────────
  -- Unused by `Int`: a history that simply omits a transaction still satisfies
  -- `Int` vacuously for it.  `Ext` cannot afford that — an omitted committed
  -- writer changes who the AR-latest writer is.
  no_spurios : ∀ T, H.txs T → ∀ t, HasTx T t → HasBegin τ t
  no_missing : ∀ t, HasBegin τ t → ∃ T, H.txs T ∧ HasTx T t

  -- ── Status is read off the terminator ──────────────────────────────────────
  -- Unused by `Int` — §Internal consistency, first example: a retried and a
  -- pending transaction are both constrained, committedness never enters.
  -- `Ext` reads from *committed* transactions only, so it needs all of these.
  committed : ∀ T, H.txs T → ∀ t, HasTx T t → HasEnd τ t → T.status = .Committed
  retried : ∀ T, H.txs T → ∀ t, HasTx T t → HasRetry τ t → T.status = .Retried
  uncommitted : ∀ T, H.txs T → ∀ t, HasTx T t → ¬ HasEnd τ t → ¬ HasRetry τ t →
    T.status = .Uncommitted
  unquie_terminator : ∀ t i j, termPos τ t i → termPos τ t j → i = j
  unquie_begin : ∀ t i j, beginPos τ t i → beginPos τ t j → i = j

  -- ── Arbitration ────────────────────────────────────────────────────────────
  -- Stated, not defined.  `Ext` needs exactly two things of `ar`, and gets them
  -- here as hypotheses rather than as obligations to re-derive about one chosen
  -- relation.  The old `ar_trace` pinned `ar` to `arId` by `iff`, which is the
  -- shape that let AR and `po` collapse into one relation last time.
  --
  --   ar_trace : ∀ S T, ∀ (hS : H.txs S) (hT : H.txs T), ∀ s t,
  --     HasTx S s → HasTx T t → (H.ar ⟨S, hS⟩ ⟨T, hT⟩ ↔ arId τ s t)

  /-- `ar` is a total order.  Totality is what makes "the `ar`-latest committed
  writer" *exist*, and `antisymm` is what makes it *unique* — neither of which
  the old model had, which is why `Ext`'s statement was not well-defined. -/
  ar_order : IsTotalOrder H.ar

  /-- `ar` extends real time: a transaction that terminates in `τ` before another
  begins is arbitrated before it.

  Keyed on `begin` for the second argument rather than on both terminators: a
  pending transaction has no terminator, and would otherwise be left dangling. -/
  ar_realtime : ∀ S T, ∀ (hS : H.txs S) (hT : H.txs T), ∀ s t, HasTx S s → HasTx T t →
    rtOrder τ s t → H.ar ⟨S, hS⟩ ⟨T, hT⟩
    -- TODO we are extending the partial order to total order we use the realtime


end Reagent
