/-
  The declarative model of a run (Section "Traces, Transactions, and Histories"
  of `docs/reagent-correctness.tex`).

  From a run's trace (a `List TLabel`) we read off, in the order the document
  develops them: transactions `(E, po)`, `min`/`max` under program order,
  committed and uncommitted transactions, the arbitration order `AR`, and the
  history `H = (𝐓, AR)`.

  A trace holds administrative steps as well as transition labels, and the
  Transaction definition excludes the former from `E`: `traceEvents` drops them
  while still counting their positions, so an event's identifier stays its index
  in the full trace and program order remains `<` on identifiers.

  Everything here is computable, so concrete traces can be checked; the
  soundness proofs live in `Consistency.lean` (Int) and `External.lean` (Ext).
-/
import Reagent.Semantics

namespace Reagent

/-- The transaction id a label carries. -/
def Label.tx : Label → TxId
  | .begin t   => t
  | .get _ _ t => t
  | .set _ _ t => t
  | .eend t    => t
  | .retry t   => t

def Label.isBegin : Label → Bool | .begin _ => true | _ => false
def Label.isEnd   : Label → Bool | .eend _  => true | _ => false
def Label.isRetry : Label → Bool | .retry _ => true | _ => false

/-- A transaction's *terminator*: `end@t` if it commits, `retry@t` if it
aborts. `AR` orders a transaction by where its terminator sits. -/
def Label.isTerminator : Label → Bool
  | .eend _  => true
  | .retry _ => true
  | _        => false

/-- An event `(ι, ℓ)`: a *transition* label together with its position `ι` in
the trace, which is what tells two otherwise-identical events apart — two
`get(x,2)@t` reads, say.

`Event.label` is a `Label`, not a `TLabel`, and that is the point: administrative
steps are trace labels but not events, so they never appear here. They still
consume a position, so `ι` remains the label's index in the full trace. -/
structure Event where
  id    : Nat
  label : Label
deriving DecidableEq, Repr

/-- The events of a trace, numbering positions from `s`. Administrative steps
are dropped from `E` but still advance the position counter. -/
def traceEventsFrom : Nat → List TLabel → List Event
  | _, []           => []
  | s, .adm :: ℓs   => traceEventsFrom (s + 1) ℓs
  | s, .ev ℓ :: ℓs  => ⟨s, ℓ⟩ :: traceEventsFrom (s + 1) ℓs

/-- The events of a trace, numbering positions from `0`. -/
def traceEvents (ℓs : List TLabel) : List Event := traceEventsFrom 0 ℓs

/-- Numbering from `s` gives every event an identifier of at least `s`. -/
theorem traceEventsFrom_id_ge (s : Nat) (ℓs : List TLabel) :
    ∀ e ∈ traceEventsFrom s ℓs, s ≤ e.id := by
  induction ℓs generalizing s with
  | nil => intro e he; cases he
  | cons ℓ ℓs ih =>
    cases ℓ with
    | adm =>
      intro e he
      exact Nat.le_of_succ_le (ih (s + 1) e he)
    | ev ℓ' =>
      intro e he
      rcases List.mem_cons.mp he with h | h
      · exact Nat.le_of_eq (congrArg Event.id h.symm)
      · exact Nat.le_of_succ_le (ih (s + 1) e h)

/-- Identifiers increase along a trace, which is what makes `po` a total order
on a transaction's events. Skipping administrative steps preserves this: the
events are a sub-sequence of the positions. -/
theorem traceEventsFrom_sorted (s : Nat) (ℓs : List TLabel) :
    (traceEventsFrom s ℓs).Pairwise (fun a b => a.id < b.id) := by
  induction ℓs generalizing s with
  | nil => exact List.Pairwise.nil
  | cons ℓ ℓs ih =>
    cases ℓ with
    | adm => exact ih (s + 1)
    | ev ℓ' =>
      refine List.Pairwise.cons (fun b hb => ?_) (ih (s + 1))
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self s)
        (traceEventsFrom_id_ge (s + 1) ℓs b hb)

theorem traceEvents_sorted (ℓs : List TLabel) :
    (traceEvents ℓs).Pairwise (fun a b => a.id < b.id) := traceEventsFrom_sorted 0 ℓs

/-- In a sorted list an identifier determines its event. -/
theorem eq_of_id_eq {es : List Event} (hs : es.Pairwise (fun a b => a.id < b.id))
    {a b : Event} (ha : a ∈ es) (hb : b ∈ es) (hid : a.id = b.id) : a = b := by
  induction es with
  | nil => cases ha
  | cons x xs ih =>
    cases hs with
    | cons hx hxs =>
      cases ha with
      | head =>
        cases hb with
        | head => rfl
        | tail _ hb' => exact absurd hid (Nat.ne_of_lt (hx _ hb'))
      | tail _ ha' =>
        cases hb with
        | head => exact absurd hid.symm (Nat.ne_of_lt (hx _ ha'))
        | tail _ hb' => exact ih hxs ha' hb'

/-! ## Transactions `(E, po)` -/

/-- A transaction `T = (E, po)`. Holding `E` as a list sorted by event
identifier *is* the pair, since a list is a finite set together with a total
order on it. `sameTx` is the requirement that every event of `E` carry the
same transaction id `t`. -/
structure Transaction where
  tx     : TxId
  events : List Event
  sameTx : ∀ e ∈ events, e.label.tx = tx
  sorted : events.Pairwise (fun a b => a.id < b.id)

namespace Transaction

/-- Program order `a ≺ b`. An event's identifier is its trace position, so `po`
is `<` on identifiers. -/
def po (_T : Transaction) (a b : Event) : Prop := a.id < b.id

@[simp] theorem po_def {T : Transaction} {a b : Event} :
    T.po a b ↔ a.id < b.id := Iff.rfl

instance (T : Transaction) (a b : Event) : Decidable (T.po a b) :=
  inferInstanceAs (Decidable (a.id < b.id))

theorem po_irrefl (T : Transaction) (a : Event) : ¬ T.po a a := Nat.lt_irrefl _

theorem po_trans (T : Transaction) {a b c : Event} :
    T.po a b → T.po b c → T.po a c := Nat.lt_trans

/-- Antisymmetry, which holds vacuously: `po` is strict, so `a ≺ b` and `b ≺ a`
never both hold. -/
theorem po_antisymm (T : Transaction) {a b : Event} :
    T.po a b → T.po b a → a = b :=
  fun h h' => absurd (Nat.lt_trans h h') (Nat.lt_irrefl a.id)

theorem id_inj (T : Transaction) {a b : Event}
    (ha : a ∈ T.events) (hb : b ∈ T.events) (hid : a.id = b.id) : a = b :=
  eq_of_id_eq T.sorted ha hb hid

/-- Totality: distinct events of `T` are `po`-comparable. -/
theorem po_total (T : Transaction) {a b : Event}
    (ha : a ∈ T.events) (hb : b ∈ T.events) (hne : a ≠ b) :
    T.po a b ∨ T.po b a := by
  rcases Nat.lt_trichotomy a.id b.id with h | h | h
  · exact .inl h
  · exact absurd (T.id_inj ha hb h) hne
  · exact .inr h

end Transaction

/-- The transaction with identifier `t` in the trace `ℓs`: the `t`-tagged events
of `ℓs`, in trace order. -/
def transactionOf (ℓs : List TLabel) (t : TxId) : Transaction where
  tx     := t
  events := (traceEvents ℓs).filter (fun e => e.label.tx == t)
  sameTx := fun _ he => of_decide_eq_true (List.mem_filter.mp he).2
  sorted := List.Pairwise.sublist List.filter_sublist (traceEvents_sorted ℓs)

/-! ## Committed and uncommitted transactions (§Committed transaction) -/

/-- The head of a sorted list is its least element. Used for both extremes:
`max_po` is `min_po` of the reversed list. -/
theorem head?_least {α : Type} {R : α → α → Prop} {es : List α} (hs : es.Pairwise R)
    {e : α} (h : es.head? = some e) : ∀ e' ∈ es, e' = e ∨ R e e' := by
  cases es with
  | nil => simp at h
  | cons x xs =>
    simp at h; subst h
    cases hs with
    | cons hx _ =>
      intro e' he'
      cases he' with
      | head => exact .inl rfl
      | tail _ h' => exact .inr (hx _ h')

theorem head?_mem {α : Type} {es : List α} {e : α} (h : es.head? = some e) : e ∈ es := by
  cases es with
  | nil => simp at h
  | cons x xs => simp at h; subst h; exact .head _

namespace Transaction

/-- `min_po(E)`: the `po`-least event, `none` when `E = ∅`. Since `T.events` is
sorted by identifier, that is its head. -/
def minPo (T : Transaction) : Option Event := T.events.head?

/-- `max_po(E)`: the `po`-greatest event, `none` when `E = ∅`. -/
def maxPo (T : Transaction) : Option Event := T.events.reverse.head?

theorem minPo_mem {T : Transaction} {e : Event} (h : T.minPo = some e) :
    e ∈ T.events := head?_mem h

theorem maxPo_mem {T : Transaction} {e : Event} (h : T.maxPo = some e) :
    e ∈ T.events := List.mem_reverse.mp (head?_mem h)

/-- `minPo` is `po`-least: `∀ e' ∈ E, e = e' ∨ (e,e') ∈ po`. -/
theorem minPo_least {T : Transaction} {e : Event} (h : T.minPo = some e) :
    ∀ e' ∈ T.events, e' = e ∨ T.po e e' :=
  head?_least T.sorted h

/-- `maxPo` is `po`-greatest: `∀ e' ∈ E, e = e' ∨ (e',e) ∈ po`. -/
theorem maxPo_greatest {T : Transaction} {e : Event} (h : T.maxPo = some e) :
    ∀ e' ∈ T.events, e' = e ∨ T.po e' e := by
  intro e' he'
  exact head?_least (List.pairwise_reverse.mpr T.sorted) h e' (List.mem_reverse.mpr he')

/-- `T` is *committed*: `po`-least event a `begin`, `po`-greatest an `end`.
Being the extremes of `po`, this forces every event of `T` to lie between
them. -/
def Committed (T : Transaction) : Prop :=
  (∃ e t, T.minPo = some e ∧ e.label = .begin t) ∧
  (∃ e t, T.maxPo = some e ∧ e.label = .eend t)

/-- `T` is *uncommitted*: its maximal event is not an `end` — typically a
`retry@t`, the aborted case, but also a transaction the run left pending. -/
def Uncommitted (T : Transaction) : Prop :=
  ¬ ∃ e t, T.maxPo = some e ∧ e.label = .eend t

theorem not_committed_of_uncommitted {T : Transaction} (h : T.Uncommitted) :
    ¬ T.Committed := fun hc => h hc.2

/-- The document's alternative `Uncommitted(𝐓) = 𝐓 \ Committed(𝐓)` agrees with
`Uncommitted` only for transactions opening with a `begin`: one failing *that*
conjunct is outside `Committed` yet may still end with an `end`. Every
transaction of a real trace does open with a `begin`, so the two coincide
there — but they are not interchangeable as stated. -/
theorem uncommitted_iff_not_committed {T : Transaction}
    (hmin : ∃ e t, T.minPo = some e ∧ e.label = .begin t) :
    T.Uncommitted ↔ ¬ T.Committed := by
  constructor
  · exact not_committed_of_uncommitted
  · intro h hx
    exact h ⟨hmin, hx⟩

end Transaction

/-! ## Arbitration and histories (§Arbitration, §History) -/

/-- The transaction identifiers of a trace, in order of first occurrence and
without repetition. Administrative steps carry no identifier and are skipped. -/
def txIds : List TLabel → List TxId
  | []            => []
  | .adm :: ℓs    => txIds ℓs
  | .ev ℓ :: ℓs   => ℓ.tx :: (txIds ℓs).filter (fun t => t != ℓ.tx)

/-- `𝐓`: all transactions of a trace, committed and uncommitted alike. -/
def transactions (ℓs : List TLabel) : List Transaction :=
  (txIds ℓs).map (transactionOf ℓs)

/-- `min_po` never sits after `max_po`. -/
theorem Transaction.minPo_id_le_maxPo_id {T : Transaction} {f e : Event}
    (hmin : T.minPo = some f) (hmax : T.maxPo = some e) : f.id ≤ e.id := by
  rcases maxPo_greatest hmax f (minPo_mem hmin) with h | h
  · exact Nat.le_of_eq (congrArg Event.id h)
  · exact Nat.le_of_lt h

/-- Arbitration: `S <_AR T` iff `S`'s terminator `max_po(S)` — an `end@S` *or* a
`retry@S` — precedes `begin@T` in the trace, which, identifiers being trace
positions, is `<` on ids.

An aborted `S` therefore still arbitrates before later transactions; only a
transaction the run left *pending* (no terminator at all) is `AR`-before
nothing. This is exactly why `Ext` must restrict its setters to committed
transactions separately: being `AR`-earlier no longer implies having
committed. -/
def AR (S T : Transaction) : Prop :=
  ∃ e f t, S.maxPo = some e ∧ e.label.isTerminator = true ∧
           T.minPo = some f ∧ f.label = .begin t ∧ e.id < f.id

theorem AR_irrefl (T : Transaction) : ¬ AR T T := by
  rintro ⟨e, f, t, hmax, _, hmin, _, hlt⟩
  exact absurd hlt (Nat.not_lt.mpr (Transaction.minPo_id_le_maxPo_id hmin hmax))

theorem AR_trans {S T U : Transaction} (h₁ : AR S T) (h₂ : AR T U) : AR S U := by
  obtain ⟨e, f, t, hSmax, hSterm, hTmin, hTbegin, h1⟩ := h₁
  obtain ⟨e', f', t', hTmax, hTterm, hUmin, hUbegin, h2⟩ := h₂
  refine ⟨e, f', t', hSmax, hSterm, hUmin, hUbegin, ?_⟩
  have := Transaction.minPo_id_le_maxPo_id hTmin hTmax
  omega

/-- Asymmetry, hence the antisymmetry a total order asks for. -/
theorem AR_asymm {S T : Transaction} (h : AR S T) : ¬ AR T S :=
  fun h' => AR_irrefl S (AR_trans h h')

/-- A history `H = (𝐓, AR)`: all transactions of a trace, committed and
uncommitted, with the arbitration order on them. `txs` and `ar` are the
document's `fst(H)` and `snd(H)`. -/
structure History where
  txs : List Transaction
  ar  : Transaction → Transaction → Prop

/-- The history of a trace. -/
def historyOf (ℓs : List TLabel) : History where
  txs := transactions ℓs
  ar  := AR

end Reagent
