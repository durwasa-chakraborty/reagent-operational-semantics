/-
  Reagent — the history model: trace → events → transactions → `HistoryOf`.
-/
import Reagent.Semantics

namespace Reagent

-- NOTE Just to avoid writing List TLabel again and reminding that a trace has
--      the τ_adm and the label
abbrev Trace : Type := List TLabel


def Label.tx : Label → TxId
  | .begin t   => t
  | .get _ _ t => t
  | .set _ _ t => t
  | .eend t    => t
  | .retry t   => t

-- NOTE Cerone's paper only talks about get and set in a transaction and doesnt care about begin and end and retry
--      So for our INT and EXT to work we would want to have a trace' (prime because trace is defined as abbrev)
def Label.isAccess : Label → Bool
  | .get ..  => true
  | .set ..  => true
  | _        => false

-- NOTE A transaction doesn't have a sequence of Events begin, end, retry at this point so status is the bearer of the
--      information as to what happened with the transaction
inductive Status where
  | Committed
  | Uncommitted
  | Retried
deriving DecidableEq, Repr

-- WARN after much back and forth (as evident from the commit history) I have decided
--      this is the best representation of OccursBefore.
--      OccursBefore cannot be a τ → Event → Event because there is no way to differentiate
--      between two events such as get@1 get@1
--      That information only appears with E = (id, e) where id ≠ ℕ
--      So now the whole flow goes like this ::
--      OccursBefore takes a generic List of Events and Event a and b
--      and inductively defines whether something is Occured Before.
--      We have to construct the List Event which we do in the subsequent section
inductive OccursBefore : List Event → Event → Event → Prop where
  | base {e f : Event} (m : List Event) : OccursBefore ([e] ++ m ++ [f]) e f
  | pre {es e f} (p : List Event) : OccursBefore es e f → OccursBefore (p ++ es) e f
  | post {es e f} (s : List Event) : OccursBefore es e f → OccursBefore (es ++ s) e f

-- NOTE T = (E,po)
--      E is a predicate where Event is an (id,label) pair
structure Transaction where
  E : Event → Prop
  po : Subtype E → Subtype E → Prop
  status : Status
  txid : TxId

structure History where
  txs : Transaction → Prop
  ar : Transaction → Transaction → Prop

-- NOTE From a trace to its transactions.
--      Pairwise is back. 
def UniqueIds (es : List Event) : Prop := es.Pairwise (fun a b => a.id ≠ b.id)


-- NOTE [.ev ⟨⟨"7f"⟩, .begin 0⟩, .ev ⟨⟨"3c"⟩, .get 1 5 0⟩, .adm, .ev ⟨⟨"99"⟩, .get 1 5 0⟩, .ev ⟨⟨"b4"⟩, .eend 0⟩]
--      [⟨⟨"7f"⟩, .begin 0⟩, ⟨⟨"3c"⟩, .get 1 5 0⟩, ⟨⟨"99"⟩, .get 1 5 0⟩, ⟨⟨"b4"⟩, .eend 0⟩]
--      the id is minted by the rule that emits the event, so it is already in the trace
--      deliberately made id non-increasing/decreasing just random UUID
--      `events` drops the adm and unwraps each .ev, keeping the Event (id and all) as emitted.
-- WARN Till this point we haven't constructed the 'es' yet

-- NOTE this will get plugged in the E of Transaction. Given an Event is this part of a predicate.
def events_of_isAccess (es : List Event) (t : TxId) : Event → Prop :=
  fun e => e ∈ es ∧ e.label.tx = t ∧ e.label.isAccess = true

-- NOTE similarly this will get plugged in to the Transaction; given Event a and b are they PO ordered in the Tx
def poOf (es : List Event) (t : TxId) :
    Subtype (events_of_isAccess es t) → Subtype (events_of_isAccess es t) → Prop :=
  fun a b => OccursBefore es a.val b.val

-- COMMITTED | RETRIED | UNCOMMITTED
def statusOf (es : List Event) (t : TxId) : Status :=
  if es.any (fun e => e.label == .eend t) then .Committed
  else if es.any (fun e => e.label == .retry t) then .Retried
  else .Uncommitted

def transactionOf (es : List Event) (t : TxId) : Transaction where
  E := events_of_isAccess es t
  po := poOf es t
  status := statusOf es t
  txid := t

-- NOTE given a list of events and a transaction does the transaction belong to that list
def txsOf (es : List Event) : Transaction → Prop :=
  fun T => ∃ t, (∃ e ∈ es, e.label.tx = t) ∧ T = transactionOf es t


-- WARN so now we have the following changes and that would mean we have a HistoryOf
--      but before that we wanted to fixate the idea that the only thing we want declaratively is the AR
--      so the HistoryOf τ × ℍ should just have AR constraints
--      Before that lets just collect the `es`
/-- The events of a trace, in order: keep the `ev`s, drop the `adm`s. No
counter, no renaming — each event is already the pair the rule emitted. -/
def events : Trace → List Event
  | [] => []
  | .ev e :: τ => e :: events τ
  | .adm :: τ => events τ -- just move ahead if its adm reduction

def txsOfTrace (τ : Trace) : Transaction → Prop := txsOf (events τ)
def Terminates (es : List Event) (t : TxId) (e : Event) : Prop :=
  e ∈ es ∧ (e.label = .eend t ∨ e.label = .retry t)

def Begins (es : List Event) (t : TxId) (e : Event) : Prop :=
  e ∈ es ∧ (e.label = .begin t)

-- NOTE avoiding naming AR or something
def RealTimeBefore (es : List Event) (s t : TxId) : Prop :=
  ∃ a b, Terminates es s a ∧ Begins es t b ∧ OccursBefore es a b

-- NOTE for optimistic locking case we can say say that T and S guard with inflight and say they are not AR ordered
--      or can be extended for an order.
-- TODO
-- ∃ H ⊨ Properties
-- Separately show there is one ℍ which satisfies
-- Given a τ and ∃ ℍ
def HistoryOf (τ : Trace) (H : History) : Prop :=
  (∀ T, H.txs T ↔ txsOfTrace τ T)
  ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → H.ar S T ∨ H.ar T S) -- total
  -- WARN
  -- I believe even when we have optimistic lock the ar will still be total order
  -- Realtime order is currently total and we will lose that with OCC
  ∧ (∀ S T, H.txs S → H.txs T → H.ar S T → ¬ H.ar T S) -- asymmetry
  ∧ (∀ S T U, H.txs S → H.txs T → H.txs U → H.ar S T → H.ar T U → H.ar S U) -- transitive
  ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → RealTimeBefore (events τ) S.txid T.txid → H.ar S T)


-- NOTE after the definition we just have a sequence of proofs to establish
--      properties about PO

theorem OccursBefore.split {es : List Event} {e f : Event} (h : OccursBefore es e f) :
    ∃ p m s, es = p ++ [e] ++ m ++ [f] ++ s := by
  induction h with
  | base m => exact ⟨[], m, [], by simp⟩
  | pre p _ ih => obtain ⟨q, m, s, rfl⟩ := ih; exact ⟨p ++ q, m, s, by simp⟩
  | post s _ ih => obtain ⟨q, m, r, rfl⟩ := ih; exact ⟨q, m, r ++ s, by simp⟩

theorem OccursBefore.of_split (p m s : List Event) (e f : Event) :
    OccursBefore (p ++ [e] ++ m ++ [f] ++ s) e f := by
  have h := OccursBefore.pre (e := e) (f := f) p (OccursBefore.post s (OccursBefore.base m))
  simpa using h

-- NOTE not two IDs of an event are equal
theorem OccursBefore.id_ne {es : List Event} {e f : Event}
    (hu : UniqueIds es) (h : OccursBefore es e f) : e.id ≠ f.id := by
  obtain ⟨p, m, s, rfl⟩ := h.split
  have hu' : List.Pairwise (fun a b : Event => a.id ≠ b.id) (p ++ (e :: (m ++ (f :: s)))) := by
    simpa [UniqueIds] using hu
  have h2 := (List.pairwise_append.mp hu').2.1
  exact (List.pairwise_cons.mp h2).1 f (by simp)

-- NOTE not two Events can be OB-ed
theorem OccursBefore.irrefl {es : List Event} {e : Event} (hu : UniqueIds es) :
    ¬ OccursBefore es e e :=
  fun h => h.id_ne hu rfl

theorem UniqueIds.split_unique {A B C D : List Event} {x : Event}
    (hu : UniqueIds (A ++ x :: B)) (h : A ++ x :: B = C ++ x :: D) : A = C ∧ B = D := by
  induction A generalizing C with
  | nil =>
    cases C with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons c C' =>
      exfalso
      have hB : B = C' ++ x :: D := by injection h
      have hne := (List.pairwise_cons.mp hu).1
      exact hne x (by rw [hB]; simp) rfl
  | cons a A' ih =>
    cases C with
    | nil =>
      exfalso
      have ha : a = x := by injection h
      have hne := (List.pairwise_cons.mp hu).1
      exact hne x (by simp) (by rw [ha])
    | cons c C' =>
      have hac : a = c := by injection h
      have h' : A' ++ x :: B = C' ++ x :: D := by injection h
      obtain ⟨h1, h2⟩ := ih (List.pairwise_cons.mp hu).2 h'
      exact ⟨by rw [hac, h1], h2⟩

-- NOTE total order :: trans
theorem OccursBefore.trans {es : List Event} {e f g : Event} (hu : UniqueIds es)
    (h1 : OccursBefore es e f) (h2 : OccursBefore es f g) : OccursBefore es e g := by
  obtain ⟨p, m, s, hes⟩ := h1.split
  obtain ⟨p', m', s', hes'⟩ := h2.split
  have hA : (p ++ [e] ++ m) ++ f :: s = p' ++ f :: (m' ++ [g] ++ s') := by
    have := hes.symm.trans hes'; simpa using this
  have huA : UniqueIds ((p ++ [e] ++ m) ++ f :: s) := by
    rw [hes] at hu; simpa [UniqueIds] using hu
  obtain ⟨-, hs⟩ := UniqueIds.split_unique huA hA
  have hcut : es = p ++ [e] ++ (m ++ [f] ++ m') ++ [g] ++ s' := by
    rw [hes, hs]; simp
  rw [hcut]; exact OccursBefore.of_split _ _ _ _ _

theorem mem_split {α : Type} {a : α} {l : List α} (h : a ∈ l) : ∃ p s, l = p ++ a :: s := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨[], l, rfl⟩
    · obtain ⟨p, s, rfl⟩ := ih h'; exact ⟨b :: p, s, rfl⟩

-- NOTE proof of OB being total
theorem OccursBefore.total {es : List Event} {e f : Event} (he : e ∈ es) (hf : f ∈ es) :
    OccursBefore es e f ∨ e = f ∨ OccursBefore es f e := by
  obtain ⟨A, B, rfl⟩ := mem_split he
  rcases List.mem_append.mp hf with hfA | hfB
  · obtain ⟨A₁, A₂, rfl⟩ := mem_split hfA
    exact Or.inr (Or.inr (by
      have := OccursBefore.of_split A₁ A₂ B f e
      simpa using this))
  · rcases List.mem_cons.mp hfB with rfl | hfB'
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨B₁, B₂, rfl⟩ := mem_split hfB'
      exact Or.inl (by
        have := OccursBefore.of_split A B₁ B₂ e f
        simpa using this)

theorem poOf_irrefl {es t} (hu : UniqueIds es) (a : Subtype (events_of_isAccess es t)) :
    ¬ poOf es t a a :=
  OccursBefore.irrefl hu

theorem poOf_trans {es t} (hu : UniqueIds es) {a b c : Subtype (events_of_isAccess es t)}
    (h1 : poOf es t a b) (h2 : poOf es t b c) : poOf es t a c :=
  OccursBefore.trans hu h1 h2

theorem poOf_antisymm {es t} (hu : UniqueIds es) {a b : Subtype (events_of_isAccess es t)}
    (h1 : poOf es t a b) (h2 : poOf es t b a) : a = b :=
  absurd (OccursBefore.trans hu h1 h2) (OccursBefore.irrefl hu)

theorem poOf_total {es t} (a b : Subtype (events_of_isAccess es t)) :
    poOf es t a b ∨ a = b ∨ poOf es t b a := by
  rcases OccursBefore.total a.property.1 b.property.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr h)

/-! ## One step at a time

A run grows by one label, so `events` grows by one event or by none.  These are
what an induction over a run needs. -/

theorem events_append : ∀ (τ σ : Trace),
    events (τ ++ σ) = events τ ++ events σ := by
  intro τ
  induction τ with
  | nil => intro σ; rfl
  | cons l τ ih => cases l <;> intro σ <;> simp [events, ih σ]

@[simp] theorem events_snoc_ev (τ : Trace) (e : Event) :
    events (τ ++ [.ev e]) = events τ ++ [e] := by
  simp [events_append, events]

@[simp] theorem events_snoc_adm (τ : Trace) : events (τ ++ [.adm]) = events τ := by
  simp [events_append, events]

-- NOTE
-- The uniqueness of the events made by UniqueIds. Ids are UUIDs now, so there is
-- no order on them to piggyback on: the po_* order proofs take the order from the
-- position in `es` (OccursBefore) and use UniqueIds only to tell events apart.
--
-- WARN
-- UniqueIds es is 'the names are distinct', and the po_* order proofs are discharged
-- from that; so an appended event must not reuse an id that already exists. Nothing
-- arithmetic gives us that.
/-- Appending an event whose id is new to `es` keeps the ids distinct. This is
the only way `UniqueIds` is ever established now: there is no arithmetic to
appeal to, only the freshness premise the emitting rule carried. -/
theorem UniqueIds.snoc {es : List Event} {n : Event}
    (hu : UniqueIds es) (hfresh : ∀ e ∈ es, e.id ≠ n.id) : UniqueIds (es ++ [n]) := by
  refine List.pairwise_append.mpr ⟨hu, by simp, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton.mp hb]
  exact hfresh a ha

end Reagent
