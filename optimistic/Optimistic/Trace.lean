-- NOTE most of the definitions are just copied from the pessimistic one
import Optimistic.Semantics

namespace Optimistic

open Reagent (TxId EvId)

def Label.tx : Label → TxId
  | .begin t   => t
  | .get _ _ t => t
  | .set _ _ t => t
  | .eend t    => t
  | .retry t   => t

def Label.isAccess : Label → Bool
  | .get .. => true
  | .set .. => true
  | _       => false

inductive Status where
  | Committed
  | Retried
  | Pending
deriving DecidableEq, Repr

inductive OccursBefore : List Event → Event → Event → Prop where
  | base {e f : Event} (m : List Event) : OccursBefore ([e] ++ m ++ [f]) e f
  | pre {es e f} (p : List Event) : OccursBefore es e f → OccursBefore (p ++ es) e f
  | post {es e f} (s : List Event) : OccursBefore es e f → OccursBefore (es ++ s) e f

structure Transaction where
  E : Event → Prop
  po : Subtype E → Subtype E → Prop
  status : Status
  txid : TxId

structure History where
  txs : Transaction → Prop
  ar : Transaction → Transaction → Prop

def UniqueIds (es : List Event) : Prop := es.Pairwise (fun a b => a.id ≠ b.id)

def events_of_isAccess (es : List Event) (t : TxId) : Event → Prop :=
  fun e => e ∈ es ∧ e.label.tx = t ∧ e.label.isAccess = true

def poOf (es : List Event) (t : TxId) :
    Subtype (events_of_isAccess es t) → Subtype (events_of_isAccess es t) → Prop :=
  fun a b => OccursBefore es a.val b.val

def statusOf (es : List Event) (t : TxId) : Status :=
  if es.any (fun e => e.label == .eend t) then .Committed
  else if es.any (fun e => e.label == .retry t) then .Retried
  else .Pending

def transactionOf (es : List Event) (t : TxId) : Transaction where
  E := events_of_isAccess es t
  po := poOf es t
  status := statusOf es t
  txid := t

def txsOf (es : List Event) : Transaction → Prop :=
  fun T => ∃ t, (∃ e ∈ es, e.label.tx = t) ∧ T = transactionOf es t

/-- The events of a trace, in order: keep the `ev`s, drop the `adm`s. -/
def events : Trace → List Event
  | [] => []
  | .ev e :: τ => e :: events τ
  | .adm :: τ => events τ

def txsOfTrace (τ : Trace) : Transaction → Prop := txsOf (events τ)

/-- `e` closes transaction `t`: an `end` or a `retry`. -/
def Terminates (es : List Event) (t : TxId) (e : Event) : Prop :=
  e ∈ es ∧ (e.label = .eend t ∨ e.label = .retry t)

def Begins (es : List Event) (t : TxId) (e : Event) : Prop :=
  e ∈ es ∧ e.label = .begin t

def RealTimeBefore (es : List Event) (s t : TxId) : Prop :=
  ∃ a b, Terminates es s a ∧ Begins es t b ∧ OccursBefore es a b

-- WARN Check this with Prof. KN|KC
def HistoryOf (τ : Trace) (H : History) : Prop :=
  (∀ T, H.txs T ↔ txsOfTrace τ T)
  ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → H.ar S T ∨ H.ar T S)
  ∧ (∀ S T, H.txs S → H.txs T → H.ar S T → ¬ H.ar T S)
  ∧ (∀ S T U, H.txs S → H.txs T → H.txs U → H.ar S T → H.ar T U → H.ar S U)
  ∧ (∀ S T, H.txs S → H.txs T → S ≠ T → RealTimeBefore (events τ) S.txid T.txid → H.ar S T)


-- NOTE these are still from lockbased but lets just keep it around for now
theorem mem_split {α : Type} {a : α} {l : List α} (h : a ∈ l) : ∃ p s, l = p ++ a :: s := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨[], l, rfl⟩
    · obtain ⟨p, s, rfl⟩ := ih h'; exact ⟨b :: p, s, rfl⟩

theorem OccursBefore.split {es : List Event} {e f : Event} (h : OccursBefore es e f) :
    ∃ p m s, es = p ++ [e] ++ m ++ [f] ++ s := by
  induction h with
  | base m => exact ⟨[], m, [], by simp⟩
  | pre p _ ih => obtain ⟨q, m, s, rfl⟩ := ih; exact ⟨p ++ q, m, s, by simp⟩
  | post s _ ih => obtain ⟨q, m, r, rfl⟩ := ih; exact ⟨q, m, r ++ s, by simp⟩

theorem OccursBefore.of_split (p m s : List Event) (e f : Event) :
    OccursBefore (p ++ [e] ++ m ++ [f] ++ s) e f := by
  sorry

theorem OccursBefore.id_ne {es : List Event} {e f : Event}
    (hu : UniqueIds es) (h : OccursBefore es e f) : e.id ≠ f.id := by
  obtain ⟨p, m, s, rfl⟩ := h.split
  have hu' : List.Pairwise (fun a b : Event => a.id ≠ b.id) (p ++ (e :: (m ++ (f :: s)))) := by
    simpa [UniqueIds] using hu
  have h2 := (List.pairwise_append.mp hu').2.1
  exact (List.pairwise_cons.mp h2).1 f (by simp)

theorem OccursBefore.irrefl {es : List Event} {e : Event} (hu : UniqueIds es) :
    ¬ OccursBefore es e e := by
  sorry

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

theorem OccursBefore.snoc_last {es : List Event} {a n : Event} (ha : a ∈ es) :
    OccursBefore (es ++ [n]) a n := by
  sorry

theorem OccursBefore.snoc_mono {es : List Event} {a b n : Event}
    (h : OccursBefore es a b) : OccursBefore (es ++ [n]) a b := by
  sorry

theorem UniqueIds.snoc {es : List Event} {n : Event}
    (hu : UniqueIds es) (hfresh : ∀ e ∈ es, e.id ≠ n.id) : UniqueIds (es ++ [n]) := by
  refine List.pairwise_append.mpr ⟨hu, by simp, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton.mp hb]
  exact hfresh a ha

/-! ## Runs, one step at a time -/

theorem events_append : ∀ (τ σ : Trace), events (τ ++ σ) = events τ ++ events σ := by
  sorry

@[simp] theorem events_snoc_ev (τ : Trace) (e : Event) :
    events (τ ++ [.ev e]) = events τ ++ [e] := by
  sorry

@[simp] theorem events_snoc_adm (τ : Trace) : events (τ ++ [.adm]) = events τ := by
  sorry

theorem Run.split {C₀ C'' : Config} {pre post : Trace}
    (h : Run C₀ (pre ++ post) C'') : ∃ C', Run C₀ pre C' ∧ Run C' post C'' := by
  induction pre generalizing C₀ with
  | nil => exact ⟨C₀, .nil, h⟩
  | cons ℓ ls ih =>
    cases h with
    | cons hstep hrest =>
      obtain ⟨C', h1, h2⟩ := ih hrest
      exact ⟨C', .cons hstep h1, h2⟩

theorem listReverseInduction {α : Type} {motive : List α → Prop}
    (nil : motive []) (snoc : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) :
    ∀ l, motive l := fun l => by
  have h : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a as ih => simpa using snoc as.reverse a ih
  simpa using h l.reverse

-- NOTE we are still employing the same es :: a strategy
theorem Run.reverseRecOn {C₀ : Config} {motive : Trace → Config → Prop}
    (base : motive [] C₀)
    (ind : ∀ (ℓs : Trace) (C : Config) (ℓ : TLabel) (C' : Config),
      Run C₀ ℓs C → motive ℓs C → Trans C ℓ C' → motive (ℓs ++ [ℓ]) C')
    {ℓs : Trace} {C : Config} (h : Run C₀ ℓs C) : motive ℓs C := by
  induction ℓs using listReverseInduction generalizing C with
  | nil => cases h; exact base
  | snoc ls ℓ ih =>
    obtain ⟨C', h1, h2⟩ := Run.split h
    cases h2 with
    | cons hstep hrest =>
      cases hrest
      exact ind ls C' ℓ C h1 (ih h1) hstep

end Optimistic
