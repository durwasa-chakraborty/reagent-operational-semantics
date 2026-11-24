/-
  Reagent — runs.

  `Trace` is the list of labels, so the relation "this chain of steps emits that
  trace" needs its own name.  Both consistency axioms are stated about runs, so
  this sits below them.  It belongs in `Trace.lean` if you'd rather have it there.
-/
import Reagent.Trace

namespace Reagent

/-- The initial configuration `⟨σ₀, ⊥, ⊥, E₀, σ₀, ()⟩`, minting transaction ids
from `0` and with no event id used yet. -/
def initConfig (E₀ : ThreadMap) : Config :=
  { store := Store.init_store, activeThread := none, activeTx := none,
    threadMap := E₀, snapshot := Store.init_store, savedBody := .val .unit,
    nextTx := 0, usedIds := [] }

/-- A run: a chain of `Trans` steps emitting `τ`. -/
inductive Run : Config → Trace → Config → Prop where
  | nil  {C} : Run C [] C
  | cons {C ℓ C' w C''} : Trans C ℓ C' → Run C' w C'' → Run C (ℓ :: w) C''

-- NOTE If a run emits pre ++ post then there ∃ a config C' st. pre part ends and the post begins.
--      We need a cut point
theorem Run.split {C₀ C'' : Config} {pre post : Trace}
    (h : Run C₀ (pre ++ post) C'') : ∃ C', Run C₀ pre C' ∧ Run C' post C'' := by
  induction pre generalizing C₀ with
  | nil => exact ⟨C₀, .nil, h⟩
  | cons ℓ ls ih =>
    cases h with
    | cons hstep hrest =>
      obtain ⟨C', h1, h2⟩ := ih hrest
      exact ⟨C', .cons hstep h1, h2⟩

-- NOTE run extended by one step at the end
theorem Run.snoc {C₀ C C' : Config} {τ : Trace} {ℓ : TLabel}
    (h : Run C₀ τ C) (hstep : Trans C ℓ C') : Run C₀ (τ ++ [ℓ]) C' := by
  induction h with
  | nil => exact .cons hstep .nil
  | cons hs _ ih => exact .cons hs (ih hstep)

-- NOTE reverse because we are doing [a,b] and an event c comes makes the list [a,b,c] which looks like [a,b] :: [c]
--      while most of the Lean4 induction works like [a,b,c] [a]::[b,c]
--
--      So the idea is adding a to the front of r ≃ adding a to the reverse of r
--      a :: [b,c,d] ≃ [d,c,b] :: a
--      so (a::r).reverse = [d,c,b] :: a
--      ⇒  (a::r).reverse = r.reverse :: a
--
theorem listReverseInduction {α : Type} {motive : List α → Prop}
    (nil : motive []) (snoc : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) :
    ∀ l, motive l := fun l => by
  have h : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a as ih => simpa using snoc as.reverse a ih
  simpa using h l.reverse

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


-- NOTE maybe shorter ways of proving it that ID is unique but okay, can live with it
--      or probably if there are some ways to prove it or the library comes with it.

-- NOTE Simple induction ; goes something like if all the events emitted so far has its id
--      in `u` and say we have new event `n` whose id ∉ u then every event will be in n.id :: u
--      additionally prove that ids are still distinct
--
--      first is events ls ++ n
--      Distinctness
--      e is inductive
--        can either be in ls (member cons of member)
--        or can be in the n  (member cons of itself)
theorem ids_snoc {ls : Trace} {u : List EvId} (n : Event)
    (ih1 : ∀ e ∈ events ls, e.id ∈ u) (ih2 : UniqueIds (events ls)) (hfresh : n.id ∉ u) :
    (∀ e ∈ events (ls ++ [.ev n]), e.id ∈ n.id :: u)
      ∧ UniqueIds (events (ls ++ [.ev n])) := by
  rw [events_snoc_ev]
  refine ⟨fun e he => ?_, ih2.snoc (fun e he heq => hfresh (heq ▸ ih1 e he))⟩
  rcases List.mem_append.mp he with h' | h'
  · exact List.mem_cons_of_mem _ (ih1 e h')
  · rw [List.mem_singleton.mp h']; exact List.mem_cons_self ..


-- NOTE ∀ e ∈ Events, e.id ∈ C.userIds ∧ all the Ids are Unique
--      all the ids are recorded in that List of EventIds
theorem inv_ids {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    (∀ e ∈ events τ, e.id ∈ C.usedIds) ∧ UniqueIds (events τ) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      (∀ e ∈ events τ, e.id ∈ C.usedIds) ∧ UniqueIds (events τ))
    ⟨by simp [events], by simp [events, UniqueIds]⟩ ?_ h
  rintro ls C m C' _ ⟨ih1, ih2⟩ hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => simpa using ⟨ih1, ih2⟩
  | @begin σ θ E snap body n u i eb α hfresh =>
    exact ids_snoc ⟨α, .begin n⟩ ih1 ih2 hfresh
  | @get σ i t E snap body n u l v α hfresh hv =>
    exact ids_snoc ⟨α, .get l v t⟩ ih1 ih2 hfresh
  | @set σ i t E snap body n u l v α hfresh =>
    exact ids_snoc ⟨α, .set l v t⟩ ih1 ih2 hfresh
  | @eend σ i t E snap body n u α hfresh =>
    exact ids_snoc ⟨α, .eend t⟩ ih1 ih2 hfresh
  | @retry σ i t E snap body n u α hfresh =>
    exact ids_snoc ⟨α, .retry t⟩ ih1 ih2 hfresh

end Reagent
