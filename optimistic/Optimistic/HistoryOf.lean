/-
  prompt.org, entry "Proving HistoryOf":

    ∀ C' τ. Run C₀ τ C' → ∃ H. HistoryOf τ H

  Witness H := (txs(τ), AR) with AR the finish order; then H1–H5 one by one.
-/
import Optimistic.Trace

namespace Optimistic

open Reagent (TxId ThId ThreadMap Expr update)

/-! ## Witness -/

/-- `fin S`: the trace contains a terminator of `S`. -/
def Finished (es : List Event) (t : TxId) : Prop := ∃ a, Terminates es t a

/-- The three clauses of the witness `AR`: finished transactions by their
terminators, finished before pending, pending by their `begin`. -/
def finishOrder (es : List Event) (S T : Transaction) : Prop :=
  (∃ a b, Terminates es S.txid a ∧ Terminates es T.txid b ∧ OccursBefore es a b)
  ∨ (Finished es S.txid ∧ ¬ Finished es T.txid)
  ∨ (¬ Finished es S.txid ∧ ¬ Finished es T.txid ∧
      ∃ a b, Begins es S.txid a ∧ Begins es T.txid b ∧ OccursBefore es a b)

/-- `H := (txs(τ), AR)`, built from the given `τ` and nothing else. -/
def witness (τ : Trace) : History := ⟨txsOfTrace τ, finishOrder (events τ)⟩

theorem Terminates.tx {es : List Event} {t : TxId} {a : Event}
    (h : Terminates es t a) : a.label.tx = t := by
  sorry

theorem Begins.tx {es : List Event} {t : TxId} {a : Event}
    (h : Begins es t a) : a.label.tx = t := by
  sorry

/-- Two transactions of a trace with the same tag are the same transaction:
each is `transactionOf es t` for its tag. -/
theorem txsOf_txid_inj {es : List Event} {S T : Transaction}
    (hS : txsOf es S) (hT : txsOf es T) (h : S.txid = T.txid) : S = T := by
  obtain ⟨s, -, rfl⟩ := hS
  obtain ⟨t, -, rfl⟩ := hT
  simp only [transactionOf] at h
  subst h; rfl

/-! ## Run facts -/

theorem Trans.usedIds_ev {C C' : Config} {n : Event} (h : Trans C (.ev n) C') :
    n.id ∉ C.usedIds ∧ C'.usedIds = n.id :: C.usedIds := by
  cases h with
  | ctx _ hh => cases hh <;> simp_all
  | kcasRetry _ _ _ hα => exact ⟨hα, rfl⟩
  | retry _ _ hα => exact ⟨hα, rfl⟩

theorem Trans.usedIds_adm {C C' : Config} (h : Trans C .adm C') :
    C'.usedIds = C.usedIds := by
  sorry

/-- Event ids are distinct, so `≺` is a strict order. The paper uses
transitivity and irreflexivity of `≺` without comment; in Lean `≺` is
`OccursBefore` on events, and both need this. -/
theorem inv_ids {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    (∀ e ∈ events τ, e.id ∈ C.usedIds) ∧ UniqueIds (events τ) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      (∀ e ∈ events τ, e.id ∈ C.usedIds) ∧ UniqueIds (events τ))
    ⟨by simp [events], by simp [events, UniqueIds]⟩ ?_ h
  rintro ls C ℓ C' _ ⟨ih1, ih2⟩ hstep
  cases ℓ with
  | adm => rw [events_snoc_adm, hstep.usedIds_adm]; exact ⟨ih1, ih2⟩
  | ev n =>
    obtain ⟨hfresh, hids⟩ := hstep.usedIds_ev
    rw [events_snoc_ev, hids]
    refine ⟨fun e he => ?_, ih2.snoc (fun e he heq => hfresh (heq ▸ ih1 e he))⟩
    rcases List.mem_append.mp he with h' | h'
    · exact List.mem_cons_of_mem _ (ih1 e h')
    · rw [List.mem_singleton.mp h']; exact List.mem_cons_self ..

/-- "A transaction has to begin before it can end": every `begin` of `t`
occurs before every terminator of `t`. -/
def BeginsBeforeTerm (es : List Event) : Prop :=
  ∀ t b a, Begins es t b → Terminates es t a → OccursBefore es b a

theorem bbt_snoc_nonbegin {es : List Event} {n : Event} (hC : BeginsBeforeTerm es)
    (hn : ∀ t, n.label ≠ .begin t) : BeginsBeforeTerm (es ++ [n]) := by
  intro t b a hb ha
  have hb' : b ∈ es := by
    rcases List.mem_append.mp hb.1 with h | h
    · exact h
    · rw [List.mem_singleton.mp h] at hb; exact absurd hb.2 (hn t)
  rcases List.mem_append.mp ha.1 with h | h
  · exact (hC t b a ⟨hb', hb.2⟩ ⟨h, ha.2⟩).snoc_mono
  · rw [List.mem_singleton.mp h]; exact OccursBefore.snoc_last hb'

theorem bbt_snoc_begin {es : List Event} {n : Event} {t₀ : TxId} (hC : BeginsBeforeTerm es)
    (hA : ∀ e ∈ es, e.label.tx < t₀) (hn : n.label = .begin t₀) :
    BeginsBeforeTerm (es ++ [n]) := by
  intro t b a hb ha
  rcases List.mem_append.mp ha.1 with haes | han
  · rcases List.mem_append.mp hb.1 with hbes | hbn
    · exact (hC t b a ⟨hbes, hb.2⟩ ⟨haes, ha.2⟩).snoc_mono
    · -- the new `begin` mints `t₀`, but `a` is an older event tagged `t₀`
      have hl := hb.2
      rw [List.mem_singleton.mp hbn, hn] at hl
      have ht : t₀ = t := by simpa using hl
      have := hA a haes
      rw [ha.tx, ← ht] at this
      exact absurd this (Nat.lt_irrefl _)
  · have hl := ha.2
    rw [List.mem_singleton.mp han, hn] at hl
    rcases hl with h | h | h <;> cases h

theorem lt_snoc {es : List Event} {n : Event} {N N' : TxId}
    (hA : ∀ e ∈ es, e.label.tx < N) (hN : N ≤ N') (hn : n.label.tx < N') :
    ∀ e ∈ es ++ [n], e.label.tx < N' := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact Nat.lt_of_lt_of_le (hA e h) hN
  · rw [List.mem_singleton.mp h]; exact hn

theorem txs_update_some {f : ThId → Option (TxId × Log × Expr)} {N : TxId} {i : ThId}
    {t₀ : TxId} {Λ₀ : Log} {Ê₀ : Expr}
    (hB : ∀ j t Λ Ê, f j = some (t, Λ, Ê) → t < N) (ht : t₀ < N) :
    ∀ j t Λ Ê, update f i (some (t₀, Λ₀, Ê₀)) j = some (t, Λ, Ê) → t < N := by
  intro j t Λ Ê h
  simp only [update] at h
  split at h
  · cases h; exact ht
  · exact hB j t Λ Ê h

theorem txs_update_none {f : ThId → Option (TxId × Log × Expr)} {N : TxId} {i : ThId}
    (hB : ∀ j t Λ Ê, f j = some (t, Λ, Ê) → t < N) :
    ∀ j t Λ Ê, update f i none j = some (t, Λ, Ê) → t < N := by
  intro j t Λ Ê h
  simp only [update] at h
  split at h
  · cases h
  · exact hB j t Λ Ê h

/-- The induction H5 asks for, on `C₀ ─τ→ C ─ℓ→ C'`. To go through it carries
two more facts: every tag used so far is below `nextTx`, so a new `begin`
has no older terminator; and so is every live tag in `Θ`. -/
theorem inv_bbt {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    (∀ e ∈ events τ, e.label.tx < C.nextTx)
    ∧ (∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → t < C.nextTx)
    ∧ BeginsBeforeTerm (events τ) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      (∀ e ∈ events τ, e.label.tx < C.nextTx)
      ∧ (∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → t < C.nextTx)
      ∧ BeginsBeforeTerm (events τ))
    ⟨by simp [events], by simp [initConfig],
     fun t b a hb _ => by simp [events, Begins] at hb⟩ ?_ h
  rintro ls C ℓ C' _ ⟨hA, hB, hC⟩ hstep
  cases hstep with
  | ctx _ hh =>
    cases hh with
    | begin hi hα =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_succ _) (by simp [Label.tx]),
        txs_update_some (fun j t Λ Ê h => Nat.lt_succ_of_lt (hB j t Λ Ê h)) (Nat.lt_succ_self _),
        bbt_snoc_begin hC hA rfl⟩
    | getLog hi _ _ =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), hB,
        bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
    | getMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_some hB (hB _ _ _ _ hi),
        bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
    | setLog hi _ _ =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_some hB (hB _ _ _ _ hi),
        bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
    | setMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_some hB (hB _ _ _ _ hi),
        bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
    | commit hi _ _ =>
      simp only [events_snoc_ev]
      exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_none hB,
        bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
    | adm _ =>
      simp only [events_snoc_adm]
      exact ⟨hA, hB, hC⟩
  | kcasRetry _ hi _ _ =>
    simp only [events_snoc_ev]
    exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_none hB,
      bbt_snoc_nonbegin hC (by intro t h; cases h)⟩
  | retry _ hi _ =>
    simp only [events_snoc_ev]
    exact ⟨lt_snoc hA (Nat.le_refl _) (hB _ _ _ _ hi), txs_update_none hB,
      bbt_snoc_nonbegin hC (by intro t h; cases h)⟩

/-! ## (D) two live threads never run the same `t` -/

def LiveDistinct (θ : ThId → Option (TxId × Log × Expr)) : Prop :=
  ∀ i j t Λ Λ' Ê Ê', θ i = some (t, Λ, Ê) → θ j = some (t, Λ', Ê') → i = j

theorem LiveDistinct.update_none {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    (hD : LiveDistinct θ) : LiveDistinct (update θ i none) := by
  intro a b t Λ Λ' Ê Ê' ha hb
  by_cases hai : a = i
  · simp [update, hai] at ha
  by_cases hbi : b = i
  · simp [update, hbi] at hb
  simp only [update, hai, hbi, if_false] at ha hb
  exact hD a b t Λ Λ' Ê Ê' ha hb

/-- The thread keeps its tag and only changes its log. -/
theorem LiveDistinct.update_same {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t₀ : TxId} {Λ₀ Λ₁ : Log} {Ê₀ : Expr}
    (hD : LiveDistinct θ) (hi : θ i = some (t₀, Λ₀, Ê₀)) :
    LiveDistinct (update θ i (some (t₀, Λ₁, Ê₀))) := by
  intro a b t Λ Λ' Ê Ê' ha hb
  by_cases hai : a = i <;> by_cases hbi : b = i
  · rw [hai, hbi]
  · simp only [update, hai, hbi, if_true, if_false] at ha hb
    obtain ⟨rfl, -, -⟩ := ha
    rw [hai]; exact hD i b t₀ Λ₀ Λ' Ê₀ Ê' hi hb
  · simp only [update, hai, hbi, if_true, if_false] at ha hb
    obtain ⟨rfl, -, -⟩ := hb
    rw [hbi]; exact hD a i t₀ Λ Λ₀ Ê Ê₀ ha hi
  · simp only [update, hai, hbi, if_false] at ha hb
    exact hD a b t Λ Λ' Ê Ê' ha hb

/-- Begin: the new tag is above every live tag, so it clashes with none. -/
theorem LiveDistinct.update_fresh {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {N : TxId} {Λ₁ : Log} {Ê₁ : Expr}
    (hD : LiveDistinct θ) (hB : ∀ j t Λ Ê, θ j = some (t, Λ, Ê) → t < N) :
    LiveDistinct (update θ i (some (N, Λ₁, Ê₁))) := by
  intro a b t Λ Λ' Ê Ê' ha hb
  by_cases hai : a = i <;> by_cases hbi : b = i
  · rw [hai, hbi]
  · simp only [update, hai, hbi, if_true, if_false] at ha hb
    obtain ⟨rfl, -, -⟩ := ha
    exact absurd (hB b N Λ' Ê' hb) (Nat.lt_irrefl _)
  · simp only [update, hai, hbi, if_true, if_false] at ha hb
    obtain ⟨rfl, -, -⟩ := hb
    exact absurd (hB a N Λ Ê ha) (Nat.lt_irrefl _)
  · simp only [update, hai, hbi, if_false] at ha hb
    exact hD a b t Λ Λ' Ê Ê' ha hb

/-- (D), "follows from `t` fresh". -/
theorem inv_distinct {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : LiveDistinct C.txs := by
  refine Run.reverseRecOn (motive := fun _ C => LiveDistinct C.txs)
    (by intro i j t Λ Λ' Ê Ê' hi; simp [initConfig] at hi) ?_ h
  intro ls C ℓ C' hrun hD hstep
  have hB := (inv_bbt hrun).2.1
  cases hstep with
  | ctx _ hh =>
    cases hh with
    | begin _ _ => exact hD.update_fresh hB
    | getLog _ _ _ => exact hD
    | getMem hi _ _ _ => exact hD.update_same hi
    | setLog hi _ _ => exact hD.update_same hi
    | setMem hi _ _ _ => exact hD.update_same hi
    | commit _ _ _ => exact hD.update_none
    | adm _ => exact hD
  | kcasRetry _ _ _ _ => exact hD.update_none
  | retry _ _ _ => exact hD.update_none

theorem update_eq_some {θ : ThId → Option (TxId × Log × Expr)} {i k : ThId}
    {v : Option (TxId × Log × Expr)} {t : TxId} {Λ : Log} {Ê : Expr}
    (hk : update θ i v k = some (t, Λ, Ê)) :
    (k = i ∧ v = some (t, Λ, Ê)) ∨ (k ≠ i ∧ θ k = some (t, Λ, Ê)) := by
  by_cases hki : k = i
  · left; simp only [update, hki, if_true] at hk; exact ⟨hki, hk⟩
  · right; simp only [update, hki, if_false] at hk; exact ⟨hki, hk⟩


/-! ## (T) and Lemma N -/

/-- `Term(τ·n) = Term(τ) ∪ T(n)`: a terminator of the snoc is an old one, or `n`. -/
theorem terminates_snoc {es : List Event} {n : Event} {t : TxId} {a : Event}
    (h : Terminates (es ++ [n]) t a) :
    Terminates es t a ∨ (n.label = .eend t ∨ n.label = .retry t) := by
  obtain ⟨hm, hl⟩ := h
  rcases List.mem_append.mp hm with hm | hm
  · exact Or.inl ⟨hm, hl⟩
  · rw [List.mem_singleton.mp hm] at hl; exact Or.inr hl

/-- (T) across a step with `T(n) = ∅` and `Live' ⊆ Live` (get/set, Mem and Log). -/
theorem closed_snoc_keep {es : List Event} {θ θ' : ThId → Option (TxId × Log × Expr)}
    {n : Event}
    (ih : ∀ j t Λ Ê, θ j = some (t, Λ, Ê) → ∀ a, ¬ Terminates es t a)
    (hθ : ∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∃ k Λ' Ê', θ k = some (t, Λ', Ê'))
    (hn : ∀ t, ¬ (n.label = .eend t ∨ n.label = .retry t)) :
    ∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∀ a, ¬ Terminates (es ++ [n]) t a := by
  intro j t Λ Ê hj a ha
  obtain ⟨k, Λ', Ê', hk⟩ := hθ j t Λ Ê hj
  rcases terminates_snoc ha with ha | ha
  · exact ih k t Λ' Ê' hk a ha
  · exact hn t ha

/-- Rewriting thread `i`'s own entry keeps its tag, so `Live' ⊆ Live`. -/
theorem live_update_same {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t₀ : TxId} {Λ₀ Λ₁ : Log} {Ê₀ Ê₁ : Expr} (hi : θ i = some (t₀, Λ₀, Ê₀)) :
    ∀ j t Λ Ê, update θ i (some (t₀, Λ₁, Ê₁)) j = some (t, Λ, Ê) →
      ∃ k Λ' Ê', θ k = some (t, Λ', Ê') := by
  intro j t Λ Ê hj
  rcases update_eq_some hj with ⟨-, hv⟩ | ⟨-, hj⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, -, -⟩ := hv
    exact ⟨i, _, _, hi⟩
  · exact ⟨j, _, _, hj⟩

/-- (T) `Live(C) ∩ Term(τ) = ∅`: a running transaction has no terminator in
the trace so far. Uses (F) from `inv_bbt` at `begin` and (D) from
`inv_distinct` at `end`/`retry`. -/
theorem inv_closed {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → ∀ a, ¬ Terminates (events τ) t a := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → ∀ a, ¬ Terminates (events τ) t a)
    (by intro j t Λ Ê hj; simp [initConfig] at hj) ?_ h
  intro ls C ℓ C' hrun ih hstep
  have hF := (inv_bbt hrun).1
  have hD := inv_distinct hrun
  -- end/retry: `Live' = Live \ {t₀}` by (D), `Term' = Term ∪ {t₀}`
  have term : ∀ {i : ThId} {t₀ : TxId} {Λ₀ : Log} {Ê₀ : Expr} (n : Event),
      C.txs i = some (t₀, Λ₀, Ê₀) →
      (∀ t, (n.label = .eend t ∨ n.label = .retry t) → t = t₀) →
      ∀ j t Λ Ê, update C.txs i none j = some (t, Λ, Ê) →
        ∀ a, ¬ Terminates (events ls ++ [n]) t a := by
    intro i t₀ Λ₀ Ê₀ n hi hn j t Λ Ê hj a ha
    rcases update_eq_some hj with ⟨-, hv⟩ | ⟨hji, hj⟩
    · cases hv
    · rcases terminates_snoc ha with ha | ha
      · exact ih j t Λ Ê hj a ha
      · have hi' : C.txs i = some (t, Λ₀, Ê₀) := by rw [hn t ha]; exact hi
        exact hji (hD j i t Λ Λ₀ Ê Ê₀ hj hi')
  cases hstep with
  | ctx _ hh =>
    cases hh with
    | begin _ _ =>
      -- `Live' = Live ∪ {N}`; `N ∉ Term` by (F)
      simp only [events_snoc_ev]
      intro j t Λ Ê hj a ha
      rcases update_eq_some hj with ⟨-, hv⟩ | ⟨-, hj⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, -, -⟩ := hv
        rcases terminates_snoc ha with ha | ha
        · have hlt := hF a ha.1
          rcases ha.2 with hl | hl <;> simp [hl, Label.tx] at hlt
        · rcases ha with hl | hl <;> cases hl
      · rcases terminates_snoc ha with ha | ha
        · exact ih j t Λ Ê hj a ha
        · rcases ha with hl | hl <;> cases hl
    | getLog _ _ _ =>
      simp only [events_snoc_ev]
      exact closed_snoc_keep ih (fun j t Λ Ê hj => ⟨j, Λ, Ê, hj⟩)
        (by intro t hl; rcases hl with hl | hl <;> cases hl)
    | getMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact closed_snoc_keep ih (live_update_same hi)
        (by intro t hl; rcases hl with hl | hl <;> cases hl)
    | setLog hi _ _ =>
      simp only [events_snoc_ev]
      exact closed_snoc_keep ih (live_update_same hi)
        (by intro t hl; rcases hl with hl | hl <;> cases hl)
    | setMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact closed_snoc_keep ih (live_update_same hi)
        (by intro t hl; rcases hl with hl | hl <;> cases hl)
    | commit hi _ _ =>
      simp only [events_snoc_ev]
      exact term _ hi (by intro t hl; rcases hl with hl | hl <;> cases hl <;> rfl)
    | adm _ =>
      simp only [events_snoc_adm]
      exact ih
  | kcasRetry _ hi _ _ =>
    simp only [events_snoc_ev]
    exact term _ hi (by intro t hl; rcases hl with hl | hl <;> cases hl <;> rfl)
  | retry _ hi _ =>
    simp only [events_snoc_ev]
    exact term _ hi (by intro t hl; rcases hl with hl | hl <;> cases hl <;> rfl)


/-- Lemma N: the event a step emits is not tagged by a transaction that has
already terminated, `tag n ∉ Term(τ)`. (F) at `begin`, (T) otherwise. -/
theorem tag_not_term {E₀ : ThreadMap} {τ : Trace} {C C' : Config} {n : Event}
    (h : Run (initConfig E₀) τ C) (hstep : Trans C (.ev n) C') :
    ∀ a, ¬ Terminates (events τ) n.label.tx a := by
  have hF := (inv_bbt h).1
  have hT := inv_closed h
  intro a ha
  cases hstep with
  | ctx _ hh =>
    cases hh with
    | begin _ _ =>
      have hlt := hF a ha.1
      rw [ha.tx] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
    | getLog hi _ _ => exact hT _ _ _ _ hi a ha
    | getMem hi _ _ _ => exact hT _ _ _ _ hi a ha
    | setLog hi _ _ => exact hT _ _ _ _ hi a ha
    | setMem hi _ _ _ => exact hT _ _ _ _ hi a ha
    | commit hi _ _ => exact hT _ _ _ _ hi a ha
  | kcasRetry _ hi _ _ => exact hT _ _ _ _ hi a ha
  | retry _ hi _ => exact hT _ _ _ _ hi a ha

/-- A `begin` event can only be emitted with tag `nextTx`. -/
theorem Trans.begin_tag {C C' : Config} {n : Event} {t : TxId}
    (hstep : Trans C (.ev n) C') (hn : n.label = .begin t) : t = C.nextTx := by
  cases hstep with
  | ctx _ hh => cases hh <;> simp_all
  | kcasRetry => simp at hn
  | retry => simp at hn

theorem begins_mono {es : List Event} {n : Event} {t : TxId}
    (h : ∃ b, Begins es t b) : ∃ b, Begins (es ++ [n]) t b := by
  sorry

/-- Every tag used so far, and every live tag, has a `begin`, across one step. -/
theorem begun_snoc {es : List Event} {θ' : ThId → Option (TxId × Log × Expr)} {n : Event}
    (ih1 : ∀ e ∈ es, ∃ b, Begins es e.label.tx b)
    (hn : ∃ b, Begins (es ++ [n]) n.label.tx b)
    (hθ : ∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∃ b, Begins (es ++ [n]) t b) :
    (∀ e ∈ es ++ [n], ∃ b, Begins (es ++ [n]) e.label.tx b)
    ∧ (∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∃ b, Begins (es ++ [n]) t b) := by
  refine ⟨fun e he => ?_, hθ⟩
  rcases List.mem_append.mp he with he | he
  · exact begins_mono (ih1 e he)
  · rw [List.mem_singleton.mp he]; exact hn

/-- Every tag in the trace, and every live tag, has a `begin` in the trace. -/
theorem inv_begun {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    (∀ e ∈ events τ, ∃ b, Begins (events τ) e.label.tx b)
    ∧ (∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → ∃ b, Begins (events τ) t b) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      (∀ e ∈ events τ, ∃ b, Begins (events τ) e.label.tx b)
      ∧ (∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → ∃ b, Begins (events τ) t b))
    ⟨by simp [events], by intro j t Λ Ê hj; simp [initConfig] at hj⟩ ?_ h
  rintro ls C ℓ C' _ ⟨ih1, ih2⟩ hstep
  -- a thread that keeps (or drops) its tag: every live tag of `C'` was live in `C`
  have keep : ∀ {θ' : ThId → Option (TxId × Log × Expr)} (n : Event),
      (∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∃ k Λ' Ê', C.txs k = some (t, Λ', Ê')) →
      ∀ j t Λ Ê, θ' j = some (t, Λ, Ê) → ∃ b, Begins (events ls ++ [n]) t b := by
    intro θ' n hθ j t Λ Ê hj
    obtain ⟨k, Λ', Ê', hk⟩ := hθ j t Λ Ê hj
    exact begins_mono (ih2 k t Λ' Ê' hk)
  have drop : ∀ {i : ThId} (j : ThId) t Λ Ê, update C.txs i none j = some (t, Λ, Ê) →
      ∃ k Λ' Ê', C.txs k = some (t, Λ', Ê') := by
    intro i j t Λ Ê hj
    rcases update_eq_some hj with ⟨-, hv⟩ | ⟨-, hj⟩
    · cases hv
    · exact ⟨j, Λ, Ê, hj⟩
  cases hstep with
  | ctx _ hh =>
    cases hh with
    | begin _ _ =>
      simp only [events_snoc_ev]
      refine begun_snoc ih1 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩ ?_
      intro j t Λ Ê hj
      rcases update_eq_some hj with ⟨-, hv⟩ | ⟨-, hj⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, -, -⟩ := hv
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      · exact begins_mono (ih2 j t Λ Ê hj)
    | getLog hi _ _ =>
      simp only [events_snoc_ev]
      exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi))
        (keep _ (fun j t Λ Ê hj => ⟨j, Λ, Ê, hj⟩))
    | getMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ (live_update_same hi))
    | setLog hi _ _ =>
      simp only [events_snoc_ev]
      exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ (live_update_same hi))
    | setMem hi _ _ _ =>
      simp only [events_snoc_ev]
      exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ (live_update_same hi))
    | commit hi _ _ =>
      simp only [events_snoc_ev]
      exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ drop)
    | adm _ =>
      simp only [events_snoc_adm]
      exact ⟨ih1, ih2⟩
  | kcasRetry _ hi _ _ =>
    simp only [events_snoc_ev]
    exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ drop)
  | retry _ hi _ =>
    simp only [events_snoc_ev]
    exact begun_snoc ih1 (begins_mono (ih2 _ _ _ _ hi)) (keep _ drop)


-- AI
-- These gaps have been identified by claude.
-- Facts the pen-and-paper proof uses without an argument. Left as `sorry`.

-- H3, H4 ("using some uniqueness"): a transaction has at most one terminator
-- By construction or definition I think these sorries can be discharged
-- Prima facie looks correct.
theorem term_unique {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {t : TxId} {a a' : Event}
    (ha : Terminates (events τ) t a) (ha' : Terminates (events τ) t a') : a = a' := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t a a', Terminates (events τ) t a → Terminates (events τ) t a' → a = a')
    (by intro t a a' ha; simp [events, Terminates] at ha) ?_ h t a a' ha ha'
  intro ls C ℓ C' hrun ih hstep
  cases ℓ with
  | adm => simp only [events_snoc_adm]; exact ih
  | ev n =>
    simp only [events_snoc_ev]
    intro t a a' ha ha'
    have key : ∀ b, Terminates (events ls ++ [n]) t b → b = n ∨ Terminates (events ls) t b := by
      intro b hb
      rcases List.mem_append.mp hb.1 with hm | hm
      · exact Or.inr ⟨hm, hb.2⟩
      · exact Or.inl (List.mem_singleton.mp hm)
    have hN := tag_not_term hrun hstep
    -- a second terminator of `t` would be emitted while `t ∈ Term`: Lemma N
    rcases key a ha with rfl | ha₀ <;> rcases key a' ha' with rfl | ha₀'
    · rfl
    · exact absurd ha₀' (by rw [← ha.tx]; exact hN a')
    · exact absurd ha₀ (by rw [← ha'.tx]; exact hN a)
    · exact ih t a a' ha₀ ha₀'

/-- H3, H4 ("using some uniqueness"): a transaction has at most one `begin`. -/
theorem begin_unique {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {t : TxId} {b b' : Event}
    (hb : Begins (events τ) t b) (hb' : Begins (events τ) t b') : b = b' := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t b b', Begins (events τ) t b → Begins (events τ) t b' → b = b')
    (by intro t b b' hb; simp [events, Begins] at hb) ?_ h t b b' hb hb'
  intro ls C ℓ C' hrun ih hstep
  cases ℓ with
  | adm => simp only [events_snoc_adm]; exact ih
  | ev n =>
    simp only [events_snoc_ev]
    intro t b b' hb hb'
    have key : ∀ c, Begins (events ls ++ [n]) t c → c = n ∨ Begins (events ls) t c := by
      intro c hc
      rcases List.mem_append.mp hc.1 with hm | hm
      · exact Or.inr ⟨hm, hc.2⟩
      · exact Or.inl (List.mem_singleton.mp hm)
    have hF := (inv_bbt hrun).1
    -- the new `begin` mints `nextTx`, which no older event carries: (F)
    have fresh : ∀ c, n.label = .begin t → Begins (events ls) t c → False := by
      intro c hn hc
      have hlt := hF c hc.1
      rw [hc.tx, hstep.begin_tag hn] at hlt
      exact Nat.lt_irrefl _ hlt
    rcases key b hb with rfl | hb₀ <;> rcases key b' hb' with rfl | hb₀'
    · rfl
    · exact (fresh b' hb.2 hb₀').elim
    · exact (fresh b hb'.2 hb₀).elim
    · exact ih t b b' hb₀ hb₀'

/-- H2, both pending: a pending transaction has a `begin` to be ordered by. -/
theorem begins_of_txs {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {T : Transaction} (hT : txsOfTrace τ T) :
    ∃ b, Begins (events τ) T.txid b := by
  obtain ⟨t, ⟨e, he, hte⟩, rfl⟩ := hT
  obtain ⟨b, hb⟩ := (inv_begun h).1 e he
  rw [hte] at hb
  exact ⟨b, hb⟩



/-- H1: by construction, `A ↔ A`. -/
theorem witness_h1 (τ : Trace) : ∀ T, (witness τ).txs T ↔ txsOfTrace τ T := by
  sorry

/-- H2: case on the status of `S` and `T`. -/
theorem witness_h2 {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ S T, (witness τ).txs S → (witness τ).txs T → S ≠ T →
      (witness τ).ar S T ∨ (witness τ).ar T S := by
  intro S T hS hT hne
  simp only [witness, finishOrder]
  -- distinct transactions have distinct tags, so their events differ
  have hdiff : ∀ a b : Event, a.label.tx = S.txid → b.label.tx = T.txid → a ≠ b :=
    fun a b ha hb hab => hne (txsOf_txid_inj hS hT (by rw [← ha, ← hb, hab]))
  by_cases fS : Finished (events τ) S.txid <;> by_cases fT : Finished (events τ) T.txid
  · -- both finished: order the terminators
    obtain ⟨a, ha⟩ := fS
    obtain ⟨b, hb⟩ := fT
    rcases OccursBefore.total ha.1 hb.1 with hab | hab | hba
    · exact Or.inl (Or.inl ⟨a, b, ha, hb, hab⟩)
    · exact absurd hab (hdiff a b ha.tx hb.tx)
    · exact Or.inr (Or.inl ⟨b, a, hb, ha, hba⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨fS, fT⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨fT, fS⟩))
  · -- both pending: order the begins
    obtain ⟨a, ha⟩ := begins_of_txs h hS
    obtain ⟨b, hb⟩ := begins_of_txs h hT
    rcases OccursBefore.total ha.1 hb.1 with hab | hab | hba
    · exact Or.inl (Or.inr (Or.inr ⟨fS, fT, a, b, ha, hb, hab⟩))
    · exact absurd hab (hdiff a b ha.tx hb.tx)
    · exact Or.inr (Or.inr (Or.inr ⟨fT, fS, b, a, hb, ha, hba⟩))

/-- H3: the same case analysis. The mixed cases would put a pending
transaction before a finished one. -/
theorem witness_h3 {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ S T, (witness τ).txs S → (witness τ).txs T →
      (witness τ).ar S T → ¬ (witness τ).ar T S := by
  intro S T _ _ h1 h2
  have hu := (inv_ids h).2
  simp only [witness, finishOrder] at h1 h2
  rcases h1 with ⟨a, b, ha, hb, hab⟩ | ⟨fS, nfT⟩ | ⟨nfS, nfT, a, b, ha, hb, hab⟩ <;>
  rcases h2 with ⟨b', a', hb', ha', hba⟩ | ⟨fT, nfS'⟩ | ⟨nfT', nfS', b', a', hb', ha', hba⟩
  · -- both finished
    rw [term_unique h hb' hb, term_unique h ha' ha] at hba
    exact OccursBefore.irrefl hu (OccursBefore.trans hu hab hba)
  · exact nfS' ⟨a, ha⟩
  · exact nfS' ⟨a, ha⟩
  · exact nfT ⟨b', hb'⟩
  · exact nfT fT
  · exact nfS' fS
  · exact nfS ⟨a', ha'⟩
  · exact nfT fT
  · -- both pending
    rw [begin_unique h hb' hb, begin_unique h ha' ha] at hba
    exact OccursBefore.irrefl hu (OccursBefore.trans hu hab hba)

/-- H4: case analysis, ditto. Statuses never go from pending to finished. -/
theorem witness_h4 {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ S T U, (witness τ).txs S → (witness τ).txs T → (witness τ).txs U →
      (witness τ).ar S T → (witness τ).ar T U → (witness τ).ar S U := by
  intro S T U _ _ _ h1 h2
  have hu := (inv_ids h).2
  simp only [witness, finishOrder] at h1 h2 ⊢
  rcases h1 with ⟨a, b, ha, hb, hab⟩ | ⟨fS, nfT⟩ | ⟨nfS, nfT, a, b, ha, hb, hab⟩ <;>
  rcases h2 with ⟨b', c, hb', hc, hbc⟩ | ⟨fT, nfU⟩ | ⟨nfT', nfU, b', c, hb', hc, hbc⟩
  · -- fin, fin, fin
    rw [term_unique h hb' hb] at hbc
    exact Or.inl ⟨a, c, ha, hc, OccursBefore.trans hu hab hbc⟩
  · -- fin, fin, pend
    exact Or.inr (Or.inl ⟨⟨a, ha⟩, nfU⟩)
  · exact absurd ⟨b, hb⟩ nfT'
  · exact absurd ⟨b', hb'⟩ nfT
  · exact absurd fT nfT
  · -- fin, pend, pend
    exact Or.inr (Or.inl ⟨fS, nfU⟩)
  · exact absurd ⟨b', hb'⟩ nfT
  · exact absurd fT nfT
  · -- pend, pend, pend: transitivity on `begin`, using uniqueness
    rw [begin_unique h hb' hb] at hbc
    exact Or.inr (Or.inr ⟨nfS, nfU, a, c, ha, hc, OccursBefore.trans hu hab hbc⟩)

-- H5: `RT(S,T)` says `S` ended before `T` began, so `S` is finished.
-- `T` pending: the middle clause. `T` finished: `begin_T ≺ term_T`
theorem witness_h5 {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ S T, (witness τ).txs S → (witness τ).txs T → S ≠ T →
      RealTimeBefore (events τ) S.txid T.txid → (witness τ).ar S T := by
  intro S T _ _ _ ⟨a, b, ha, hb, hab⟩
  simp only [witness, finishOrder]
  by_cases fT : Finished (events τ) T.txid
  · obtain ⟨c, hc⟩ := fT
    have hbc := (inv_bbt h).2.2 T.txid b c hb hc
    exact Or.inl ⟨a, c, ha, hc, OccursBefore.trans (inv_ids h).2 hab hbc⟩
  · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fT⟩)


theorem historyOf_exists {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (h : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H :=
  ⟨witness τ, witness_h1 τ, witness_h2 h, witness_h3 h, witness_h4 h, witness_h5 h⟩

end Optimistic
