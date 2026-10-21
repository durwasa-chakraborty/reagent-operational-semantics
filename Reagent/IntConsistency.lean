/-
  Reagent — internal consistency (§Internal consistency, `docs/reagent-correctness.tex:545`).

  Cerone et al.'s axiom:

      ∀ (E, po) ∈ H. ∀ e ∈ E. ∀ x, n.
        ( e = (_, get(x,n))  ∧  po⁻¹(e) ∩ HEvent_x ≠ ∅ )
          ⟹  max_po ( po⁻¹(e) ∩ HEvent_x ) = (_, _(x,n))


-/
import Reagent.Trace

namespace Reagent

/-! ## The axiom -/

/-- `HEvent_x`: the label is a read or a write on `x`. -/
def Label.accesses (x : Loc) : Label → Bool
  | .get l _ _ => l == x
  | .set l _ _ => l == x
  | _          => false

/-- The value a read or a write carries; `none` for `begin`/`eend`/`retry`. -/
def Label.accessVal : Label → Option Nat
  | .get _ v _ => some v
  | .set _ v _ => some v
  | _          => none

/-- `a ∈ po⁻¹(e) ∩ HEvent_x`: within `T`, `a` strictly `po`-precedes `e` and
accesses `x`.

`T.po` is reflexive (`IsTotalOrder`), so the strictness of `po⁻¹` is spelled
out as `a ≠ e`. -/
def Transaction.PriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.po a e ∧ a ≠ e ∧ a.val.label.accesses x = true

/-- `a = max_po ( po⁻¹(e) ∩ HEvent_x )`.

NOTE `a` is the last thing a transaction did to x before e. -/
def Transaction.MaxPriorAccess (T : Transaction) (x : Loc) (e a : Subtype T.E) : Prop :=
  T.PriorAccess x a e ∧ ∀ b, T.PriorAccess x b e → T.po b a

/-- **Int** for a single transaction. Verbatim -/
def Transaction.Int (T : Transaction) : Prop :=
  ∀ (e : Subtype T.E) (x n : Nat) (t : TxId),
    e.val.label = .get x n t →
    ∀ a : Subtype T.E, T.MaxPriorAccess x e a → a.val.label.accessVal = some n

/-- `H ⊨ Int`.  Every transaction of `H`, committed or not  `T.status` never
enters (§ Internal consistency, first example). -/
def History.Int (H : History) : Prop := ∀ T, H.txs T → T.Int

/-! ## The machine half

Everything below is about `τ` and the configuration only; no `History` appears.
Ported from `archive/IntConsistency.pre-declarative.lean`, restated on positions
of `τ` rather than on the old `traceEvents` list. -/

/-- A run splits at any point where its trace does. -/
theorem Trace.split {C₀ C'' : Config} {pre post : List TLabel}
    (h : Trace C₀ (pre ++ post) C'') : ∃ C', Trace C₀ pre C' ∧ Trace C' post C'' := by
  induction pre generalizing C₀ with
  | nil => exact ⟨C₀, .nil, h⟩
  | cons ℓ ls ih =>
    cases h with
    | cons hstep hrest =>
      obtain ⟨C', h1, h2⟩ := ih hrest
      exact ⟨C', .cons hstep h1, h2⟩

/-- Reverse (snoc) induction on lists; core provides no such recursor. -/
theorem listReverseInduction {α : Type} {motive : List α → Prop}
    (nil : motive []) (snoc : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) :
    ∀ l, motive l := fun l => by
  have h : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a as ih => simpa using snoc as.reverse a ih
  simpa using h l.reverse

/-- Induction on a run from its last step. -/
theorem Trace.reverseRecOn {C₀ : Config} {motive : List TLabel → Config → Prop}
    (base : motive [] C₀)
    (ind : ∀ (ℓs : List TLabel) (C : Config) (ℓ : TLabel) (C' : Config),
      Trace C₀ ℓs C → motive ℓs C → Trans C ℓ C' → motive (ℓs ++ [ℓ]) C')
    {ℓs : List TLabel} {C : Config} (h : Trace C₀ ℓs C) : motive ℓs C := by
  induction ℓs using listReverseInduction generalizing C with
  | nil => cases h; exact base
  | snoc ls ℓ ih =>
    obtain ⟨C', h1, h2⟩ := Trace.split h
    cases h2 with
    | cons hstep hrest =>
      cases hrest
      exact ind ls C' ℓ C h1 (ih h1) hstep

/-- Reading position `i` of a snoc: either it is a position of the prefix, or it
is the appended element itself. -/
theorem getElem?_snoc {α : Type} {l : List α} {a b : α} {i : Nat}
    (h : (l ++ [a])[i]? = some b) : l[i]? = some b ∨ (i = l.length ∧ a = b) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · left; rwa [List.getElem?_append_left hi] at h
  · rw [List.getElem?_append_right hi] at h
    rcases Nat.eq_or_lt_of_le hi with he | he
    · subst he
      exact Or.inr ⟨rfl, by simpa using h⟩
    · exfalso
      have h1 : [a].length ≤ i - l.length := by simp; omega
      rw [List.getElem?_eq_none h1] at h
      simp at h

/-- A position of the prefix is the same position of the snoc. -/
theorem getElem?_snoc_left {α : Type} {l : List α} {a b : α} {k : Nat}
    (h : l[k]? = some b) : (l ++ [a])[k]? = some b := by
  have hk : k < l.length := by
    rcases Nat.lt_or_ge k l.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h; simp at h
  rw [List.getElem?_append_left hk]; exact h

/-- Every transaction id occurring in the trace so far, and the live one, lies
below `nextTx`.  This is what makes `Begin`'s minted id genuinely fresh, and it
is what makes a newly begun transaction have no history. -/
theorem inv_nextTx {E₀ : ThreadMap} {τ : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) τ C) :
    (∀ (i : Nat) (lb : Label), τ[i]? = some (TLabel.ev lb) → lb.tx < C.nextTx) ∧
      (∀ t, C.activeTx = some t → t < C.nextTx) := by
  refine Trace.reverseRecOn (motive := fun τ C =>
      (∀ (i : Nat) (lb : Label), τ[i]? = some (TLabel.ev lb) → lb.tx < C.nextTx) ∧
        (∀ t, C.activeTx = some t → t < C.nextTx))
    ⟨by simp, by simp [initConfig]⟩ ?_ h
  rintro ls C m C' _ ⟨ih1, ih2⟩ hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @get σ i t E snap body n l v hv =>
    refine ⟨fun k lb hk => ?_, ih2⟩
    rcases getElem?_snoc hk with h' | ⟨_, h'⟩
    · exact ih1 _ _ h'
    · cases h'; exact ih2 t rfl
  | @set σ i t E snap body n l v =>
    refine ⟨fun k lb hk => ?_, ih2⟩
    rcases getElem?_snoc hk with h' | ⟨_, h'⟩
    · exact ih1 _ _ h'
    · cases h'; exact ih2 t rfl
  | @eend σ i t E snap body n =>
    refine ⟨fun k lb hk => ?_, by simp⟩
    rcases getElem?_snoc hk with h' | ⟨_, h'⟩
    · exact ih1 _ _ h'
    · cases h'; exact ih2 t rfl
  | @retry σ i t E snap body n =>
    refine ⟨fun k lb hk => ?_, by simp⟩
    rcases getElem?_snoc hk with h' | ⟨_, h'⟩
    · exact ih1 _ _ h'
    · cases h'; exact ih2 t rfl
  | @begin σ θ E snap body n i eb =>
    refine ⟨fun k lb hk => ?_, ?_⟩
    · rcases getElem?_snoc hk with h' | ⟨_, h'⟩
      · exact Nat.lt_succ_of_lt (ih1 _ _ h')
      · cases h'; exact Nat.lt_succ_self _
    · intro t' ht'
      have : n = t' := Option.some.inj ht'
      subst this
      exact Nat.lt_succ_self _
  | @adm Cadm i r eb hloc =>
    refine ⟨fun k lb hk => ?_, ih2⟩
    rcases getElem?_snoc hk with h' | ⟨_, h'⟩
    · exact ih1 _ _ h'
    · exact absurd h' (by simp)

/-- **The store agrees with the live transaction's last access.**

If `t` is the transaction currently holding the lock, then for every location
`x`, the value in the store is the one carried by the `po`-last `t`-tagged
access to `x` in the trace so far.  This is the semantic content of `Int`.

The lock discipline is what makes it true, and it is spent in two cases:
`begin` mints an id below which nothing in the trace can be tagged
(`inv_nextTx`), so a fresh transaction has no history to disagree with; and
`retry`, which rolls the store back, clears `activeTx` in the *same* step, so no
rollback ever lands inside a live transaction.  `eend` likewise leaves no live
transaction for the invariant to constrain. -/
theorem inv_store {E₀ : ThreadMap} {τ : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∀ (x : Loc) (j : Nat) (lb : Label),
      τ[j]? = some (TLabel.ev lb) → lb.tx = t → lb.accesses x = true →
      (∀ (k : Nat) (lb' : Label), τ[k]? = some (TLabel.ev lb') → lb'.tx = t →
        lb'.accesses x = true → k ≤ j) →
      lb.accessVal = some (C.store x) := by
  refine Trace.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∀ (x : Loc) (j : Nat) (lb : Label),
        τ[j]? = some (TLabel.ev lb) → lb.tx = t → lb.accesses x = true →
        (∀ (k : Nat) (lb' : Label), τ[k]? = some (TLabel.ev lb') → lb'.tx = t →
          lb'.accesses x = true → k ≤ j) →
        lb.accessVal = some (C.store x))
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @get σ i t E snap body n l v hv =>
    intro t' ht' x j lb hj htag hacc hmax
    have htt : t = t' := Option.some.inj ht'
    subst htt
    by_cases hlx : l = x
    · subst hlx
      have hle := hmax ls.length (Label.get l v t) (by simp) rfl (by simp [Label.accesses])
      rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
      · exfalso
        have hj' : j < ls.length := by
          rcases Nat.lt_or_ge j ls.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none hge] at h'; simp at h'
        omega
      · cases h'; simp [Label.accessVal, hv]
    · rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
      · exact ih t rfl x j lb h' htag hacc
          (fun k lb' hk => hmax k lb' (getElem?_snoc_left hk))
      · exfalso; cases h'; simp [Label.accesses, hlx] at hacc
  | @set σ i t E snap body n l v =>
    intro t' ht' x j lb hj htag hacc hmax
    have htt : t = t' := Option.some.inj ht'
    subst htt
    by_cases hlx : l = x
    · subst hlx
      have hle := hmax ls.length (Label.set l v t) (by simp) rfl (by simp [Label.accesses])
      rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
      · exfalso
        have hj' : j < ls.length := by
          rcases Nat.lt_or_ge j ls.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none hge] at h'; simp at h'
        omega
      · cases h'; simp [Label.accessVal, update]
    · rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
      · have := ih t rfl x j lb h' htag hacc
          (fun k lb' hk => hmax k lb' (getElem?_snoc_left hk))
        rw [this]
        show some (σ x) = some (update σ l v x)
        rw [update, if_neg (fun hc => hlx hc.symm)]
      · exfalso; cases h'; simp [Label.accesses, hlx] at hacc
  | @begin σ θ E snap body n i eb =>
    intro t' ht' x j lb hj htag hacc hmax
    have hn : n = t' := Option.some.inj ht'
    subst hn
    exfalso
    rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
    · have hlt := (inv_nextTx hrunls).1 j lb h'
      rw [htag] at hlt
      exact Nat.lt_irrefl _ hlt
    · cases h'; simp [Label.accesses] at hacc
  | @eend σ i t E snap body n =>
    intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n =>
    intro t' ht'; exact absurd ht' (by simp)
  | @adm Cadm i r eb hloc =>
    intro t' ht' x j lb hj htag hacc hmax
    rcases getElem?_snoc hj with h' | ⟨hjlen, h'⟩
    · exact ih t' ht' x j lb h' htag hacc
        (fun k lb' hk => hmax k lb' (getElem?_snoc_left hk))
    · exact absurd h' (by simp)

/-! ## The theorem -/

/-- **Internal consistency.**

    ∀ τ, ∀ H.  Trace C_init τ C'  ∧  HistoryOf τ H  ⟹  H ⊨ Int

 -/

theorem int_of_trace {E₀ : ThreadMap} {τ : List TLabel} {C' : Config} {H : History}
    (hrun : Trace (initConfig E₀) τ C') (hH : HistoryOf τ H) : H.Int := by
    intro T hT e x n t hlabel -- a transaction,
    intro a hmax              -- po last access to x before it
    obtain ⟨pos, hat, hinj, hcov, hpo⟩ := hH.placed
    have he_at := (hat T hT e.val e.property).1
    have ha_at := (hat T hT a.val a.property).1
    rw [hlabel] at he_at
    obtain ⟨⟨hae, hne, hacc⟩, hgreatest⟩ := hmax
    have hle : pos a.val ≤ pos e.val := (hpo T hT a e).1 hae
    have hlt : pos a.val < pos e.val := Nat.lt_of_le_of_ne hle (fun heq => hne (Subtype.ext (hinj _ _ heq)))
    have hlast : ∀ k ℓ', k < pos e.val → τ[k]? = some (.ev ℓ') →
        ℓ'.tx = t → ℓ'.accesses x = true → k ≤ pos a.val := by
      intro k l' hk hkat htag hkacc
      -- `hcov` wants `isAccess`, we hold `accesses x`; for begin/eend/retry the
      -- latter is already false, so those cases close themselves
      have hacc' : l'.isAccess = true := by
        cases l' <;> simp_all [Label.accesses, Label.isAccess]
      -- something of `H` sits at `k` — but not necessarily something of `T`
      obtain ⟨T', b, hT', hbT', hbpos⟩ := hcov k l' hkat hacc'
      have hb_at := (hat T' hT' b hbT').1
      rw [hbpos] at hb_at
      have hblab : b.label = l' := by simpa using hb_at.symm.trans hkat
      -- both transactions carry tag `t`, so they are the same transaction
      have hTT : T' = T := by
        refine hH.one_per_tag T' T hT' hT t ⟨b, hbT', ?_⟩ ⟨e.val, e.property, ?_⟩
        · rw [hblab]; exact htag
        · rw [hlabel]; rfl
      subst hTT
      -- so `b` is an event of `T`, and it is a prior access to `x`
      have hbne : pos b ≠ pos e.val := by rw [hbpos]; exact Nat.ne_of_lt hk
      have hprior : T'.PriorAccess x ⟨b, hbT'⟩ e := by
        refine ⟨(hpo T' hT' ⟨b, hbT'⟩ e).2 ?_, ?_, ?_⟩
        · rw [hbpos]; exact Nat.le_of_lt hk
        · exact fun heq => hbne (congrArg (fun z => pos z.val) heq)
        · rw [hblab]; exact hkacc
      -- `hgreatest` applies, and `hpo` carries the answer back to positions
      have := (hpo T' hT' ⟨b, hbT'⟩ a).1 (hgreatest ⟨b, hbT'⟩ hprior)
      rw [hbpos] at this
      exact this
    have hatag : a.val.label.tx = t := by
      have := hH.events_tagged T hT a.val e.val a.property e.property
      rw [this, hlabel]; rfl
    -- split the run immediately before the `get`
    have hilen : pos e.val < τ.length := by
      rcases Nat.lt_or_ge (pos e.val) τ.length with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none hge] at he_at; simp at he_at
    have hsplit : τ = τ.take (pos e.val) ++ τ.drop (pos e.val) :=
      (List.take_append_drop _ _).symm
    rw [hsplit] at hrun
    obtain ⟨Cm, hpre, hpost⟩ := Trace.split hrun
    -- the suffix begins with that very `get`
    have hdrop : τ.drop (pos e.val) = τ[pos e.val] :: τ.drop (pos e.val + 1) :=
      List.drop_eq_getElem_cons hilen
    have hhd : τ[pos e.val] = TLabel.ev (Label.get x n t) := by
      have := he_at; rw [List.getElem?_eq_getElem hilen] at this; simpa using this
    rw [hdrop, hhd] at hpost
    cases hpost with
    | cons hstep _ =>
    cases hstep with
    | ctx _ hhead =>
    cases hhead with
    | @get σ th t' E snap body nn l v hv =>
      -- so at that moment `t` held the lock and the store carried `n` at `x`
      refine inv_store hpre t rfl x (pos a.val) a.val.label ?_ hatag hacc ?_ |>.trans ?_
      · rw [List.getElem?_take, if_pos hlt]; exact ha_at
      · intro k lb' hk htag' hacc'
        have hklt : k < pos e.val := by
          rcases Nat.lt_or_ge k (pos e.val) with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none (by simpa using Nat.le_trans (Nat.min_le_left _ _) h1)] at hk
            simp at hk
        rw [List.getElem?_take, if_pos hklt] at hk
        exact hlast k lb' hklt hk htag' hacc'
      · simpa using hv









/-- The companion the theorem above needs in order not to be vacuous: some
history reads each trace.  `txsOf` (Trace.lean) is the intended witness. -/
theorem exists_historyOf (τ : List TLabel) : ∃ H, HistoryOf τ H := by
  sorry

end Reagent
