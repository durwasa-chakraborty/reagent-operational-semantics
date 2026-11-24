import Reagent.Run

namespace Reagent
-- TODO
-- Understanding why ∀
-- `HEvent_x`: the label is a read or a write on `x`.
def Label.accesses (x : Loc) : Label → Bool
  | .get l _ _ => l == x
  | .set l _ _ => l == x
  | _          => false

-- The value a read or a write carries.
def Label.accessVal : Label → Option Nat
  | .get _ v _ => some v
  | .set _ v _ => some v
  | _          => none

-- NOTE`a ∈ po⁻¹(e) ∩ HEvent_x`: within `T`, `a` `po`-precedes `e` and accesses `x`.
-- `po` is strict, so nothing has to say `a ≠ e`.
def Transaction.PriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.po a e ∧ a.val.label.accesses x = true


-- NOTE `a = max_po ( po⁻¹(e) ∩ HEvent_x )`: the last thing `T` did to `x` before `e`.
def Transaction.MaxPriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.PriorAccess x a e ∧ ∀ b, T.PriorAccess x b e → b = a ∨ T.po b a
/-
  Reagent :: INT
      ∀ (E, po) ∈ H. ∀ e ∈ E. ∀ x, n.
        ( e = (_, get(x,n))  ∧  po⁻¹(e) ∩ HEvent_x ≠ ∅ )
          ⟹  max_po ( po⁻¹(e) ∩ HEvent_x ) = (_, _(x,n))
-/
-- NOTE the whole of the Transaction.INT
def Transaction.Int (T : Transaction) : Prop :=
  ∀ (e : Subtype T.E) (x n : Nat) (t : TxId),
    e.val.label = .get x n t →
    ∀ a : Subtype T.E, T.MaxPriorAccess x a e → a.val.label.accessVal = some n

-- NOTE `H ⊨ Int`.  Every transaction of `H`, committed or not.
def History.Int (H : History) : Prop := ∀ T, H.txs T → T.Int

-- AI
-- I didn't get time to understand the entirety of the following section.
-- Will be more prepared for the next week to understand what is going on in the proof.
theorem OccursBefore.snoc_last {es : List Event} {a n : Event} (ha : a ∈ es) :
    OccursBefore (es ++ [n]) a n := by
  obtain ⟨p, s, rfl⟩ := mem_split ha
  have h := OccursBefore.of_split p s [] a n
  simpa using h

theorem OccursBefore.snoc_mono {es : List Event} {a b n : Event}
    (h : OccursBefore es a b) : OccursBefore (es ++ [n]) a b :=
  OccursBefore.post [n] h

theorem inv_nextTx {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    (∀ e ∈ events τ, e.label.tx < C.nextTx) ∧
      (∀ t, C.activeTx = some t → t < C.nextTx) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      (∀ e ∈ events τ, e.label.tx < C.nextTx) ∧
        (∀ t, C.activeTx = some t → t < C.nextTx))
    ⟨by simp [events], by simp [initConfig]⟩ ?_ h
  rintro ls C m C' _ ⟨ih1, ih2⟩ hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @get σ i t E snap body n u l v α hfresh hv =>
    refine ⟨fun e he => ?_, ih2⟩
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih1 e h'
    · have hea : e = ⟨α, Label.get l v t⟩ := by simpa using h'
      subst hea; exact ih2 t rfl
  | @set σ i t E snap body n u l v α hfresh =>
    refine ⟨fun e he => ?_, ih2⟩
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih1 e h'
    · have hea : e = ⟨α, Label.set l v t⟩ := by simpa using h'
      subst hea; exact ih2 t rfl
  | @eend σ i t E snap body n u α hfresh =>
    refine ⟨fun e he => ?_, by simp⟩
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih1 e h'
    · have hea : e = ⟨α, Label.eend t⟩ := by simpa using h'
      subst hea; exact ih2 t rfl
  | @retry σ i t E snap body n u α hfresh =>
    refine ⟨fun e he => ?_, by simp⟩
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih1 e h'
    · have hea : e = ⟨α, Label.retry t⟩ := by simpa using h'
      subst hea; exact ih2 t rfl
  | @begin σ θ E snap body n u i eb α hfresh =>
    refine ⟨fun e he => ?_, ?_⟩
    · rw [events_snoc_ev] at he
      rcases List.mem_append.mp he with h' | h'
      · exact Nat.lt_succ_of_lt (ih1 e h')
      · have hea : e = ⟨α, Label.begin n⟩ := by simpa using h'
        subst hea; exact Nat.lt_succ_self _
    · intro t' ht'
      have hn : n = t' := Option.some.inj ht'
      subst hn
      exact Nat.lt_succ_self _
  | @adm Cadm i r eb hloc =>
    refine ⟨fun e he => ?_, ih2⟩
    rw [events_snoc_adm] at he
    exact ih1 e he

def LastAccess (es : List Event) (t : TxId) (x : Loc) (a : Event) : Prop :=
  a ∈ es ∧ a.label.tx = t ∧ a.label.accesses x = true ∧
    ∀ b ∈ es, b.label.tx = t → b.label.accesses x = true → ¬ OccursBefore es a b

theorem inv_store {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∀ (x : Loc) (a : Event),
      LastAccess (events τ) t x a → a.label.accessVal = some (C.store x) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∀ (x : Loc) (a : Event),
        LastAccess (events τ) t x a → a.label.accessVal = some (C.store x))
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro t' ht' x a hlast
    have htt : t = t' := Option.some.inj ht'
    subst htt
    obtain ⟨hmem, htag, hacc, hmax⟩ := hlast
    rw [events_snoc_ev] at hmem hmax
    by_cases hlx : l = x
    · subst hlx
      have hnew : a = ⟨α, Label.get l v t⟩ := by
        rcases List.mem_append.mp hmem with h' | h'
        · exact absurd (OccursBefore.snoc_last h')
            (hmax ⟨α, Label.get l v t⟩ (by simp) rfl (by simp [Label.accesses]))
        · simpa using h'
      subst hnew
      simp [Label.accessVal, hv]
    · have hain : a ∈ events ls := by
        rcases List.mem_append.mp hmem with h' | h'
        · exact h'
        · have hea : a = ⟨α, Label.get l v t⟩ := by simpa using h'
          subst hea
          simp [Label.accesses, hlx] at hacc
      refine ih t rfl x a ⟨hain, htag, hacc, ?_⟩
      intro b hb hbtag hbacc hob
      exact hmax b (List.mem_append.mpr (Or.inl hb)) hbtag hbacc (OccursBefore.snoc_mono hob)
  | @set σ i t E snap body n u l v α hfresh =>
    intro t' ht' x a hlast
    have htt : t = t' := Option.some.inj ht'
    subst htt
    obtain ⟨hmem, htag, hacc, hmax⟩ := hlast
    rw [events_snoc_ev] at hmem hmax
    by_cases hlx : l = x
    · subst hlx
      have hnew : a = ⟨α, Label.set l v t⟩ := by
        rcases List.mem_append.mp hmem with h' | h'
        · exact absurd (OccursBefore.snoc_last h')
            (hmax ⟨α, Label.set l v t⟩ (by simp) rfl (by simp [Label.accesses]))
        · simpa using h'
      subst hnew
      simp [Label.accessVal, update]
    · have hain : a ∈ events ls := by
        rcases List.mem_append.mp hmem with h' | h'
        · exact h'
        · have hea : a = ⟨α, Label.set l v t⟩ := by simpa using h'
          subst hea
          simp [Label.accesses, hlx] at hacc
      have hmax' : ∀ b ∈ events ls, b.label.tx = t → b.label.accesses x = true →
          ¬ OccursBefore (events ls) a b := by
        intro b hb hbtag hbacc hob
        exact hmax b (List.mem_append.mpr (Or.inl hb)) hbtag hbacc (OccursBefore.snoc_mono hob)
      have hih := ih t rfl x a ⟨hain, htag, hacc, hmax'⟩
      rw [hih]
      show some (σ x) = some (update σ l v x)
      rw [update, if_neg (fun hc => hlx hc.symm)]
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro t' ht' x a hlast
    have hn : n = t' := Option.some.inj ht'
    subst hn
    exfalso
    obtain ⟨hmem, htag, hacc, -⟩ := hlast
    rw [events_snoc_ev] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · have hlt := (inv_nextTx hrunls).1 a h'
      rw [htag] at hlt
      exact Nat.lt_irrefl _ hlt
    · have hea : a = ⟨α, Label.begin n⟩ := by simpa using h'
      subst hea
      simp [Label.accesses] at hacc
  | @eend σ i t E snap body n u α hfresh =>
    intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n u α hfresh =>
    intro t' ht'; exact absurd ht' (by simp)
  | @adm Cadm i r eb hloc =>
    intro t' ht' x a hlast
    rw [events_snoc_adm] at hlast
    exact ih t' ht' x a hlast

--`∀ H`, and it stays `∀ H`: `Int` is intra-transactional and never reads `ar`.
theorem OccursBefore.mem {es : List Event} {a b : Event} (h : OccursBefore es a b) :
    a ∈ es ∧ b ∈ es := by
  obtain ⟨p, m, s, rfl⟩ := h.split
  constructor <;> simp

theorem OccursBefore.restrict_append {A B : List Event} {a b : Event}
    (hu : UniqueIds (A ++ B)) (ha : a ∈ A) (hb : b ∈ A)
    (h : OccursBefore (A ++ B) a b) : OccursBefore A a b := by
  obtain ⟨A1, A2, rfl⟩ := mem_split ha
  rcases List.mem_append.mp hb with hb1 | hb2
  · exfalso
    obtain ⟨B1, B2, hA1⟩ := mem_split hb1
    subst hA1
    have hba : OccursBefore (B1 ++ [b] ++ B2 ++ [a] ++ A2) b a :=
      OccursBefore.of_split _ _ _ _ _
    have hba' : OccursBefore ((B1 ++ [b] ++ B2 ++ [a] ++ A2) ++ B) b a :=
      OccursBefore.post B hba
    have hu' : UniqueIds ((B1 ++ [b] ++ B2 ++ [a] ++ A2) ++ B) := by
      simpa [UniqueIds] using hu
    have hbb := OccursBefore.trans hu' hba' (by simpa using h)
    exact OccursBefore.irrefl hu' hbb
  · rcases List.mem_cons.mp hb2 with rfl | hb3
    · exfalso
      exact OccursBefore.irrefl hu h
    · obtain ⟨C1, C2, rfl⟩ := mem_split hb3
      have := OccursBefore.of_split A1 C1 C2 a b
      simpa using this

theorem isAccess_of_accesses {lb : Label} {x : Loc} (h : lb.accesses x = true) :
    lb.isAccess = true := by
  cases lb <;> simp_all [Label.accesses, Label.isAccess]

/-- `a` is the last access of `t` to `x` before `e`. -/
def LastAccessBefore (es : List Event) (t : TxId) (x : Loc) (a e : Event) : Prop :=
  a ∈ es ∧ a.label.tx = t ∧ a.label.accesses x = true ∧ OccursBefore es a e ∧
    ∀ b ∈ es, b.label.tx = t → b.label.accesses x = true →
      OccursBefore es a b → ¬ OccursBefore es b e

/-- Nothing occurs after the newcomer. -/
theorem not_occursBefore_snoc {es : List Event} {e n : Event}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es) : ¬ OccursBefore (es ++ [n]) n e := by
  intro h
  exact OccursBefore.irrefl hu (OccursBefore.trans hu (OccursBefore.snoc_last he) h)

/-- An older read's last access is unchanged by appending. -/
theorem lastAccessBefore_of_snoc {es : List Event} {t : TxId} {x : Loc} {a e n : Event}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es)
    (h : LastAccessBefore (es ++ [n]) t x a e) : LastAccessBefore es t x a e := by
  obtain ⟨hmem, htag, hacc, hbef, hmax⟩ := h
  have hain : a ∈ es := by
    rcases List.mem_append.mp hmem with h' | h'
    · exact h'
    · have hea : a = n := by simpa using h'
      subst hea
      exact absurd hbef (not_occursBefore_snoc hu he)
  refine ⟨hain, htag, hacc, OccursBefore.restrict_append hu hain he hbef, ?_⟩
  intro b hb hbtag hbacc hab hbe
  exact hmax b (List.mem_append.mpr (Or.inl hb)) hbtag hbacc
    (OccursBefore.snoc_mono hab) (OccursBefore.snoc_mono hbe)

/-- **`Int` on the events of a run.**  Every read sees the value its own
transaction last left at that location. -/
theorem inv_int {E₀ : ThreadMap} {τ : Trace} {C : Config} (h : Run (initConfig E₀) τ C) :
    ∀ (x n : Nat) (t : TxId) (e a : Event),
      e ∈ events τ → e.label = .get x n t →
      LastAccessBefore (events τ) t x a e → a.label.accessVal = some n := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ (x n : Nat) (t : TxId) (e a : Event),
        e ∈ events τ → e.label = .get x n t →
        LastAccessBefore (events τ) t x a e → a.label.accessVal = some n)
    (by intro x n t e a he _ _; simp [events] at he) ?_ h
  intro ls C m C' hrunls ih hstep
  have hu : UniqueIds (events (ls ++ [m])) := (inv_ids (hrunls.snoc hstep)).2
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with h' | h'
    · -- an older read: appending changed nothing for it
      exact ih x nn t'' e a h' hlab (lastAccessBefore_of_snoc hu h' hlast)
    · -- the read just taken
      have hea : e = ⟨α, Label.get l v t⟩ := by simpa using h'
      subst hea
      simp at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨hmem, htag, hacc, hbef, hmax⟩ := hlast
      have hain : a ∈ events ls := by
        rcases List.mem_append.mp hmem with h'' | h''
        · exact h''
        · have hae : a = ⟨α, Label.get l v t⟩ := by simpa using h''
          subst hae
          exact absurd hbef (OccursBefore.irrefl hu)
      have hlastacc : LastAccess (events ls) t l a := by
        refine ⟨hain, htag, hacc, ?_⟩
        intro b hb hbtag hbacc hob
        exact hmax b (List.mem_append.mpr (Or.inl hb)) hbtag hbacc
          (OccursBefore.snoc_mono hob) (OccursBefore.snoc_last hb)
      have hst := inv_store hrunls t rfl l a hlastacc
      rw [hst]
      show some (σ l) = some v
      rw [hv]
  | @set σ i t E snap body n u l v α hfresh =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with h' | h'
    · exact ih x nn t'' e a h' hlab (lastAccessBefore_of_snoc hu h' hlast)
    · have hea : e = ⟨α, Label.set l v t⟩ := by simpa using h'
      subst hea; simp at hlab
  | @eend σ i t E snap body n u α hfresh =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with h' | h'
    · exact ih x nn t'' e a h' hlab (lastAccessBefore_of_snoc hu h' hlast)
    · have hea : e = ⟨α, Label.eend t⟩ := by simpa using h'
      subst hea; simp at hlab
  | @retry σ i t E snap body n u α hfresh =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with h' | h'
    · exact ih x nn t'' e a h' hlab (lastAccessBefore_of_snoc hu h' hlast)
    · have hea : e = ⟨α, Label.retry t⟩ := by simpa using h'
      subst hea; simp at hlab
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with h' | h'
    · exact ih x nn t'' e a h' hlab (lastAccessBefore_of_snoc hu h' hlast)
    · have hea : e = ⟨α, Label.begin n⟩ := by simpa using h'
      subst hea; simp at hlab
  | @adm Cadm i r eb hloc =>
    intro x nn t'' e a he hlab hlast
    rw [events_snoc_adm] at he hlast
    exact ih x nn t'' e a he hlab hlast

theorem int_of_run {E₀ : ThreadMap} {τ : Trace} {C' : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C') (hH : HistoryOf τ H) : H.Int := by
  intro T hT
  obtain ⟨htxs, -⟩ := hH
  obtain ⟨t₀, -, hTeq⟩ := (htxs T).mp hT
  subst hTeq
  intro e x n t hlab a hmax
  obtain ⟨⟨hpo, hacc⟩, hgreatest⟩ := hmax
  have hu : UniqueIds (events τ) := (inv_ids hrun).2
  have htag_e : e.val.label.tx = t₀ := e.property.2.1
  have htt : t₀ = t := by rw [← htag_e, hlab]; rfl
  refine inv_int hrun x n t e.val a.val e.property.1 hlab
    ⟨a.property.1, ?_, hacc, hpo, ?_⟩
  · rw [a.property.2.1, htt]
  · intro b hb hbtag hbacc hab hbe
    have hbAcc : b.label.isAccess = true := isAccess_of_accesses hbacc
    have hbE : events_of_isAccess (events τ) t₀ b := ⟨hb, by rw [hbtag, ← htt], hbAcc⟩
    rcases hgreatest ⟨b, hbE⟩ ⟨hbe, hbacc⟩ with heq | hba
    · have hba' : b = a.val := congrArg Subtype.val heq
      rw [hba'] at hab
      exact OccursBefore.irrefl hu hab
    · exact OccursBefore.irrefl hu (OccursBefore.trans hu hab hba)

end Reagent
