/-
  prompt.org, entry "Proving Internal Consistency".

  (D) live threads never run the same t,
  (L) the log mirrors po,
  then Int by induction on the run.
-/
import Optimistic.HistoryOf

namespace Optimistic

open Reagent (Loc TxId ThId ThreadMap Expr update update_other)

/-! ## Int, as Cerone writes it -/

/-- `HEvent_x`: the label is a `get` or a `set` on `x`. -/
def Label.accesses (x : Loc) : Label → Bool
  | .get l _ _ => l == x
  | .set l _ _ => l == x
  | _          => false

/-- The value a `get` or a `set` carries. -/
def Label.accessVal : Label → Option Nat
  | .get _ v _ => some v
  | .set _ v _ => some v
  | _          => none

/-- `a ∈ P_x(e) = po⁻¹(e) ∩ HEvent_x`. -/
def Transaction.PriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.po a e ∧ a.val.label.accesses x = true

/-- `a = max_po P_x(e)`. -/
def Transaction.MaxPriorAccess (T : Transaction) (x : Loc) (a e : Subtype T.E) : Prop :=
  T.PriorAccess x a e ∧ ∀ b, T.PriorAccess x b e → b = a ∨ T.po b a

/-- `e = get(x,n) ∧ P_x(e) ≠ ∅ → max_po P_x(e) = op(x,n)`. -/
def Transaction.Int (T : Transaction) : Prop :=
  ∀ (e : Subtype T.E) (x n : Nat) (t : TxId),
    e.val.label = .get x n t →
    ∀ a : Subtype T.E, T.MaxPriorAccess x a e → a.val.label.accessVal = some n

def History.Int (H : History) : Prop := ∀ T, H.txs T → T.Int

theorem Run.snoc {C₀ C C' : Config} {τ : Trace} {ℓ : TLabel}
    (h : Run C₀ τ C) (hstep : Trans C ℓ C') : Run C₀ (τ ++ [ℓ]) C' := by
  induction h with
  | nil => exact .cons hstep .nil
  | cons hs _ ih => exact .cons hs (ih hstep)

/-! ## (L) the log mirrors po -/

def NoAccess (es : List Event) (t : TxId) (x : Loc) : Prop :=
  ∀ a ∈ es, a.label.tx = t → a.label.accesses x = false

/-- `a` is the latest access to `x` tagged `t`. -/
def LastAccess (es : List Event) (t : TxId) (x : Loc) (a : Event) : Prop :=
  a ∈ es ∧ a.label.tx = t ∧ a.label.accesses x = true ∧
    ∀ b ∈ es, b.label.tx = t → b.label.accesses x = true → ¬ OccursBefore es a b

/-- (L) at one location. Only the `→` half of `Λ(x) = ⊥ ↔ no access` is kept:
the proof of Int never uses the other half. -/
def MirrorsAt (es : List Event) (t : TxId) (Λ : Log) (x : Loc) : Prop :=
  (Λ x = none → NoAccess es t x) ∧
  (∀ o c a, Λ x = some (o, c) → LastAccess es t x a → a.label.accessVal = some c)

def LogMirrors (es : List Event) (θ : ThId → Option (TxId × Log × Expr)) : Prop :=
  ∀ i t Λ Ê, θ i = some (t, Λ, Ê) → ∀ x, MirrorsAt es t Λ x

theorem MirrorsAt.congr {es : List Event} {t : TxId} {Λ Λ' : Log} {x : Loc}
    (h : MirrorsAt es t Λ x) (hx : Λ' x = Λ x) : MirrorsAt es t Λ' x := by
  sorry

/-- Other locations, other threads, non-accesses: an event that is not an
access to `x` tagged `t` changes nothing. -/
theorem MirrorsAt.snoc_irrel {es : List Event} {t : TxId} {Λ : Log} {x : Loc} {n : Event}
    (h : MirrorsAt es t Λ x) (hn : n.label.tx = t → n.label.accesses x = false) :
    MirrorsAt (es ++ [n]) t Λ x := by
  refine ⟨fun hΛ a ha htag => ?_, fun o c a hΛ hlast => ?_⟩
  · rcases List.mem_append.mp ha with ha | ha
    · exact h.1 hΛ a ha htag
    · rw [List.mem_singleton.mp ha] at htag ⊢; exact hn htag
  · obtain ⟨hmem, htag, hacc, hmax⟩ := hlast
    have hain : a ∈ es := by
      rcases List.mem_append.mp hmem with ha | ha
      · exact ha
      · rw [List.mem_singleton.mp ha] at htag hacc
        rw [hn htag] at hacc; cases hacc
    exact h.2 o c a hΛ ⟨hain, htag, hacc, fun b hb hbt hba hob =>
      hmax b (List.mem_append.mpr (Or.inl hb)) hbt hba hob.snoc_mono⟩

/-- Get-Mem, Set-Mem, Set-Log, Get-Log at `x`: the new event is now the latest
access, and the log's current value is its value. -/
theorem MirrorsAt.snoc_new {es : List Event} {t : TxId} {Λ : Log} {x : Loc} {n : Event}
    {o c : Nat} (htag : n.label.tx = t) (hacc : n.label.accesses x = true)
    (hval : n.label.accessVal = some c) (hΛ : Λ x = some (o, c)) :
    MirrorsAt (es ++ [n]) t Λ x := by
  refine ⟨fun h => (by rw [hΛ] at h; cases h), fun o' c' a hΛ' hlast => ?_⟩
  rw [hΛ] at hΛ'
  simp only [Option.some.injEq, Prod.mk.injEq] at hΛ'
  obtain ⟨-, rfl⟩ := hΛ'
  obtain ⟨hmem, -, -, hmax⟩ := hlast
  rcases List.mem_append.mp hmem with ha | ha
  · exact absurd (OccursBefore.snoc_last ha) (hmax n (by simp) htag hacc)
  · rw [List.mem_singleton.mp ha]; exact hval

/-- One step by thread `i` running `t₀`, as seen by any other live thread:
by (D) it runs a different tag, so nothing changes for it. -/
theorem LogMirrors.snoc_other {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {n : Event} {i : ThId} {t₀ : TxId} {Λ₀ : Log} {Ê₀ : Expr}
    (hM : LogMirrors es θ) (hD : LiveDistinct θ) (hi : θ i = some (t₀, Λ₀, Ê₀))
    (htag : n.label.tx = t₀) {k : ThId} {t : TxId} {Λ : Log} {Ê : Expr}
    (hki : k ≠ i) (hk : θ k = some (t, Λ, Ê)) : ∀ x, MirrorsAt (es ++ [n]) t Λ x := by
  have hne : t₀ ≠ t := by
    intro heq; subst heq; exact hki (hD k i t₀ Λ Λ₀ Ê Ê₀ hk hi)
  intro x
  exact (hM k t Λ Ê hk x).snoc_irrel (fun h => absurd (htag.symm.trans h) hne)

/-- The stepping thread itself, after an access to `l` with value `c`. -/
theorem mirrors_access {es : List Event} {t₀ : TxId} {Λ₀ Λ₁ : Log} {n : Event}
    {l : Loc} {o c : Nat}
    (hM : ∀ x, MirrorsAt es t₀ Λ₀ x) (htag : n.label.tx = t₀)
    (hacc : ∀ x, n.label.accesses x = (l == x)) (hval : n.label.accessVal = some c)
    (hΛ₁ : Λ₁ l = some (o, c)) (hrest : ∀ x, l ≠ x → Λ₁ x = Λ₀ x) :
    ∀ x, MirrorsAt (es ++ [n]) t₀ Λ₁ x := by
  intro x
  by_cases hlx : l = x
  · subst hlx; exact MirrorsAt.snoc_new htag (by simp [hacc]) hval hΛ₁
  · exact ((hM x).congr (hrest x hlx)).snoc_irrel (fun _ => by simp [hacc, hlx])

/-- (L), by induction on the run. -/
theorem inv_log {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : LogMirrors (events τ) C.txs := by
  refine Run.reverseRecOn (motive := fun τ C => LogMirrors (events τ) C.txs)
    (by intro i t Λ Ê hi; simp [initConfig] at hi) ?_ h
  intro ls C ℓ C' hrun hM hstep
  have hD := inv_distinct hrun
  have hA := (inv_bbt hrun).1
  cases hstep with
  | @ctx _ i _ _ _ _ hh =>
    cases hh with
    | @begin C i e α hi _ =>
      -- Begin: Λ := ∅, and the fresh tag has no old events
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, -⟩ := hv
        intro x
        refine ⟨fun _ a ha htag => ?_, fun o c a hΛ _ => by simp [Log.empty] at hΛ⟩
        rcases List.mem_append.mp ha with ha | ha
        · exact absurd (htag ▸ hA a ha) (Nat.lt_irrefl _)
        · rw [List.mem_singleton.mp ha]; rfl
      · intro x
        exact (hM k t Λ Ê hk x).snoc_irrel (fun _ => rfl)
    | @getLog C i t₀ Λ₀ Ê₀ l o v α hi hl _ =>
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      by_cases hki : k = i
      · subst hki; rw [hi] at hk; obtain ⟨rfl, rfl, rfl⟩ := hk
        exact mirrors_access (hM k t₀ Λ₀ Ê₀ hi) rfl (fun _ => rfl) rfl hl (fun _ _ => rfl)
      · exact hM.snoc_other hD hi rfl hki hk
    | @getMem C i t₀ Λ₀ Ê₀ l v α hi hl _ _ =>
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        exact mirrors_access (o := v) (hM i t₀ Λ₀ Ê₀ hi) rfl (fun _ => rfl) rfl
          (by simp [update]) (fun x hlx => update_other Λ₀ l x _ hlx)
      · exact hM.snoc_other hD hi rfl hki hk
    | @setLog C i t₀ Λ₀ Ê₀ l o c v α hi _ _ =>
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        exact mirrors_access (o := o) (hM i t₀ Λ₀ Ê₀ hi) rfl (fun _ => rfl) rfl
          (by simp [update]) (fun x hlx => update_other Λ₀ l x _ hlx)
      · exact hM.snoc_other hD hi rfl hki hk
    | @setMem C i t₀ Λ₀ Ê₀ l u v α hi _ _ _ =>
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        exact mirrors_access (o := u) (hM i t₀ Λ₀ Ê₀ hi) rfl (fun _ => rfl) rfl
          (by simp [update]) (fun x hlx => update_other Λ₀ l x _ hlx)
      · exact hM.snoc_other hD hi rfl hki hk
    | @commit C i t₀ Λ₀ Ê₀ α hi _ _ =>
      intro k t Λ Ê hk
      simp only [events_snoc_ev]
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · cases hv
      · exact hM.snoc_other hD hi rfl hki hk
    | adm _ =>
      simp only [events_snoc_adm]; exact hM
  | @kcasRetry i t₀ Λ₀ Ê₀ α _ hi _ _ =>
    intro k t Λ Ê hk
    simp only [events_snoc_ev]
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
    · cases hv
    · exact hM.snoc_other hD hi rfl hki hk
  | @retry i t₀ Λ₀ Ê₀ α _ hi _ =>
    intro k t Λ Ê hk
    simp only [events_snoc_ev]
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
    · cases hv
    · exact hM.snoc_other hD hi rfl hki hk

/-! ## From (L) to Int -/

theorem OccursBefore.mem {es : List Event} {a b : Event} (h : OccursBefore es a b) :
    a ∈ es ∧ b ∈ es := by
  sorry

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
  sorry

/-- `a = max_po P_x(e)` on the event list: the last access of `t` to `x`
before `e`. -/
def LastAccessBefore (es : List Event) (t : TxId) (x : Loc) (a e : Event) : Prop :=
  a ∈ es ∧ a.label.tx = t ∧ a.label.accesses x = true ∧ OccursBefore es a e ∧
    ∀ b ∈ es, b.label.tx = t → b.label.accesses x = true →
      OccursBefore es a b → ¬ OccursBefore es b e

theorem not_occursBefore_snoc {es : List Event} {e n : Event}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es) : ¬ OccursBefore (es ++ [n]) n e := by
  sorry

/-- Old reads: `P_x(e)` only looks backwards, and the new event is later. -/
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

/-- For the read just taken, the last access before it is the last access of
the old trace. -/
theorem lastAccess_of_new {es : List Event} {t : TxId} {x : Loc} {a n : Event}
    (hu : UniqueIds (es ++ [n])) (h : LastAccessBefore (es ++ [n]) t x a n) :
    LastAccess es t x a := by
  obtain ⟨hmem, htag, hacc, hbef, hmax⟩ := h
  have hain : a ∈ es := by
    rcases List.mem_append.mp hmem with h' | h'
    · exact h'
    · rw [List.mem_singleton.mp h'] at hbef; exact absurd hbef (OccursBefore.irrefl hu)
  refine ⟨hain, htag, hacc, fun b hb hbtag hbacc hob => ?_⟩
  exact hmax b (List.mem_append.mpr (Or.inl hb)) hbtag hbacc
    (OccursBefore.snoc_mono hob) (OccursBefore.snoc_last hb)

/-- Int on the events of a run, by induction: `Int(τ) → Int(τ · a)`. -/
theorem inv_int {E₀ : ThreadMap} {τ : Trace} {C : Config} (h : Run (initConfig E₀) τ C) :
    ∀ (x n : Nat) (t : TxId) (e a : Event),
      e ∈ events τ → e.label = .get x n t →
      LastAccessBefore (events τ) t x a e → a.label.accessVal = some n := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ (x n : Nat) (t : TxId) (e a : Event),
        e ∈ events τ → e.label = .get x n t →
        LastAccessBefore (events τ) t x a e → a.label.accessVal = some n)
    (by intro x n t e a he _ _; simp [events] at he) ?_ h
  intro ls C ℓ C' hrun ih hstep
  have hu : UniqueIds (events (ls ++ [ℓ])) := (inv_ids (hrun.snoc hstep)).2
  cases ℓ with
  | adm =>
    intro x nn t e a he hlab hlast
    rw [events_snoc_adm] at he hlast
    exact ih x nn t e a he hlab hlast
  | ev m =>
    intro x nn t e a he hlab hlast
    rw [events_snoc_ev] at he hlast hu
    rcases List.mem_append.mp he with he | he
    · -- an old read: nothing changes for it
      exact ih x nn t e a he hlab (lastAccessBefore_of_snoc hu he hlast)
    · -- the read just taken
      rw [List.mem_singleton.mp he] at hlab hlast
      have hlastacc := lastAccess_of_new hu hlast
      cases hstep with
      | ctx _ hh =>
        cases hh with
        | @getLog C i t₀ Λ₀ Ê₀ l o v α hi hl _ =>
          -- Get-Log returns the log's current value, the latest access by (L)
          cases hlab
          exact ((inv_log hrun) _ _ _ _ hi _).2 _ _ a hl hlastacc
        | @getMem C i t₀ Λ₀ Ê₀ l v α hi hl _ _ =>
          -- P_x ≠ ∅, so t touched l; by (L) Get-Mem could not have fired
          cases hlab
          have := ((inv_log hrun) _ _ _ _ hi _).1 hl a hlastacc.1 hlastacc.2.1
          rw [hlastacc.2.2.1] at this; cases this
        | begin _ _ => cases hlab
        | setLog _ _ _ => cases hlab
        | setMem _ _ _ _ => cases hlab
        | commit _ _ _ => cases hlab
      | kcasRetry _ _ _ _ => cases hlab
      | retry _ _ _ => cases hlab

/-- `H ⊨ Int` for every history of a run. Int never reads `ar`, so this holds
for every `H` with `HistoryOf τ H`, in particular the witness. -/
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

/-- The main theorem, without Ext: some history of the run satisfies Int. -/
theorem historyOf_int {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (h : Run (initConfig E₀) τ C') : ∃ H, HistoryOf τ H ∧ H.Int := by
  obtain ⟨H, hH⟩ := historyOf_exists h
  exact ⟨H, hH, int_of_run h hH⟩

end Optimistic
