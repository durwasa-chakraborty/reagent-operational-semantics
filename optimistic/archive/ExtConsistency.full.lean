/-
  prompt.org, entry "Proving External Consistency", part (a).

  Ext_c for the witness history: Lemma 1 (External), Lemma 2 (expected value
  is kept), Lemma 3 (current value), Lemma 4 (store is the commit order), then
  the five steps of the proof. (Closed) is proved from Lemma N (HistoryOf).
-/
import Optimistic.IntConsistency

namespace Optimistic

open Reagent (Loc TxId ThId ThreadMap Expr Store update update_other)

/-! ## Statement -/

/-- `T ⊢ Read(x, n)`: a `get(x, n)` with `po⁻¹(e) ∩ HEvent_x = ∅`. -/
def Transaction.ReadsExt (T : Transaction) (x : Loc) (n : Nat) : Prop :=
  ∃ e : Subtype T.E, (∃ t, e.val.label = .get x n t) ∧ ¬ ∃ a, T.PriorAccess x a e

/-- `T ⊢ Write(x, n)`: the `po`-last `set` on `x` in `T` writes `n`. -/
def Transaction.WritesVal (T : Transaction) (x : Loc) (n : Nat) : Prop :=
  ∃ a : Subtype T.E, (∃ t, a.val.label = .set x n t) ∧
    ∀ b : Subtype T.E, (∃ t w, b.val.label = .set x w t) → ¬ T.po a b

/-- `S ∈ W_x(T)`. -/
def History.InW (H : History) (x : Loc) (T S : Transaction) : Prop :=
  H.txs S ∧ S.status = .Committed ∧ S ≠ T ∧ H.ar S T ∧ ∃ v, S.WritesVal x v

/-- `S = max_AR W_x(T)`. -/
def History.MaxW (H : History) (x : Loc) (T S : Transaction) : Prop :=
  H.InW x T S ∧ ∀ U, H.InW x T U → U = S ∨ H.ar U S

/-- `Ext_c`: Cerone's Ext with `VIS = AR`, for committed readers. -/
def History.ExtC (H : History) : Prop :=
  ∀ T, H.txs T → T.status = .Committed → ∀ x n, T.ReadsExt x n →
    ((¬ ∃ S, H.InW x T S) ∧ n = Store.init_store x)
    ∨ ∃ S, H.MaxW x T S ∧ S.WritesVal x n

/-! ## (Closed) -/

/-- `a ≺ b` in `es ++ [n]`: already in `es`, or `b` is the new event. -/
theorem OccursBefore.snoc_cases {es : List Event} {a b n : Event}
    (h : OccursBefore (es ++ [n]) a b) : OccursBefore es a b ∨ (b = n ∧ a ∈ es) := by
  obtain ⟨p, m, s, hs⟩ := h.split
  rcases List.eq_nil_or_concat s with rfl | ⟨s', x, rfl⟩
  · obtain ⟨hes, hn⟩ := List.append_inj' (s₁ := es) (s₂ := p ++ [a] ++ m) (t₁ := [n]) (t₂ := [b])
      (by rw [hs]; simp) rfl
    refine Or.inr ⟨(List.singleton_inj.mp hn).symm, ?_⟩
    rw [hes]; simp
  · obtain ⟨hes, -⟩ := List.append_inj' (s₁ := es) (s₂ := p ++ [a] ++ m ++ [b] ++ s') (t₁ := [n])
      (t₂ := [x]) (by rw [hs]; simp) rfl
    rw [hes]; exact Or.inl (OccursBefore.of_split _ _ _ _ _)

theorem OccursBefore.mem_left {es : List Event} {a b : Event}
    (h : OccursBefore es a b) : a ∈ es := by
  obtain ⟨p, m, s, rfl⟩ := h.split
  simp

/-- (Closed): after `t` commits or retries, no event is tagged `t`.
Lemma N at the step that emits `b`, by induction on the run. -/
theorem closed_after_term {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {t : TxId} {a b : Event}
    (ha : Terminates (events τ) t a) (hab : OccursBefore (events τ) a b) :
    b.label.tx ≠ t := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t a b, Terminates (events τ) t a → OccursBefore (events τ) a b → b.label.tx ≠ t)
    (by intro t a b ha; simp [events, Terminates] at ha) ?_ h t a b ha hab
  intro ls C ℓ C' hrun ih hstep
  cases ℓ with
  | adm => simp only [events_snoc_adm]; exact ih
  | ev n =>
    simp only [events_snoc_ev]
    intro t a b ha hab
    rcases hab.snoc_cases with hab | ⟨rfl, ha'⟩
    · exact ih t a b ⟨hab.mem_left, ha.2⟩ hab
    · -- `b` is the new event and `t ∈ Term(ls)`: Lemma N
      intro heq
      exact tag_not_term hrun hstep a (by rw [heq]; exact ⟨ha', ha.2⟩)

/-! ## Lemma 1 (External) -/

/-- (←) of Lemma 1, by induction on the run. -/
theorem inv_external_back {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ i t Λ Ê, C.txs i = some (t, Λ, Ê) → ∀ x, NoAccess (events τ) t x → Λ x = none := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ i t Λ Ê, C.txs i = some (t, Λ, Ê) → ∀ x, NoAccess (events τ) t x → Λ x = none)
    (by intro i t Λ Ê hi; simp [initConfig] at hi) ?_ h
  intro ls C ℓ C' _ ih hstep
  -- an access-free trace stays access-free on its prefix
  have hpre : ∀ (n : Event) t x, NoAccess (events ls ++ [n]) t x → NoAccess (events ls) t x :=
    fun n t x hna a ha => hna a (List.mem_append.mpr (Or.inl ha))
  cases hstep with
  | @ctx _ i _ _ _ _ hh =>
    cases hh with
    | begin _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, -⟩ := hv; rfl
      · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | getLog _ _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | @getMem C i t₀ Λ₀ Ê₀ l v α hi _ _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · -- the new event is an access to x tagged t
          subst hlx
          have := hna _ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
          simp [Label.accesses] at this
        · rw [update_other Λ₀ l x _ hlx]
          exact ih i t₀ Λ₀ Ê₀ hi x (hpre _ _ _ hna)
      · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | @setLog C i t₀ Λ₀ Ê₀ l o c v α hi _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · subst hlx
          have := hna _ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
          simp [Label.accesses] at this
        · rw [update_other Λ₀ l x _ hlx]
          exact ih i t₀ Λ₀ Ê₀ hi x (hpre _ _ _ hna)
      · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | @setMem C i t₀ Λ₀ Ê₀ l u v α hi _ _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · subst hlx
          have := hna _ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
          simp [Label.accesses] at this
        · rw [update_other Λ₀ l x _ hlx]
          exact ih i t₀ Λ₀ Ê₀ hi x (hpre _ _ _ hna)
      · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | commit _ _ _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_ev] at hna
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · cases hv
      · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
    | adm _ =>
      intro k t Λ Ê hk x hna
      simp only [events_snoc_adm] at hna
      exact ih k t Λ Ê hk x hna
  | kcasRetry _ _ _ _ =>
    intro k t Λ Ê hk x hna
    simp only [events_snoc_ev] at hna
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
    · cases hv
    · exact ih k t Λ Ê hk x (hpre _ _ _ hna)
  | retry _ _ _ =>
    intro k t Λ Ê hk x hna
    simp only [events_snoc_ev] at hna
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
    · cases hv
    · exact ih k t Λ Ê hk x (hpre _ _ _ hna)

/-- Lemma 1 (External): `Λ(x) = ⊥ ↔ τ has no access to x tagged t`.
(→) is the first half of (L), `inv_log`; (←) is `inv_external_back`. -/
theorem inv_external {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) {i : ThId} {t : TxId} {Λ : Log} {Ê : Expr}
    (hi : C.txs i = some (t, Λ, Ê)) (x : Loc) :
    Λ x = none ↔ NoAccess (events τ) t x :=
  ⟨fun hx => ((inv_log h) i t Λ Ê hi x).1 hx, inv_external_back h i t Λ Ê hi x⟩

/-! ## Lemma 2 (expected value is kept) -/

/-- Lemma 2, by induction on the steps from `C` to `C''`. Stated for every
thread running `t`, not only `i`: the steps in between are taken by any
thread, and only (D) says which one runs `t`. `t < nextTx` is carried so that
a later `begin` cannot mint `t` again. -/
theorem expected_kept {C C'' : Config} {w : Trace} (hw : Run C w C'')
    {t : TxId} {x : Loc} {o : Nat} (hlt : t < C.nextTx)
    (h0 : ∀ k Λ Ê, C.txs k = some (t, Λ, Ê) → ∃ c, Λ x = some (o, c)) :
    t < C''.nextTx ∧ ∀ k Λ Ê, C''.txs k = some (t, Λ, Ê) → ∃ c, Λ x = some (o, c) := by
  refine Run.reverseRecOn (C₀ := C) (motive := fun _ C'' =>
      t < C''.nextTx ∧ ∀ k Λ Ê, C''.txs k = some (t, Λ, Ê) → ∃ c, Λ x = some (o, c))
    ⟨hlt, h0⟩ ?_ hw
  intro ls C ℓ C' _ ⟨ihlt, ih⟩ hstep
  cases hstep with
  | @ctx _ i _ _ _ _ hh =>
    cases hh with
    | begin _ _ =>
      refine ⟨Nat.lt_succ_of_lt ihlt, fun k Λ Ê hk => ?_⟩
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · -- the new tag is `nextTx`, which is above `t`
        obtain ⟨rfl, -, -⟩ := hv
        exact absurd ihlt (Nat.lt_irrefl _)
      · exact ih k Λ Ê hk
    | getLog _ _ _ => exact ⟨ihlt, ih⟩
    | @getMem C i t₀ Λ₀ Ê₀ l v α hi hl _ _ =>
      refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        obtain ⟨c, hc⟩ := ih i Λ₀ Ê₀ hi
        -- Get-Mem needs `Λ(l) = ⊥`, so it does not fire on `x`
        have hlx : l ≠ x := by rintro rfl; rw [hl] at hc; cases hc
        exact ⟨c, by rw [update_other Λ₀ l x _ hlx]; exact hc⟩
      · exact ih k Λ Ê hk
    | @setLog C i t₀ Λ₀ Ê₀ l o' c' v α hi hl _ =>
      refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        obtain ⟨c, hc⟩ := ih i Λ₀ Ê₀ hi
        by_cases hlx : l = x
        · -- Set-Log replaces `(o, c)` by `(o, v)`
          subst hlx
          rw [hl] at hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          exact ⟨v, by simp [update]⟩
        · exact ⟨c, by rw [update_other Λ₀ l x _ hlx]; exact hc⟩
      · exact ih k Λ Ê hk
    | @setMem C i t₀ Λ₀ Ê₀ l u v α hi hl _ _ =>
      refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        obtain ⟨c, hc⟩ := ih i Λ₀ Ê₀ hi
        have hlx : l ≠ x := by rintro rfl; rw [hl] at hc; cases hc
        exact ⟨c, by rw [update_other Λ₀ l x _ hlx]; exact hc⟩
      · exact ih k Λ Ê hk
    | commit _ _ _ =>
      refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · cases hv
      · exact ih k Λ Ê hk
    | adm _ => exact ⟨ihlt, ih⟩
  | kcasRetry _ _ _ _ =>
    refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
    · cases hv
    · exact ih k Λ Ê hk
  | retry _ _ _ =>
    refine ⟨ihlt, fun k Λ Ê hk => ?_⟩
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
    · cases hv
    · exact ih k Λ Ê hk

/-! ## Lemma 3 (current value) -/

/-- `t` has a `set` on `x`. -/
def HasSet (es : List Event) (t : TxId) (x : Loc) : Prop :=
  ∃ a ∈ es, ∃ v, a.label = .set x v t

/-- The `po`-last `set` on `x` tagged `t` writes `v`. -/
def LastSetVal (es : List Event) (t : TxId) (x : Loc) (v : Nat) : Prop :=
  ∃ a ∈ es, a.label = .set x v t ∧
    ∀ b ∈ es, (∃ w, b.label = .set x w t) → ¬ OccursBefore es a b

theorem HasSet.snoc {es : List Event} {t : TxId} {x : Loc} {n : Event}
    (h : HasSet es t x) : HasSet (es ++ [n]) t x := by
  obtain ⟨a, ha, v, hl⟩ := h
  exact ⟨a, List.mem_append_left _ ha, v, hl⟩

theorem HasSet.of_snoc {es : List Event} {t : TxId} {x : Loc} {n : Event}
    (h : HasSet (es ++ [n]) t x) (hn : ∀ w, n.label ≠ .set x w t) : HasSet es t x := by
  obtain ⟨a, ha, v, hl⟩ := h
  rcases List.mem_append.mp ha with ha | ha
  · exact ⟨a, ha, v, hl⟩
  · rw [List.mem_singleton.mp ha] at hl; exact absurd hl (hn v)

/-- An event that is not a `set` on `x` tagged `t` keeps the last `set`. -/
theorem LastSetVal.snoc {es : List Event} {t : TxId} {x : Loc} {v : Nat} {n : Event}
    (hu : UniqueIds (es ++ [n])) (h : LastSetVal es t x v)
    (hn : ∀ w, n.label ≠ .set x w t) : LastSetVal (es ++ [n]) t x v := by
  obtain ⟨a, ha, hl, hmax⟩ := h
  refine ⟨a, List.mem_append_left _ ha, hl, fun b hb hbs hab => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact hmax b hb hbs (OccursBefore.restrict_append hu ha hb hab)
  · rw [List.mem_singleton.mp hb] at hbs
    obtain ⟨w, hw⟩ := hbs
    exact hn w hw

/-- A new `set` is the last one. -/
theorem LastSetVal.new {es : List Event} {t : TxId} {x : Loc} {v : Nat} {n : Event}
    (hu : UniqueIds (es ++ [n])) (hn : n.label = .set x v t) :
    LastSetVal (es ++ [n]) t x v := by
  refine ⟨n, List.mem_append_right _ (List.mem_singleton_self _), hn, fun b hb _ hnb => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact not_occursBefore_snoc hu hb hnb
  · rw [List.mem_singleton.mp hb] at hnb; exact OccursBefore.irrefl hu hnb

/-- Lemma 3 at one location. -/
def CurVal (es : List Event) (t : TxId) (Λ : Log) (x : Loc) : Prop :=
  ∀ o c, Λ x = some (o, c) → (HasSet es t x → LastSetVal es t x c) ∧ (¬ HasSet es t x → c = o)

/-- An event that is not a `set` on `x` tagged `t` changes nothing. -/
theorem CurVal.snoc_irrel {es : List Event} {t : TxId} {Λ : Log} {x : Loc} {n : Event}
    (hu : UniqueIds (es ++ [n])) (h : CurVal es t Λ x) (hn : ∀ w, n.label ≠ .set x w t) :
    CurVal (es ++ [n]) t Λ x := by
  intro o c hx
  obtain ⟨h1, h2⟩ := h o c hx
  exact ⟨fun hs => (h1 (hs.of_snoc hn)).snoc hu hn, fun hs => h2 (fun hs' => hs hs'.snoc)⟩

/-- Lemma 3 (current value), by induction on the run. -/
theorem inv_cur {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ i t Λ Ê, C.txs i = some (t, Λ, Ê) → ∀ x, CurVal (events τ) t Λ x := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ i t Λ Ê, C.txs i = some (t, Λ, Ê) → ∀ x, CurVal (events τ) t Λ x)
    (by intro i t Λ Ê hi; simp [initConfig] at hi) ?_ h
  intro ls C ℓ C' hrun ih hstep
  have hD := inv_distinct hrun
  have hu : UniqueIds (events (ls ++ [ℓ])) := (inv_ids (hrun.snoc hstep)).2
  -- a step by thread `i` running `t₀`, seen by another live thread: by (D) a different tag
  have hother : ∀ (n : Event) i t₀ Λ₀ Ê₀ k t Λ Ê, C.txs i = some (t₀, Λ₀, Ê₀) →
      n.label.tx = t₀ → k ≠ i → C.txs k = some (t, Λ, Ê) →
      UniqueIds (events ls ++ [n]) → ∀ x, CurVal (events ls ++ [n]) t Λ x := by
    intro n i t₀ Λ₀ Ê₀ k t Λ Ê hi htag hki hk hu' x
    have hne : t₀ ≠ t := by
      intro heq; subst heq; exact hki (hD k i t₀ Λ Λ₀ Ê Ê₀ hk hi)
    refine (ih k t Λ Ê hk x).snoc_irrel hu' (fun w hw => hne ?_)
    rw [← htag, hw]; rfl
  cases hstep with
  | @ctx _ i _ _ _ _ hh =>
    cases hh with
    | begin _ _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
      · obtain ⟨rfl, rfl, -⟩ := hv
        intro o c hx; simp [Log.empty] at hx
      · exact (ih k t Λ Ê hk x).snoc_irrel hu (fun w hw => by cases hw)
    | @getLog C i t₀ Λ₀ Ê₀ l o v α hi hl _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      by_cases hki : k = i
      · subst hki; rw [hi] at hk; obtain ⟨rfl, rfl, rfl⟩ := hk
        exact (ih k t₀ Λ₀ Ê₀ hi x).snoc_irrel hu (fun w hw => by cases hw)
      · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
    | @getMem C i t₀ Λ₀ Ê₀ l v α hi hl _ _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · -- Get-Mem creates `(v, v)`, and `t` has no earlier access to `x` (Lemma 1)
          subst hlx
          intro o c hx
          simp only [update, if_true, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          refine ⟨fun hs => absurd hs ?_, fun _ => rfl⟩
          intro hs
          obtain ⟨a, ha, w, hw⟩ := hs.of_snoc (fun w hw => by cases hw)
          have := ((inv_external hrun hi l).mp hl) a ha (by rw [hw]; rfl)
          rw [hw] at this; simp [Label.accesses] at this
        · refine ((ih i t₀ Λ₀ Ê₀ hi x).snoc_irrel hu (fun w hw => by cases hw)) |> fun h' => ?_
          intro o c hx
          rw [update_other Λ₀ l x _ hlx] at hx
          exact h' o c hx
      · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
    | @setLog C i t₀ Λ₀ Ê₀ l o c v α hi hl _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · -- Set-Log makes `c` the value of the new last `set`
          subst hlx
          intro o' c' hx
          simp only [update, if_true, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨fun _ => LastSetVal.new hu rfl,
            fun hs => absurd ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _, rfl⟩ hs⟩
        · intro o' c' hx
          rw [update_other Λ₀ l x _ hlx] at hx
          exact (ih i t₀ Λ₀ Ê₀ hi x).snoc_irrel hu
            (fun w hw => by simp at hw; exact hlx hw.1) o' c' hx
      · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
    | @setMem C i t₀ Λ₀ Ê₀ l u v α hi hl _ _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hv
        by_cases hlx : l = x
        · -- Set-Mem creates `(u, v)` with the new `set` the last one
          subst hlx
          intro o' c' hx
          simp only [update, if_true, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨fun _ => LastSetVal.new hu rfl,
            fun hs => absurd ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _, rfl⟩ hs⟩
        · intro o' c' hx
          rw [update_other Λ₀ l x _ hlx] at hx
          exact (ih i t₀ Λ₀ Ê₀ hi x).snoc_irrel hu
            (fun w hw => by simp at hw; exact hlx hw.1) o' c' hx
      · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
    | @commit C i t₀ Λ₀ Ê₀ α hi _ _ =>
      intro k t Λ Ê hk x
      simp only [events_snoc_ev] at hu ⊢
      rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
      · cases hv
      · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
    | adm _ =>
      simp only [events_snoc_adm]; exact ih
  | @kcasRetry i t₀ Λ₀ Ê₀ α _ hi _ _ =>
    intro k t Λ Ê hk x
    simp only [events_snoc_ev] at hu ⊢
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
    · cases hv
    · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x
  | @retry i t₀ Λ₀ Ê₀ α _ hi _ =>
    intro k t Λ Ê hk x
    simp only [events_snoc_ev] at hu ⊢
    rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
    · cases hv
    · exact hother _ i t₀ Λ₀ Ê₀ k t Λ Ê hi rfl hki hk hu x

/-! ## Lemma 4 (store is the commit order) -/

/-- `c` is the commit event of `t`. -/
def CommitEv (es : List Event) (t : TxId) (c : Event) : Prop := c ∈ es ∧ c.label = .eend t

/-- Lemma 4 at one location: `σ(x)` is the last `set` value of the latest
committed writer of `x`, or `σ₀(x)` if there is none. -/
def StoreSpec (es : List Event) (σ : Store) (x : Loc) : Prop :=
  (∃ s c, CommitEv es s c ∧ HasSet es s x ∧ LastSetVal es s x (σ x) ∧
      ∀ s' c', CommitEv es s' c' → HasSet es s' x → c' = c ∨ OccursBefore es c' c)
  ∨ ((∀ s c, CommitEv es s c → ¬ HasSet es s x) ∧ σ x = Store.init_store x)

theorem CommitEv.snoc {es : List Event} {t : TxId} {c n : Event}
    (h : CommitEv es t c) : CommitEv (es ++ [n]) t c :=
  ⟨List.mem_append_left _ h.1, h.2⟩

theorem CommitEv.of_snoc {es : List Event} {t : TxId} {c n : Event}
    (h : CommitEv (es ++ [n]) t c) (hn : n.label ≠ .eend t) : CommitEv es t c := by
  rcases List.mem_append.mp h.1 with hc | hc
  · exact ⟨hc, h.2⟩
  · rw [List.mem_singleton.mp hc] at h; exact absurd h.2 hn

/-- A new event not tagged by any committed transaction leaves the committed
writers and their last `set`s alone. `hend` names the one transaction the new
event may commit; it must not write `x`. -/
theorem StoreSpec.snoc {es : List Event} {σ : Store} {x : Loc} {n : Event}
    (hu : UniqueIds (es ++ [n])) (h : StoreSpec es σ x)
    (htx : ∀ s c, CommitEv es s c → n.label.tx ≠ s)
    (hend : ∀ s, n.label = .eend s → ¬ HasSet (es ++ [n]) s x) :
    StoreSpec (es ++ [n]) σ x := by
  have hset : ∀ s c, CommitEv es s c → ∀ w, n.label ≠ .set x w s :=
    fun s c hc w hw => htx s c hc (by rw [hw]; rfl)
  -- a commit event of the longer trace is an old one, or one of a non-writer
  have hold : ∀ s c, CommitEv (es ++ [n]) s c → HasSet (es ++ [n]) s x → CommitEv es s c := by
    intro s c hc hs
    by_cases hn : n.label = .eend s
    · exact absurd hs (hend s hn)
    · exact hc.of_snoc hn
  rcases h with ⟨s, c, hc, hs, hv, hmax⟩ | ⟨hnone, hinit⟩
  · refine Or.inl ⟨s, c, hc.snoc, hs.snoc, hv.snoc hu (hset s c hc), fun s' c' hc' hs' => ?_⟩
    have hc'old := hold s' c' hc' hs'
    rcases hmax s' c' hc'old (hs'.of_snoc (hset s' c' hc'old)) with heq | hlt
    · exact Or.inl heq
    · exact Or.inr hlt.snoc_mono
  · refine Or.inr ⟨fun s c hc hs => ?_, hinit⟩
    have hcold := hold s c hc hs
    exact hnone s c hcold (hs.of_snoc (hset s c hcold))

/-- Commit of a writer `t₀` of `x`: it becomes the latest committed writer. -/
theorem StoreSpec.commit_writer {es : List Event} {σ' : Store} {x : Loc} {n : Event}
    {t₀ : TxId} (hu : UniqueIds (es ++ [n])) (hn : n.label = .eend t₀)
    (hs : HasSet es t₀ x) (hv : LastSetVal es t₀ x (σ' x)) :
    StoreSpec (es ++ [n]) σ' x := by
  refine Or.inl ⟨t₀, n, ⟨List.mem_append_right _ (List.mem_singleton_self _), hn⟩, hs.snoc,
    hv.snoc hu (fun w hw => by rw [hn] at hw; cases hw), fun s' c' hc' _ => ?_⟩
  rcases List.mem_append.mp hc'.1 with hc | hc
  · exact Or.inr (OccursBefore.snoc_last hc)
  · exact Or.inl (List.mem_singleton.mp hc)

/-- Lemma 4, by induction on the run. Only Commit changes `σ`. -/
theorem inv_store {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : ∀ x, StoreSpec (events τ) C.store x := by
  refine Run.reverseRecOn (motive := fun τ C => ∀ x, StoreSpec (events τ) C.store x)
    (fun x => Or.inr ⟨fun s c hc => by simp [events, CommitEv] at hc, rfl⟩) ?_ h
  intro ls C ℓ C' hrun ih hstep
  have hrun' := hrun.snoc hstep
  have hu : UniqueIds (events (ls ++ [ℓ])) := (inv_ids hrun').2
  -- (Closed): the new event is not tagged by a transaction already committed
  have htx : ∀ n : Event, ℓ = .ev n → ∀ s c, CommitEv (events ls) s c → n.label.tx ≠ s := by
    intro n hℓ s c hc
    subst hℓ
    have hc' : CommitEv (events (ls ++ [.ev n])) s c := by
      rw [events_snoc_ev]; exact hc.snoc
    refine closed_after_term hrun' ⟨hc'.1, Or.inl hc'.2⟩ ?_
    rw [events_snoc_ev]; exact OccursBefore.snoc_last hc.1
  cases hstep with
  | @ctx _ i _ _ _ _ hh =>
    cases hh with
    | begin _ _ =>
      intro x; simp only [events_snoc_ev] at hu ⊢
      exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
    | getLog _ _ _ =>
      intro x; simp only [events_snoc_ev] at hu ⊢
      exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
    | getMem _ _ _ _ =>
      intro x; simp only [events_snoc_ev] at hu ⊢
      exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
    | setLog _ _ _ =>
      intro x; simp only [events_snoc_ev] at hu ⊢
      exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
    | setMem _ _ _ _ =>
      intro x; simp only [events_snoc_ev] at hu ⊢
      exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
    | @commit C i t₀ Λ₀ Ê₀ α hi hok _ =>
      intro x
      have htx' := htx _ rfl
      simp only [events_snoc_ev] at hu ⊢
      -- `t₀` does not write `x` in the longer trace if it does not in the old one
      have hns : ¬ HasSet (events ls) t₀ x → ∀ s, Label.eend t₀ = .eend s →
          ¬ HasSet (events ls ++ [⟨α, .eend t₀⟩]) s x := by
        intro hn s hs hs'
        cases hs
        exact hn (hs'.of_snoc (fun w hw => by cases hw))
      cases hΛ : Λ₀ x with
      | none =>
        -- `Λ(x) = ⊥`: σ'(x) = σ(x), and `t₀` has no access to `x` (Lemma 1)
        have hσ : Log.apply C.store Λ₀ x = C.store x := by simp [Log.apply, hΛ]
        show StoreSpec _ (Log.apply C.store Λ₀) x
        have hnoset : ¬ HasSet (events ls) t₀ x := by
          rintro ⟨a, ha, w, hw⟩
          have := ((inv_external hrun hi x).mp hΛ) a ha (by rw [hw]; rfl)
          rw [hw] at this; simp [Label.accesses] at this
        have := (ih x).snoc hu htx' (hns hnoset)
        unfold StoreSpec at this ⊢; rw [hσ]; exact this
      | some oc =>
        obtain ⟨o, c⟩ := oc
        have hσ : Log.apply C.store Λ₀ x = c := by simp [Log.apply, hΛ]
        show StoreSpec _ (Log.apply C.store Λ₀) x
        obtain ⟨hw, hr⟩ := (inv_cur hrun) i t₀ Λ₀ Ê₀ hi x o c hΛ
        by_cases hs : HasSet (events ls) t₀ x
        · -- `t₀` set `x`: σ'(x) = c, its last `set` (Lemma 3)
          exact StoreSpec.commit_writer hu rfl hs (by rw [hσ]; exact hw hs)
        · -- `t₀` only read `x`: c = o (Lemma 3) and σ(x) = o (KCasOk)
          have hco : c = o := hr hs
          have hσ' : Log.apply C.store Λ₀ x = C.store x := by
            rw [hσ, hco]; exact (hok x o c hΛ).symm
          have := (ih x).snoc hu htx' (hns hs)
          unfold StoreSpec at this ⊢; rw [hσ']; exact this
    | adm _ =>
      intro x; simp only [events_snoc_adm]; exact ih x
  | kcasRetry _ _ _ _ =>
    intro x; simp only [events_snoc_ev] at hu ⊢
    exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)
  | retry _ _ _ =>
    intro x; simp only [events_snoc_ev] at hu ⊢
    exact (ih x).snoc hu (htx _ rfl) (fun s hs => by cases hs)

/-! ## Proof of Ext_c -/

theorem mem_events_split {e : Event} : ∀ {τ : Trace}, e ∈ events τ →
    ∃ τ₁ τ₂, τ = τ₁ ++ .ev e :: τ₂
  | [], h => by simp [events] at h
  | .ev f :: τ, h => by
    simp only [events, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], τ, rfl⟩
    · obtain ⟨τ₁, τ₂, rfl⟩ := mem_events_split h
      exact ⟨.ev f :: τ₁, τ₂, rfl⟩
  | .adm :: τ, h => by
    simp only [events] at h
    obtain ⟨τ₁, τ₂, rfl⟩ := mem_events_split h
    exact ⟨.adm :: τ₁, τ₂, rfl⟩

theorem Run.append {C₀ C₁ C₂ : Config} {τ σ : Trace}
    (h₁ : Run C₀ τ C₁) (h₂ : Run C₁ σ C₂) : Run C₀ (τ ++ σ) C₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

theorem OccursBefore.append_of_mem {A B : List Event} {a b : Event}
    (ha : a ∈ A) (hb : b ∈ B) : OccursBefore (A ++ B) a b := by
  obtain ⟨A₁, A₂, rfl⟩ := mem_split ha
  obtain ⟨B₁, B₂, rfl⟩ := mem_split hb
  have := OccursBefore.of_split A₁ (A₂ ++ B₁) B₂ a b
  simpa using this

/-- Whatever comes before `c` lies in the part before `c`. -/
theorem OccursBefore.mem_of_before {A R : List Event} {a c : Event}
    (hu : UniqueIds (A ++ c :: R)) (h : OccursBefore (A ++ c :: R) a c) : a ∈ A := by
  rcases List.mem_append.mp h.mem.1 with ha | ha
  · exact ha
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact absurd h (OccursBefore.irrefl hu)
    · have hca : OccursBefore (A ++ c :: R) c a := by
        have := OccursBefore.append_of_mem (A := A ++ [c]) (List.mem_append_right _
          (List.mem_singleton_self c)) ha
        simpa using this
      exact absurd (OccursBefore.trans hu h hca) (OccursBefore.irrefl hu)

theorem eend_of_committed {es : List Event} {t : TxId} (h : statusOf es t = .Committed) :
    ∃ c ∈ es, c.label = .eend t := by
  unfold statusOf at h
  split at h
  · next hany =>
    obtain ⟨c, hc, hcl⟩ := List.any_eq_true.mp hany
    exact ⟨c, hc, by simpa using hcl⟩
  · split at h <;> cases h

theorem committed_of_eend {es : List Event} {t : TxId} {c : Event}
    (hc : c ∈ es) (hcl : c.label = .eend t) : statusOf es t = .Committed := by
  have : es.any (fun e => e.label == .eend t) = true :=
    List.any_eq_true.mpr ⟨c, hc, by simp [hcl]⟩
  rw [statusOf, if_pos this]

theorem writesVal_of_lastSetVal {es : List Event} {s : TxId} {x : Loc} {v : Nat}
    (h : LastSetVal es s x v) : (transactionOf es s).WritesVal x v := by
  obtain ⟨a, ha, hl, hmax⟩ := h
  refine ⟨⟨a, ha, by rw [hl]; rfl, by rw [hl]; rfl⟩, ⟨s, hl⟩, fun b ⟨t, w, hb⟩ hab => ?_⟩
  have hbt : t = s := by have := b.property.2.1; rw [hb] at this; exact this
  subst hbt
  exact hmax b.val b.property.1 ⟨w, hb⟩ hab

theorem hasSet_of_writesVal {es : List Event} {s : TxId} {x : Loc} {v : Nat}
    (h : (transactionOf es s).WritesVal x v) : HasSet es s x := by
  obtain ⟨a, ⟨t, ha⟩, -⟩ := h
  have hat : t = s := by have := a.property.2.1; rw [ha] at this; exact this
  subst hat
  exact ⟨a.val, a.property.1, v, ha⟩

/-- Step 5: `W_x(T)` is the set of writers of `x` committed before `c`, and
the latest of them is `max_AR W_x(T)`. -/
theorem ext_step5 {es es_c R : List Event} {c : Event} {t : TxId} {σ : Store}
    {x : Loc} {n : Nat}
    (hes : es = es_c ++ c :: R) (hu : UniqueIds es)
    (hclosed : ∀ s a b, Terminates es s a → OccursBefore es a b → b.label.tx ≠ s)
    (htu : ∀ s a a', Terminates es s a → Terminates es s a' → a = a')
    (hc : c.label = .eend t) (hspec : StoreSpec es_c σ x) (hσ : σ x = n) :
    let H : History := ⟨txsOf es, finishOrder es⟩
    let T := transactionOf es t
    ((¬ ∃ S, H.InW x T S) ∧ n = Store.init_store x) ∨ ∃ S, H.MaxW x T S ∧ S.WritesVal x n := by
  intro H T
  have hcm : c ∈ es := by rw [hes]; simp
  have hTc : Terminates es t c := ⟨hcm, Or.inl hc⟩
  have hsub : ∀ {a}, a ∈ es_c → a ∈ es := fun ha => by rw [hes]; exact List.mem_append_left _ ha
  have hbefore : ∀ {a}, a ∈ es_c → OccursBefore es a c := fun ha => by
    rw [hes]; exact OccursBefore.append_of_mem ha (List.mem_cons_self ..)
  -- events of a transaction committed before `c` all lie before `c`
  have hinPre : ∀ s a b, CommitEv es_c s a → b ∈ es → b.label.tx = s → b ∈ es_c := by
    intro s a b ha hb hbs
    rw [hes] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hb
    · refine absurd hbs (hclosed s a b ⟨hsub ha.1, Or.inl ha.2⟩ ?_)
      rw [hes]; exact OccursBefore.append_of_mem ha.1 hb
  have hlast : ∀ s a v, CommitEv es_c s a → LastSetVal es_c s x v → LastSetVal es s x v := by
    rintro s a v ha ⟨w, hw, hwl, hmax⟩
    refine ⟨w, hsub hw, hwl, fun b hb hbs hwb => ?_⟩
    have hbtag : b.label.tx = s := by obtain ⟨w', hw'⟩ := hbs; rw [hw']; rfl
    have hb' := hinPre s a b ha hb hbtag
    rw [hes] at hwb hu
    exact hmax b hb' hbs (OccursBefore.restrict_append hu hw hb' hwb)
  have hhas : ∀ s a, CommitEv es_c s a → HasSet es s x → HasSet es_c s x := by
    rintro s a ha ⟨b, hb, w, hbl⟩
    exact ⟨b, hinPre s a b ha hb (by rw [hbl]; rfl), w, hbl⟩
  -- a committed `U` with `U →AR T` committed before `c`
  have hpre : ∀ u, (transactionOf es u).status = .Committed →
      finishOrder es (transactionOf es u) T → ∃ a, CommitEv es_c u a := by
    intro u hUc har
    obtain ⟨a, ha, hal⟩ := eend_of_committed hUc
    rcases har with ⟨a', b', ha', hb', hab⟩ | ⟨-, hnf⟩ | ⟨-, hnf, -⟩
    · have h1 : a' = a := htu u a' a ha' ⟨ha, Or.inl hal⟩
      have h2 : b' = c := htu t b' c hb' hTc
      subst h1; subst h2
      rw [hes] at hab hu
      exact ⟨a', OccursBefore.mem_of_before hu hab, hal⟩
    · exact absurd ⟨c, hTc⟩ hnf
    · exact absurd ⟨c, hTc⟩ hnf
  -- `T` itself did not commit before `c`
  have hnotT : ∀ a, ¬ CommitEv es_c t a := fun a ha =>
    hclosed t a c ⟨hsub ha.1, Or.inl ha.2⟩ (hbefore ha.1) (by rw [hc]; rfl)
  rcases hspec with ⟨s, a, ha, hsx, hv, hmax⟩ | ⟨hnone, hinit⟩
  · rw [hσ] at hv
    have hst : s ≠ t := fun h => hnotT a (h ▸ ha)
    refine Or.inr ⟨transactionOf es s, ⟨⟨⟨s, ⟨a, hsub ha.1, by rw [ha.2]; rfl⟩, rfl⟩,
      committed_of_eend (hsub ha.1) ha.2,
      fun h => hst (congrArg Transaction.txid h),
      Or.inl ⟨a, c, ⟨hsub ha.1, Or.inl ha.2⟩, hTc, hbefore ha.1⟩,
      ⟨n, writesVal_of_lastSetVal (hlast s a n ha hv)⟩⟩, ?_⟩,
      writesVal_of_lastSetVal (hlast s a n ha hv)⟩
    rintro U ⟨⟨u, -, rfl⟩, hUc, -, hUar, ⟨w, hUw⟩⟩
    obtain ⟨b, hb⟩ := hpre u hUc hUar
    rcases hmax u b hb (hhas u b hb (hasSet_of_writesVal hUw)) with rfl | hba
    · have : u = s := by have := hb.2.symm.trans ha.2; cases this; rfl
      exact Or.inl (by rw [this])
    · refine Or.inr (Or.inl ⟨b, a, ⟨hsub hb.1, Or.inl hb.2⟩, ⟨hsub ha.1, Or.inl ha.2⟩, ?_⟩)
      rw [hes]; exact OccursBefore.post _ hba
  · refine Or.inl ⟨?_, hσ ▸ hinit⟩
    rintro ⟨U, ⟨u, -, rfl⟩, hUc, -, hUar, ⟨w, hUw⟩⟩
    obtain ⟨b, hb⟩ := hpre u hUc hUar
    exact hnone u b hb (hhas u b hb (hasSet_of_writesVal hUw))

/-- `Ext_c` for the witness history, in the five steps of the paper proof. -/
theorem extC_witness {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : (witness τ).ExtC := by
  intro T hT hcom x n hread
  obtain ⟨t, -, rfl⟩ := hT
  obtain ⟨⟨ev, hevE⟩, ⟨t', hlab⟩, hnoprior⟩ := hread
  have het : ev.label.tx = t := hevE.2.1
  replace hlab : ev.label = .get x n t' := hlab
  have htt : t' = t := by rw [hlab] at het; exact het
  subst htt
  have hu := (inv_ids hrun).2
  -- split the run at `e`
  obtain ⟨τ₁, τ₂, hτ⟩ := mem_events_split hevE.1
  have hesplit : events τ = events τ₁ ++ ev :: events τ₂ := by
    rw [hτ, events_append]; rfl
  have hrun₀ := hrun
  rw [hτ] at hrun₀
  obtain ⟨Ce, hr1, hr2⟩ := Run.split hrun₀
  cases hr2 with
  | @cons _ _ Ce₁ _ _ hstepe hr3 =>
  have hr1e : Run (initConfig E₀) (τ₁ ++ [.ev ev]) Ce₁ := hr1.snoc hstepe
  -- `e` is external: no access to `x` tagged `t` before it
  have hna : NoAccess (events τ₁) t' x := by
    intro a ha hat
    cases hacc : a.label.accesses x with
    | false => rfl
    | true =>
      exfalso
      refine hnoprior ⟨⟨a, ?_, hat, isAccess_of_accesses hacc⟩, ?_, hacc⟩
      · rw [hesplit]; exact List.mem_append_left _ ha
      · show OccursBefore (events τ) a ev
        rw [hesplit]; exact OccursBefore.append_of_mem ha (List.mem_cons_self ..)
  -- Step 1: `e` was fired by Get-Mem, so `Λ(x) := (n, n)`
  have step1 : ∃ i Λ Ê, Ce₁.txs i = some (t', Λ, Ê) ∧ Λ x = some (n, n) := by
    generalize hev : ev = ev' at hstepe hlab
    cases hstepe with
    | @ctx _ i _ _ _ _ hh =>
      cases hh with
      | getLog hi hl _ =>
        cases hlab
        rw [(inv_external hr1 hi x).mpr hna] at hl; cases hl
      | @getMem _ _ _ Λ₀ Ê₀ _ _ _ hi _ _ _ =>
        cases hlab
        exact ⟨i, update Λ₀ x (some (n, n)), Ê₀, by simp [update], by simp [update]⟩
      | begin _ _ => cases hlab
      | setLog _ _ _ => cases hlab
      | setMem _ _ _ _ => cases hlab
      | commit _ _ _ => cases hlab
    | kcasRetry _ _ _ _ => cases hlab
    | retry _ _ _ => cases hlab
  obtain ⟨i, Λe, Êe, hie, hΛe⟩ := step1
  -- locate `t`'s commit `c` after `e` (it cannot come before, by (Closed))
  obtain ⟨c, hcm, hcl⟩ := eend_of_committed hcom
  have hc₂ : c ∈ events τ₂ := by
    have hcm' := hcm
    rw [hesplit] at hcm'
    rcases List.mem_append.mp hcm' with hc | hc
    · refine absurd het (closed_after_term hrun ⟨hcm, Or.inl hcl⟩ ?_)
      rw [hesplit]; exact OccursBefore.append_of_mem hc (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hc with rfl | hc
      · rw [hcl] at hlab; cases hlab
      · exact hc
  obtain ⟨τ₃, τ₄, hτ₂⟩ := mem_events_split hc₂
  rw [hτ₂] at hr3
  obtain ⟨Cc, hr4, hr5⟩ := Run.split hr3
  cases hr5 with
  | @cons _ _ Cc₁ _ _ hstepc _ =>
  -- Step 2: at commit, `t` still expects `n` (Lemma 2)
  have hlt : t' < Ce₁.nextTx := (inv_bbt hr1e).2.1 i t' Λe Êe hie
  have h0 : ∀ k Λ Ê, Ce₁.txs k = some (t', Λ, Ê) → ∃ c, Λ x = some (n, c) := by
    intro k Λ Ê hk
    have hki := inv_distinct hr1e k i t' Λ Λe Ê Êe hk hie
    subst hki; rw [hie] at hk; cases hk
    exact ⟨n, hΛe⟩
  have hkept := (expected_kept hr4 hlt h0).2
  -- Step 3: KCasOk at the commit gives `σ_c(x) = n`
  have step3 : Cc.store x = n := by
    generalize hcv : c = cv at hstepc hcl
    cases hstepc with
    | ctx _ hh =>
      cases hh with
      | commit hj hok _ =>
        cases hcl
        obtain ⟨c', hc'⟩ := hkept _ _ _ hj
        exact hok x n c' hc'
      | begin _ _ => cases hcl
      | getLog _ _ _ => cases hcl
      | getMem _ _ _ _ => cases hcl
      | setLog _ _ _ => cases hcl
      | setMem _ _ _ _ => cases hcl
    | kcasRetry _ _ _ _ => cases hcl
    | retry _ _ _ => cases hcl
  -- Step 4: memory is the latest committed writer (Lemma 4)
  have hrc : Run (initConfig E₀) ((τ₁ ++ [.ev ev]) ++ τ₃) Cc := hr1e.append hr4
  have step4 := inv_store hrc x
  -- Step 5: that writer is `max_AR W_x(T)`
  have hes : events τ = events ((τ₁ ++ [.ev ev]) ++ τ₃) ++ c :: events τ₄ := by
    rw [hτ, hτ₂]; simp [events_append, events]
  exact ext_step5 hes hu
    (fun s a b ha hab => closed_after_term hrun ha hab)
    (fun s a a' ha ha' => term_unique hrun ha ha') hcl step4 step3

end Optimistic
