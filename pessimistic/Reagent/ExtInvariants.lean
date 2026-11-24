/-
  Reagent — the operational invariants external consistency rests on.

  `Int` needed one fact about the store: a read sees what its own transaction
  last left there (`inv_store`).  `Ext` needs the complementary one — what a
  read sees when its transaction has *not* touched that location — and that is
  a fact about everybody else's transactions, so it needs the shape of the run:
  the lock serialises transactions into blocks, and a block's writes become
  visible exactly when it commits.
-/
import Reagent.IntConsistency

namespace Reagent

/-! ## While a transaction is live -/

/-- A live transaction has not ended yet.  Its own `end` is still in the future,
so nothing in the trace so far commits it. -/
theorem inv_live_open {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∀ e ∈ events τ, e.label ≠ .eend t := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∀ e ∈ events τ, e.label ≠ .eend t)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => intro t ht e he; rw [events_snoc_adm] at he; exact ih t ht e he
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro t' ht' e he
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih t' ht' e h'
    · have : e = ⟨α, Label.get l v t⟩ := by simpa using h'
      subst this; simp
  | @set σ i t E snap body n u l v α hfresh =>
    intro t' ht' e he
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · exact ih t' ht' e h'
    · have : e = ⟨α, Label.set l v t⟩ := by simpa using h'
      subst this; simp
  | @eend σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro t' ht' e he
    have hn : n = t' := Option.some.inj ht'
    subst hn
    rw [events_snoc_ev] at he
    rcases List.mem_append.mp he with h' | h'
    · intro hc
      have hlt := (inv_nextTx hrunls).1 e h'
      rw [hc] at hlt
      exact Nat.lt_irrefl _ hlt
    · have : e = ⟨α, Label.begin n⟩ := by simpa using h'
      subst this; simp

/-- The live transaction owns the tail of the trace: everything belonging to
anyone else already happened.  This is the lock, read off the trace — while `t`
holds it no other transaction can emit anything, so `t`'s events are a
contiguous block at the end. -/
theorem inv_live_last {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∀ a ∈ events τ, ∀ b ∈ events τ,
      a.label.tx ≠ t → b.label.tx = t → OccursBefore (events τ) a b := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∀ a ∈ events τ, ∀ b ∈ events τ,
        a.label.tx ≠ t → b.label.tx = t → OccursBefore (events τ) a b)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  have key : ∀ (lb : Label) (t : TxId), lb.tx = t →
      (∀ a ∈ events ls, ∀ b ∈ events ls, a.label.tx ≠ t → b.label.tx = t →
        OccursBefore (events ls) a b) →
      ∀ (α : EvId) a, a ∈ events ls ++ [(⟨α, lb⟩ : Event)] →
        ∀ b ∈ events ls ++ [(⟨α, lb⟩ : Event)], a.label.tx ≠ t → b.label.tx = t →
          OccursBefore (events ls ++ [⟨α, lb⟩]) a b := by
    intro lb t hlb ihl α a ha b hb hat hbt
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp hb with hb' | hb'
      · exact OccursBefore.snoc_mono (ihl a ha' b hb' hat hbt)
      · have : b = ⟨α, lb⟩ := by simpa using hb'
        subst this
        exact OccursBefore.snoc_last ha'
    · have hae : a = ⟨α, lb⟩ := by simpa using ha'
      subst hae
      exact absurd hlb hat
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc =>
    intro t ht a ha b hb hat hbt
    rw [events_snoc_adm] at ha hb ⊢
    exact ih t ht a ha b hb hat hbt
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro t' ht' a ha b hb hat hbt
    have htt : t = t' := Option.some.inj ht'
    subst htt
    rw [events_snoc_ev] at ha hb ⊢
    exact key (Label.get l v t) t rfl (ih t rfl) α a ha b hb hat hbt
  | @set σ i t E snap body n u l v α hfresh =>
    intro t' ht' a ha b hb hat hbt
    have htt : t = t' := Option.some.inj ht'
    subst htt
    rw [events_snoc_ev] at ha hb ⊢
    exact key (Label.set l v t) t rfl (ih t rfl) α a ha b hb hat hbt
  | @eend σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro t' ht' a ha b hb hat hbt
    have hn : n = t' := Option.some.inj ht'
    subst hn
    rw [events_snoc_ev] at ha hb ⊢
    -- every old event has a transaction id below `n`, so the only event tagged
    -- `n` is the `begin` just emitted
    have hold : ∀ c ∈ events ls, c.label.tx ≠ n := by
      intro c hc hcn
      have hlt := (inv_nextTx hrunls).1 c hc
      rw [hcn] at hlt
      exact Nat.lt_irrefl _ hlt
    rcases List.mem_append.mp hb with hb' | hb'
    · exact absurd hbt (hold b hb')
    · have hbe : b = ⟨α, Label.begin n⟩ := by simpa using hb'
      subst hbe
      rcases List.mem_append.mp ha with ha' | ha'
      · exact OccursBefore.snoc_last ha'
      · have : a = (⟨α, Label.begin n⟩ : Event) := by simpa using ha'
        subst this
        exact absurd rfl hat


/-! ## The live transaction's own writes -/

/-- `t` has written `x` somewhere in `es`. -/
def WroteTo (es : List Event) (t : TxId) (x : Loc) : Prop :=
  ∃ w ∈ es, ∃ v, w.label = .set x v t

/-- `w` is `t`'s last write to `x` in `es`. -/
def LastWriteOf (es : List Event) (t : TxId) (x : Loc) (w : Event) : Prop :=
  w ∈ es ∧ (∃ v, w.label = .set x v t) ∧
    ∀ b ∈ es, (∃ v, b.label = .set x v t) → ¬ OccursBefore es w b

theorem LastWriteOf.of_snoc {es : List Event} {t : TxId} {x : Loc} {w n : Event}
    (hn : ¬ ∃ v, n.label = .set x v t) (h : LastWriteOf (es ++ [n]) t x w) :
    LastWriteOf es t x w := by
  obtain ⟨hmem, hset, hmax⟩ := h
  have hwes : w ∈ es := by
    rcases List.mem_append.mp hmem with h' | h'
    · exact h'
    · exact absurd (List.mem_singleton.mp h' ▸ hset) hn
  refine ⟨hwes, hset, ?_⟩
  intro b hb hbset hob
  exact hmax b (List.mem_append.mpr (Or.inl hb)) hbset (OccursBefore.snoc_mono hob)

theorem LastWriteOf.snoc_of {es : List Event} {t : TxId} {x : Loc} {w n : Event}
    (hn : ¬ ∃ v, n.label = .set x v t) (hu : UniqueIds (es ++ [n]))
    (h : LastWriteOf es t x w) : LastWriteOf (es ++ [n]) t x w := by
  obtain ⟨hmem, hset, hmax⟩ := h
  refine ⟨List.mem_append.mpr (Or.inl hmem), hset, ?_⟩
  intro b hb hbset hob
  rcases List.mem_append.mp hb with h' | h'
  · exact hmax b h' hbset (OccursBefore.restrict_append hu hmem h' hob)
  · exact hn (List.mem_singleton.mp h' ▸ hbset)

/-- While `t` is live the store carries `t`'s own uncommitted work, and nothing
else: at a location `t` has written, the store holds the value of `t`'s last
write there; at a location `t` has not written, the store still agrees with the
snapshot taken when `t` began. -/
theorem inv_live_store {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∀ x : Loc,
      (∀ w, LastWriteOf (events τ) t x w → w.label.accessVal = some (C.store x))
      ∧ (¬ WroteTo (events τ) t x → C.store x = C.snapshot x) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∀ x : Loc,
        (∀ w, LastWriteOf (events τ) t x w → w.label.accessVal = some (C.store x))
        ∧ (¬ WroteTo (events τ) t x → C.store x = C.snapshot x))
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  have hu : UniqueIds (events (ls ++ [m])) := (inv_ids (hrunls.snoc hstep)).2
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc =>
    intro t ht x
    obtain ⟨h1, h2⟩ := ih t ht x
    rw [events_snoc_adm]
    exact ⟨h1, h2⟩
  | @eend σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro t' ht' x
    have htt : t = t' := Option.some.inj ht'
    subst htt
    rw [events_snoc_ev] at hu
    have hnot : ¬ ∃ w, (⟨α, Label.get l v t⟩ : Event).label = .set x w t := by simp
    obtain ⟨h1, h2⟩ := ih t rfl x
    refine ⟨fun w hw => ?_, fun hnw => ?_⟩
    · rw [events_snoc_ev] at hw
      exact h1 w (LastWriteOf.of_snoc hnot hw)
    · refine h2 (fun hc => hnw ?_)
      obtain ⟨w, hwm, hwv⟩ := hc
      rw [events_snoc_ev]
      exact ⟨w, List.mem_append.mpr (Or.inl hwm), hwv⟩
  | @set σ i t E snap body n u l v α hfresh =>
    intro t' ht' x
    have htt : t = t' := Option.some.inj ht'
    subst htt
    rw [events_snoc_ev] at hu
    by_cases hlx : l = x
    · subst hlx
      refine ⟨fun w hw => ?_, fun hnw => ?_⟩
      · rw [events_snoc_ev] at hw
        obtain ⟨hmem, hset, hmax⟩ := hw
        have hwe : w = ⟨α, Label.set l v t⟩ := by
          rcases List.mem_append.mp hmem with h' | h'
          · exact absurd (OccursBefore.snoc_last h')
              (hmax ⟨α, Label.set l v t⟩ (by simp) ⟨v, rfl⟩)
          · simpa using h'
        subst hwe
        simp [Label.accessVal, update]
      · exact absurd ⟨⟨α, Label.set l v t⟩, by rw [events_snoc_ev]; simp, v, rfl⟩ hnw
    · have hnot : ¬ ∃ w, (⟨α, Label.set l v t⟩ : Event).label = .set x w t := by
        rintro ⟨w, hc⟩
        simp at hc
        exact hlx hc.1
      obtain ⟨h1, h2⟩ := ih t rfl x
      have hstore : (update σ l v) x = σ x := by
        rw [update, if_neg (fun hc => hlx hc.symm)]
      refine ⟨fun w hw => ?_, fun hnw => ?_⟩
      · rw [events_snoc_ev] at hw
        show w.label.accessVal = some ((update σ l v) x)
        rw [hstore]
        exact h1 w (LastWriteOf.of_snoc hnot hw)
      · show (update σ l v) x = snap x
        rw [hstore]
        refine h2 (fun hc => hnw ?_)
        obtain ⟨w, hwm, hwv⟩ := hc
        rw [events_snoc_ev]
        exact ⟨w, List.mem_append.mpr (Or.inl hwm), hwv⟩
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro t' ht' x
    have hn : n = t' := Option.some.inj ht'
    subst hn
    rw [events_snoc_ev] at hu
    refine ⟨fun w hw => ?_, fun _ => rfl⟩
    exfalso
    rw [events_snoc_ev] at hw
    obtain ⟨hmem, ⟨v, hset⟩, -⟩ := hw
    rcases List.mem_append.mp hmem with h' | h'
    · have hlt := (inv_nextTx hrunls).1 w h'
      rw [hset] at hlt
      exact Nat.lt_irrefl _ hlt
    · have : w = (⟨α, Label.begin n⟩ : Event) := by simpa using h'
      subst this
      simp at hset


/-! ## Which writes are visible

A write becomes visible exactly when its transaction commits.  Until then the
store carries it but the *committed* value of the location is still whatever the
last committed writer left, and a `retry` throws the uncommitted work away
without ever making it visible. -/

/-- `w` is a write to `x` whose transaction commits somewhere in `es`. -/
def CommittedWrite (es : List Event) (x : Loc) (w : Event) : Prop :=
  w ∈ es ∧ ∃ v s, w.label = .set x v s ∧ ∃ c ∈ es, c.label = .eend s

/-- … and no committed write to `x` comes after it. -/
def LastCommittedWrite (es : List Event) (x : Loc) (w : Event) : Prop :=
  CommittedWrite es x w ∧ ∀ b, CommittedWrite es x b → ¬ OccursBefore es w b

/-- The committed value of `x` after `es`: what the last committed writer left,
or the initial store if nobody committed a write to `x`. -/
def CommittedVal (es : List Event) (x : Loc) (v : Nat) : Prop :=
  (∃ w, LastCommittedWrite es x w ∧ w.label.accessVal = some v)
  ∨ ((¬ ∃ w, CommittedWrite es x w) ∧ v = Store.init_store x)

theorem CommittedWrite.mono {es : List Event} {x : Loc} {w n : Event}
    (h : CommittedWrite es x w) : CommittedWrite (es ++ [n]) x w := by
  obtain ⟨hmem, v, s, hset, c, hc, hcl⟩ := h
  exact ⟨List.mem_append.mpr (Or.inl hmem), v, s, hset,
    c, List.mem_append.mpr (Or.inl hc), hcl⟩

/-- A step that neither writes `x` visibly nor commits anyone who did leaves the
committed value of `x` alone. -/
theorem CommittedVal.snoc {es : List Event} {x : Loc} {v : Nat} {n : Event}
    (hu : UniqueIds (es ++ [n]))
    (hn : ¬ CommittedWrite (es ++ [n]) x n)
    (hsame : ∀ b ∈ es, CommittedWrite (es ++ [n]) x b → CommittedWrite es x b)
    (h : CommittedVal es x v) : CommittedVal (es ++ [n]) x v := by
  have hback : ∀ b, CommittedWrite (es ++ [n]) x b → CommittedWrite es x b := by
    intro b hb
    rcases List.mem_append.mp hb.1 with h' | h'
    · exact hsame b h' hb
    · exact absurd (List.mem_singleton.mp h' ▸ hb) hn
  rcases h with ⟨w, ⟨hcw, hmax⟩, hval⟩ | ⟨hnone, hinit⟩
  · refine Or.inl ⟨w, ⟨hcw.mono, ?_⟩, hval⟩
    intro b hb hob
    exact hmax b (hback b hb)
      (OccursBefore.restrict_append hu hcw.1 (hback b hb).1 hob)
  · exact Or.inr ⟨fun ⟨w, hw⟩ => hnone ⟨w, hback w hw⟩, hinit⟩

/-- A finite list has a last element satisfying any predicate it satisfies at
all.  With `OccursBefore` total on members, "last" is "nothing satisfying `P`
comes after it". -/
theorem exists_last_of (P : Event → Prop) : ∀ (es : List Event), UniqueIds es →
    (∃ w ∈ es, P w) → ∃ w ∈ es, P w ∧ ∀ b ∈ es, P b → ¬ OccursBefore es w b := by
  refine listReverseInduction (motive := fun es => UniqueIds es →
      (∃ w ∈ es, P w) → ∃ w ∈ es, P w ∧ ∀ b ∈ es, P b → ¬ OccursBefore es w b)
    (by intro _ h; obtain ⟨w, hw, -⟩ := h; cases hw) ?_
  intro xs y ih hu h
  have huxs : UniqueIds xs := (List.pairwise_append.mp hu).1
  rcases Classical.em (P y) with hy | hy
  · refine ⟨y, by simp, hy, ?_⟩
    intro b hb _ hob
    rcases List.mem_append.mp hb with h' | h'
    · exact not_occursBefore_snoc hu h' hob
    · exact OccursBefore.irrefl hu (List.mem_singleton.mp h' ▸ hob)
  · have hxs : ∃ w ∈ xs, P w := by
      obtain ⟨w, hw, hpw⟩ := h
      rcases List.mem_append.mp hw with h' | h'
      · exact ⟨w, h', hpw⟩
      · exact absurd (List.mem_singleton.mp h' ▸ hpw) hy
    obtain ⟨w, hwm, hpw, hmax⟩ := ih huxs hxs
    refine ⟨w, List.mem_append.mpr (Or.inl hwm), hpw, ?_⟩
    intro b hb hpb hob
    rcases List.mem_append.mp hb with h' | h'
    · exact hmax b h' hpb (OccursBefore.restrict_append hu hwm h' hob)
    · exact hy (List.mem_singleton.mp h' ▸ hpb)


/-- The lock and the live transaction are held and released together.  `Begin`
tests only `λ`, so this is what says its `θ` was `⊥` too. -/
theorem inv_lock {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : C.activeThread = none ↔ C.activeTx = none := by
  refine Run.reverseRecOn (motive := fun _ C => C.activeThread = none ↔ C.activeTx = none)
    (by simp [initConfig]) ?_ h
  intro ls C m C' _ ih hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => exact ih
  | @get σ i t E snap body n u l v α hfresh hv => simp
  | @set σ i t E snap body n u l v α hfresh => simp
  | @eend σ i t E snap body n u α hfresh => simp
  | @retry σ i t E snap body n u α hfresh => simp
  | @begin σ θ E snap body n u i eb α hfresh => simp

/-- **The committed store.**  Between transactions the store *is* the committed
value of every location; inside a transaction the snapshot is.  `Retry` restores
the store from the snapshot, which is why an abandoned attempt never becomes
visible, and `End` is the one step that moves a transaction's writes across. -/
theorem inv_committed {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : ∀ x : Loc,
      (C.activeTx = none → CommittedVal (events τ) x (C.store x)) ∧
      (∀ t, C.activeTx = some t → CommittedVal (events τ) x (C.snapshot x)) := by
  refine Run.reverseRecOn (motive := fun τ C => ∀ x : Loc,
      (C.activeTx = none → CommittedVal (events τ) x (C.store x)) ∧
      (∀ t, C.activeTx = some t → CommittedVal (events τ) x (C.snapshot x)))
    (by
      intro x
      refine ⟨fun _ => Or.inr ⟨?_, rfl⟩, fun t ht => absurd ht (by simp [initConfig])⟩
      rintro ⟨w, hw, -⟩
      simp [events] at hw) ?_ h
  intro ls C m C' hrunls ih hstep
  have huls : UniqueIds (events ls) := (inv_ids hrunls).2
  have hu : UniqueIds (events (ls ++ [m])) := (inv_ids (hrunls.snoc hstep)).2
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc =>
    intro x; rw [events_snoc_adm]; exact ih x
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro x
    rw [events_snoc_ev] at hu ⊢
    refine ⟨fun hc => absurd hc (by simp), fun t' ht' => ?_⟩
    have htt : t = t' := Option.some.inj ht'
    subst htt
    refine CommittedVal.snoc hu ?_ ?_ ((ih x).2 t rfl)
    · rintro ⟨-, v', s, hset, -⟩; simp at hset
    · intro b hbm hb
      obtain ⟨-, v', s, hset, c, hc, hcl⟩ := hb
      refine ⟨hbm, v', s, hset, ?_⟩
      rcases List.mem_append.mp hc with h' | h'
      · exact ⟨c, h', hcl⟩
      · have hce : c = (⟨α, Label.get l v t⟩ : Event) := by simpa using h'
        subst hce; simp at hcl
  | @set σ i t E snap body n u l v α hfresh =>
    intro x
    rw [events_snoc_ev] at hu ⊢
    refine ⟨fun hc => absurd hc (by simp), fun t' ht' => ?_⟩
    have htt : t = t' := Option.some.inj ht'
    subst htt
    refine CommittedVal.snoc hu ?_ ?_ ((ih x).2 t rfl)
    · -- the write just made is not committed: `t` has not ended
      rintro ⟨-, v', s, hset, c, hc, hcl⟩
      have hst : s = t := by simp at hset; exact hset.2.2.symm ▸ rfl
      rcases List.mem_append.mp hc with h' | h'
      · exact inv_live_open hrunls t rfl c h' (by rw [hcl, hst])
      · have hce : c = (⟨α, Label.set l v t⟩ : Event) := by simpa using h'
        subst hce; simp at hcl
    · intro b hbm hb
      obtain ⟨-, v', s, hset, c, hc, hcl⟩ := hb
      refine ⟨hbm, v', s, hset, ?_⟩
      rcases List.mem_append.mp hc with h' | h'
      · exact ⟨c, h', hcl⟩
      · have hce : c = (⟨α, Label.set l v t⟩ : Event) := by simpa using h'
        subst hce; simp at hcl
  | @retry σ i t E snap body n u α hfresh =>
    intro x
    rw [events_snoc_ev] at hu ⊢
    refine ⟨fun _ => ?_, fun t' ht' => absurd ht' (by simp)⟩
    refine CommittedVal.snoc hu ?_ ?_ ((ih x).2 t rfl)
    · rintro ⟨-, v', s, hset, -⟩; simp at hset
    · intro b hbm hb
      obtain ⟨-, v', s, hset, c, hc, hcl⟩ := hb
      refine ⟨hbm, v', s, hset, ?_⟩
      rcases List.mem_append.mp hc with h' | h'
      · exact ⟨c, h', hcl⟩
      · have hce : c = (⟨α, Label.retry t⟩ : Event) := by simpa using h'
        subst hce; simp at hcl
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro x
    rw [events_snoc_ev] at hu ⊢
    refine ⟨fun hc => absurd hc (by simp), fun t' ht' => ?_⟩
    have hpre : θ = none := (inv_lock hrunls).mp rfl
    refine CommittedVal.snoc hu ?_ ?_ ((ih x).1 hpre)
    · rintro ⟨-, v', s, hset, -⟩; simp at hset
    · intro b hbm hb
      obtain ⟨-, v', s, hset, c, hc, hcl⟩ := hb
      refine ⟨hbm, v', s, hset, ?_⟩
      rcases List.mem_append.mp hc with h' | h'
      · exact ⟨c, h', hcl⟩
      · have hce : c = (⟨α, Label.begin n⟩ : Event) := by simpa using h'
        subst hce; simp at hcl
  | @eend σ i t E snap body n u α hfresh =>
    intro x
    rw [events_snoc_ev] at hu ⊢
    refine ⟨fun _ => ?_, fun t' ht' => absurd ht' (by simp)⟩
    by_cases hw : WroteTo (events ls) t x
    · -- `t` wrote `x`; its last write there is now the last committed write
      obtain ⟨w, hwm, hpw, hmax⟩ :=
        exists_last_of (fun w => ∃ v, w.label = .set x v t) (events ls) huls hw
      have hval : w.label.accessVal = some (σ x) :=
        (inv_live_store hrunls t rfl x).1 w ⟨hwm, hpw, hmax⟩
      obtain ⟨vw, hwset⟩ := hpw
      refine Or.inl ⟨w, ⟨⟨List.mem_append.mpr (Or.inl hwm), vw, t, hwset,
        ⟨α, Label.eend t⟩, by simp, rfl⟩, ?_⟩, hval⟩
      intro b hb hob
      obtain ⟨hbm, v', s, hbset, c, hc, hcl⟩ := hb
      have hbes : b ∈ events ls := by
        rcases List.mem_append.mp hbm with h' | h'
        · exact h'
        · have : b = (⟨α, Label.eend t⟩ : Event) := by simpa using h'
          subst this; simp at hbset
      have hobes : OccursBefore (events ls) w b :=
        OccursBefore.restrict_append hu hwm hbes hob
      by_cases hst : s = t
      · subst hst
        exact hmax b hbes ⟨v', hbset⟩ hobes
      · have hba : OccursBefore (events ls) b w :=
          inv_live_last hrunls t rfl b hbes w hwm
            (by rw [hbset]; exact hst) (by rw [hwset]; rfl)
        exact OccursBefore.irrefl huls (OccursBefore.trans huls hobes hba)
    · -- `t` never wrote `x`, so committing it changes nothing there
      have hss : σ x = snap x := (inv_live_store hrunls t rfl x).2 hw
      show CommittedVal (events ls ++ [(⟨α, Label.eend t⟩ : Event)]) x (σ x)
      rw [hss]
      refine CommittedVal.snoc hu ?_ ?_ ((ih x).2 t rfl)
      · rintro ⟨-, v', s, hset, -⟩; simp at hset
      · intro b hbm hb
        obtain ⟨-, v', s, hset, c, hc, hcl⟩ := hb
        refine ⟨hbm, v', s, hset, ?_⟩
        rcases List.mem_append.mp hc with h' | h'
        · exact ⟨c, h', hcl⟩
        · have hce : c = (⟨α, Label.eend t⟩ : Event) := by simpa using h'
          subst hce
          have hst : t = s := by simpa using hcl
          subst hst
          exact absurd ⟨b, hbm, v', hset⟩ hw


/-! ## Freezing the committed value at a read

`CommittedVal` is about the whole of `es`, so it is not stable: a later
transaction commits and it changes.  What a read saw is the committed value *as
of that read*, and that is stable, so it is what an induction over the run can
carry. -/

/-- A write to `x` that was committed before `e`. -/
def CommittedWriteBefore (es : List Event) (x : Loc) (e w : Event) : Prop :=
  w ∈ es ∧ (∃ v s, w.label = .set x v s ∧ ∃ c ∈ es, c.label = .eend s ∧ OccursBefore es c e)
       ∧ OccursBefore es w e

def LastCommittedWriteBefore (es : List Event) (x : Loc) (e w : Event) : Prop :=
  CommittedWriteBefore es x e w ∧ ∀ b, CommittedWriteBefore es x e b → ¬ OccursBefore es w b

/-- The committed value of `x` as of `e`. -/
def CommittedValBefore (es : List Event) (x : Loc) (e : Event) (v : Nat) : Prop :=
  (∃ w, LastCommittedWriteBefore es x e w ∧ w.label.accessVal = some v)
  ∨ ((¬ ∃ w, CommittedWriteBefore es x e w) ∧ v = Store.init_store x)

theorem CommittedWriteBefore.restrict {es : List Event} {x : Loc} {e w n : Event}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es)
    (h : CommittedWriteBefore (es ++ [n]) x e w) : CommittedWriteBefore es x e w := by
  obtain ⟨hwm, ⟨v, s, hset, c, hcm, hcl, hce⟩, hwe⟩ := h
  have hces : c ∈ es := by
    rcases List.mem_append.mp hcm with h' | h'
    · exact h'
    · exact absurd (List.mem_singleton.mp h' ▸ hce) (not_occursBefore_snoc hu he)
  have hwes : w ∈ es := by
    rcases List.mem_append.mp hwm with h' | h'
    · exact h'
    · exact absurd (List.mem_singleton.mp h' ▸ hwe) (not_occursBefore_snoc hu he)
  exact ⟨hwes, ⟨v, s, hset, c, hces, hcl,
      OccursBefore.restrict_append hu hces he hce⟩,
    OccursBefore.restrict_append hu hwes he hwe⟩

theorem CommittedWriteBefore.mono {es : List Event} {x : Loc} {e w n : Event}
    (h : CommittedWriteBefore es x e w) : CommittedWriteBefore (es ++ [n]) x e w := by
  obtain ⟨hwm, ⟨v, s, hset, c, hcm, hcl, hce⟩, hwe⟩ := h
  exact ⟨List.mem_append.mpr (Or.inl hwm),
    ⟨v, s, hset, c, List.mem_append.mpr (Or.inl hcm), hcl, OccursBefore.snoc_mono hce⟩,
    OccursBefore.snoc_mono hwe⟩

/-- What an older read saw is unchanged by a later step. -/
theorem CommittedValBefore.snoc {es : List Event} {x : Loc} {e n : Event} {v : Nat}
    (hu : UniqueIds (es ++ [n])) (he : e ∈ es)
    (h : CommittedValBefore es x e v) : CommittedValBefore (es ++ [n]) x e v := by
  rcases h with ⟨w, ⟨hcw, hmax⟩, hval⟩ | ⟨hnone, hinit⟩
  · refine Or.inl ⟨w, ⟨hcw.mono, ?_⟩, hval⟩
    intro b hb hob
    exact hmax b (hb.restrict hu he)
      (OccursBefore.restrict_append hu hcw.1 (hb.restrict hu he).1 hob)
  · exact Or.inr ⟨fun ⟨w, hw⟩ => hnone ⟨w, hw.restrict hu he⟩, hinit⟩

/-- At the moment of the read, "committed" and "committed before this read"
agree: everything already in the trace happened before it. -/
theorem CommittedVal.toBefore {es : List Event} {x : Loc} {v : Nat} {e : Event}
    (hu : UniqueIds (es ++ [e])) (h : CommittedVal es x v) :
    CommittedValBefore (es ++ [e]) x e v := by
  have hback : ∀ b, CommittedWriteBefore (es ++ [e]) x e b → CommittedWrite es x b := by
    intro b hb
    obtain ⟨hbm, ⟨v', s, hset, c, hcm, hcl, hce⟩, hbe⟩ := hb
    have hces : c ∈ es := by
      rcases List.mem_append.mp hcm with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h' ▸ hce) (OccursBefore.irrefl hu)
    have hbes : b ∈ es := by
      rcases List.mem_append.mp hbm with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h' ▸ hbe) (OccursBefore.irrefl hu)
    exact ⟨hbes, v', s, hset, c, hces, hcl⟩
  rcases h with ⟨w, ⟨hcw, hmax⟩, hval⟩ | ⟨hnone, hinit⟩
  · obtain ⟨hwm, v', s, hset, c, hcm, hcl⟩ := hcw
    refine Or.inl ⟨w, ⟨⟨List.mem_append.mpr (Or.inl hwm),
      ⟨v', s, hset, c, List.mem_append.mpr (Or.inl hcm), hcl,
        OccursBefore.snoc_last hcm⟩, OccursBefore.snoc_last hwm⟩, ?_⟩, hval⟩
    intro b hb hob
    exact hmax b (hback b hb)
      (OccursBefore.restrict_append hu hwm (hback b hb).1 hob)
  · exact Or.inr ⟨fun ⟨w, hw⟩ => hnone ⟨w, hback w hw⟩, hinit⟩

/-- `t` has neither read nor written `x` before `e`. -/
def NoPriorAccess (es : List Event) (t : TxId) (x : Loc) (e : Event) : Prop :=
  ¬ ∃ a ∈ es, a.label.tx = t ∧ a.label.accesses x = true ∧ OccursBefore es a e

theorem NoPriorAccess.restrict {es : List Event} {t : TxId} {x : Loc} {e n : Event}
    (h : NoPriorAccess (es ++ [n]) t x e) : NoPriorAccess es t x e := by
  rintro ⟨a, ham, hat, hax, hae⟩
  exact h ⟨a, List.mem_append.mpr (Or.inl ham), hat, hax, OccursBefore.snoc_mono hae⟩

/-- **`Ext` on the trace.**  A read of `x` by a transaction that has not touched
`x` sees the value the last transaction to commit a write to `x` left there, or
the initial store when nobody has. -/
theorem inv_ext {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ (x n : Nat) (t : TxId) (e : Event), e ∈ events τ → e.label = .get x n t →
      NoPriorAccess (events τ) t x e → CommittedValBefore (events τ) x e n := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ (x n : Nat) (t : TxId) (e : Event), e ∈ events τ → e.label = .get x n t →
        NoPriorAccess (events τ) t x e → CommittedValBefore (events τ) x e n)
    (by intro x n t e he _ _; simp [events] at he) ?_ h
  intro ls C m C' hrunls ih hstep
  have hu : UniqueIds (events (ls ++ [m])) := (inv_ids (hrunls.snoc hstep)).2
  -- every case but the read just taken is the same: the step changed nothing
  -- for a read that already happened
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc =>
    intro x n t e he hlab hnp
    rw [events_snoc_adm] at he hnp ⊢
    exact ih x n t e he hlab hnp
  | @set σ i t E snap body n u l v α hfresh =>
    intro x nn t'' e he hlab hnp
    rw [events_snoc_ev] at he hnp hu ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact (ih x nn t'' e h' hlab hnp.restrict).snoc hu h'
    · have : e = (⟨α, Label.set l v t⟩ : Event) := by simpa using h'
      subst this; simp at hlab
  | @eend σ i t E snap body n u α hfresh =>
    intro x nn t'' e he hlab hnp
    rw [events_snoc_ev] at he hnp hu ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact (ih x nn t'' e h' hlab hnp.restrict).snoc hu h'
    · have : e = (⟨α, Label.eend t⟩ : Event) := by simpa using h'
      subst this; simp at hlab
  | @retry σ i t E snap body n u α hfresh =>
    intro x nn t'' e he hlab hnp
    rw [events_snoc_ev] at he hnp hu ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact (ih x nn t'' e h' hlab hnp.restrict).snoc hu h'
    · have : e = (⟨α, Label.retry t⟩ : Event) := by simpa using h'
      subst this; simp at hlab
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro x nn t'' e he hlab hnp
    rw [events_snoc_ev] at he hnp hu ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact (ih x nn t'' e h' hlab hnp.restrict).snoc hu h'
    · have : e = (⟨α, Label.begin n⟩ : Event) := by simpa using h'
      subst this; simp at hlab
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro x nn t'' e he hlab hnp
    rw [events_snoc_ev] at he hnp hu ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact (ih x nn t'' e h' hlab hnp.restrict).snoc hu h'
    · -- the read just taken
      have hea : e = (⟨α, Label.get l v t⟩ : Event) := by simpa using h'
      subst hea
      simp at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      -- the reader has not written `x`, so the store still holds the snapshot
      have hnw : ¬ WroteTo (events ls) t l := by
        rintro ⟨w, hwm, v', hwset⟩
        exact hnp ⟨w, List.mem_append.mpr (Or.inl hwm), by rw [hwset]; rfl,
          by rw [hwset]; simp [Label.accesses],
          OccursBefore.snoc_last hwm⟩
      have hss : σ l = snap l := (inv_live_store hrunls t rfl l).2 hnw
      have hcv : CommittedVal (events ls) l v := by
        rw [← hv, hss]; exact (inv_committed hrunls l).2 t rfl
      exact CommittedVal.toBefore hu hcv


/-! ## Transactions are blocks

The lock does not merely keep transactions from interleaving step by step: it
lays them out in the trace one after another.  That is what turns `ar` from a
choice into a fact, because real-time order is then total on the transactions a
run performs. -/

/-- Everything `s` did comes before everything `t` did. -/
def BlockBefore (es : List Event) (s t : TxId) : Prop :=
  ∀ a ∈ es, a.label.tx = s → ∀ b ∈ es, b.label.tx = t → OccursBefore es a b

theorem BlockBefore.asymm {es : List Event} {s t : TxId} (hu : UniqueIds es)
    {a b : Event} (ha : a ∈ es) (hat : a.label.tx = s) (hb : b ∈ es) (hbt : b.label.tx = t)
    (h1 : BlockBefore es s t) (h2 : BlockBefore es t s) : False :=
  OccursBefore.irrefl hu
    (OccursBefore.trans hu (h1 a ha hat b hb hbt) (h2 b hb hbt a ha hat))

/-- The live transaction has already begun. -/
theorem inv_live_begun {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ t, C.activeTx = some t → ∃ b ∈ events τ, b.label = .begin t := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ t, C.activeTx = some t → ∃ b ∈ events τ, b.label = .begin t)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C m C' hrunls ih hstep
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => intro t ht; rw [events_snoc_adm]; exact ih t ht
  | @eend σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @retry σ i t E snap body n u α hfresh => intro t' ht'; exact absurd ht' (by simp)
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro t' ht'
    obtain ⟨b, hbm, hbl⟩ := ih t' ht'
    exact ⟨b, by rw [events_snoc_ev]; exact List.mem_append.mpr (Or.inl hbm), hbl⟩
  | @set σ i t E snap body n u l v α hfresh =>
    intro t' ht'
    obtain ⟨b, hbm, hbl⟩ := ih t' ht'
    exact ⟨b, by rw [events_snoc_ev]; exact List.mem_append.mpr (Or.inl hbm), hbl⟩
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro t' ht'
    have hn : n = t' := Option.some.inj ht'
    subst hn
    exact ⟨⟨α, Label.begin n⟩, by rw [events_snoc_ev]; simp, rfl⟩

/-- Every event's transaction has a `begin`. -/
theorem inv_begun {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ e ∈ events τ, ∃ b ∈ events τ, b.label = .begin e.label.tx := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ e ∈ events τ, ∃ b ∈ events τ, b.label = .begin e.label.tx)
    (by intro e he; simp [events] at he) ?_ h
  intro ls C m C' hrunls ih hstep
  have lift : ∀ (n : Event) (e : Event), (∃ b ∈ events ls, b.label = .begin e.label.tx) →
      ∃ b ∈ events ls ++ [n], b.label = .begin e.label.tx := by
    rintro n e ⟨b, hbm, hbl⟩
    exact ⟨b, List.mem_append.mpr (Or.inl hbm), hbl⟩
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => intro e he; rw [events_snoc_adm] at he ⊢; exact ih e he
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro e he
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h')
    · have : e = (⟨α, Label.begin n⟩ : Event) := by simpa using h'
      subst this
      exact ⟨⟨α, Label.begin n⟩, by simp, rfl⟩
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro e he
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h')
    · have : e = (⟨α, Label.get l v t⟩ : Event) := by simpa using h'
      subst this
      exact lift _ _ (inv_live_begun hrunls t rfl)
  | @set σ i t E snap body n u l v α hfresh =>
    intro e he
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h')
    · have : e = (⟨α, Label.set l v t⟩ : Event) := by simpa using h'
      subst this
      exact lift _ _ (inv_live_begun hrunls t rfl)
  | @eend σ i t E snap body n u α hfresh =>
    intro e he
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h')
    · have : e = (⟨α, Label.eend t⟩ : Event) := by simpa using h'
      subst this
      exact lift _ _ (inv_live_begun hrunls t rfl)
  | @retry σ i t E snap body n u α hfresh =>
    intro e he
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h')
    · have : e = (⟨α, Label.retry t⟩ : Event) := by simpa using h'
      subst this
      exact lift _ _ (inv_live_begun hrunls t rfl)

/-- Every transaction but the live one has finished. -/
theorem inv_terminated {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) :
    ∀ e ∈ events τ, C.activeTx ≠ some e.label.tx →
      ∃ a ∈ events τ, (a.label = .eend e.label.tx ∨ a.label = .retry e.label.tx) := by
  refine Run.reverseRecOn (motive := fun τ C =>
      ∀ e ∈ events τ, C.activeTx ≠ some e.label.tx →
        ∃ a ∈ events τ, (a.label = .eend e.label.tx ∨ a.label = .retry e.label.tx))
    (by intro e he; simp [events] at he) ?_ h
  intro ls C m C' hrunls ih hstep
  have lift : ∀ (n : Event) (e : Event),
      (∃ a ∈ events ls, (a.label = .eend e.label.tx ∨ a.label = .retry e.label.tx)) →
      ∃ a ∈ events ls ++ [n], (a.label = .eend e.label.tx ∨ a.label = .retry e.label.tx) := by
    rintro n e ⟨a, ham, hal⟩
    exact ⟨a, List.mem_append.mpr (Or.inl ham), hal⟩
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => intro e he hne; rw [events_snoc_adm] at he ⊢; exact ih e he hne
  | @get σ i t E snap body n u l v α hfresh hv =>
    intro e he hne
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h' hne)
    · have : e = (⟨α, Label.get l v t⟩ : Event) := by simpa using h'
      subst this; exact absurd rfl hne
  | @set σ i t E snap body n u l v α hfresh =>
    intro e he hne
    rw [events_snoc_ev] at he ⊢
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h' hne)
    · have : e = (⟨α, Label.set l v t⟩ : Event) := by simpa using h'
      subst this; exact absurd rfl hne
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro e he hne
    rw [events_snoc_ev] at he ⊢
    have hpre : θ = none := (inv_lock hrunls).mp rfl
    rcases List.mem_append.mp he with h' | h'
    · exact lift _ e (ih e h' (by rw [hpre]; simp))
    · have : e = (⟨α, Label.begin n⟩ : Event) := by simpa using h'
      subst this; exact absurd rfl hne
  | @eend σ i t E snap body n u α hfresh =>
    intro e he _
    rw [events_snoc_ev] at he ⊢
    by_cases het : e.label.tx = t
    · exact ⟨⟨α, Label.eend t⟩, by simp, Or.inl (by rw [het])⟩
    · rcases List.mem_append.mp he with h' | h'
      · exact lift _ e (ih e h' (fun hc => het (Option.some.inj hc).symm))
      · have : e = (⟨α, Label.eend t⟩ : Event) := by simpa using h'
        subst this; exact absurd rfl het
  | @retry σ i t E snap body n u α hfresh =>
    intro e he _
    rw [events_snoc_ev] at he ⊢
    by_cases het : e.label.tx = t
    · exact ⟨⟨α, Label.retry t⟩, by simp, Or.inr (by rw [het])⟩
    · rcases List.mem_append.mp he with h' | h'
      · exact lift _ e (ih e h' (fun hc => het (Option.some.inj hc).symm))
      · have : e = (⟨α, Label.retry t⟩ : Event) := by simpa using h'
        subst this; exact absurd rfl het

/-- **The lock serialises.**  Any two distinct transactions of a run are laid
out one entirely before the other. -/
theorem inv_block {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (h : Run (initConfig E₀) τ C) : ∀ s t : TxId, s ≠ t →
      BlockBefore (events τ) s t ∨ BlockBefore (events τ) t s := by
  refine Run.reverseRecOn (motive := fun τ C => ∀ s t : TxId, s ≠ t →
      BlockBefore (events τ) s t ∨ BlockBefore (events τ) t s)
    (by intro s t _; exact Or.inl (by intro a ha; simp [events] at ha)) ?_ h
  intro ls C m C' hrunls ih hstep
  have mono : ∀ (n : Event) (s t : TxId), n.label.tx ≠ s → n.label.tx ≠ t →
      BlockBefore (events ls) s t → BlockBefore (events ls ++ [n]) s t := by
    intro n s t hns hnt hb a ha hat b hb' hbt
    have ha' : a ∈ events ls := by
      rcases List.mem_append.mp ha with h' | h'
      · exact h'
      · exact absurd hat (by rw [List.mem_singleton.mp h']; exact hns)
    have hb'' : b ∈ events ls := by
      rcases List.mem_append.mp hb' with h' | h'
      · exact h'
      · exact absurd hbt (by rw [List.mem_singleton.mp h']; exact hnt)
    exact OccursBefore.snoc_mono (hb a ha' hat b hb'' hbt)
  -- the new event belongs to the live transaction, which owns the tail
  have live : ∀ (α : EvId) (lb : Label) (t₀ : TxId), lb.tx = t₀ →
      (∀ a ∈ events ls, ∀ b ∈ events ls, a.label.tx ≠ t₀ → b.label.tx = t₀ →
        OccursBefore (events ls) a b) →
      ∀ s, s ≠ t₀ → BlockBefore (events ls ++ [(⟨α, lb⟩ : Event)]) s t₀ := by
    intro α lb t₀ hlb hll s hst a ha hat b hb hbt
    have ha' : a ∈ events ls := by
      rcases List.mem_append.mp ha with h' | h'
      · exact h'
      · exact absurd hat (by rw [List.mem_singleton.mp h', hlb]; exact fun hc => hst hc.symm)
    rcases List.mem_append.mp hb with h' | h'
    · exact OccursBefore.snoc_mono (hll a ha' b h' (by rw [hat]; exact hst) hbt)
    · rw [List.mem_singleton.mp h']
      exact OccursBefore.snoc_last ha'
  cases hstep with
  | ctx _ hhead =>
  cases hhead with
  | @adm Cadm i r eb hloc => intro s t hst; rw [events_snoc_adm]; exact ih s t hst
  | @begin σ θ E snap body n u i eb α hfresh =>
    intro s t hst
    rw [events_snoc_ev]
    have hold : ∀ c ∈ events ls, c.label.tx ≠ n := by
      intro c hc hcn
      have hlt := (inv_nextTx hrunls).1 c hc
      rw [hcn] at hlt
      exact Nat.lt_irrefl _ hlt
    have hll : ∀ a ∈ events ls, ∀ b ∈ events ls, a.label.tx ≠ n → b.label.tx = n →
        OccursBefore (events ls) a b := by
      intro a _ b hb _ hbn; exact absurd hbn (hold b hb)
    by_cases htn : t = n
    · subst htn
      exact Or.inl (live α (Label.begin t) t rfl hll s hst)
    · by_cases hsn : s = n
      · subst hsn
        exact Or.inr (live α (Label.begin s) s rfl hll t (fun hc => hst hc.symm))
      · rcases ih s t hst with hb | hb
        · exact Or.inl (mono _ s t (fun hc => hsn hc.symm) (fun hc => htn hc.symm) hb)
        · exact Or.inr (mono _ t s (fun hc => htn hc.symm) (fun hc => hsn hc.symm) hb)
  | @get σ i t₀ E snap body n u l v α hfresh hv =>
    intro s t hst
    rw [events_snoc_ev]
    have hll := inv_live_last hrunls t₀ rfl
    by_cases htn : t = t₀
    · subst htn
      exact Or.inl (live α (Label.get l v t) t rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) s hst)
    · by_cases hsn : s = t₀
      · subst hsn
        exact Or.inr (live α (Label.get l v s) s rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) t
          (fun hc => hst hc.symm))
      · rcases ih s t hst with hb | hb
        · exact Or.inl (mono _ s t (fun hc => hsn hc.symm) (fun hc => htn hc.symm) hb)
        · exact Or.inr (mono _ t s (fun hc => htn hc.symm) (fun hc => hsn hc.symm) hb)
  | @set σ i t₀ E snap body n u l v α hfresh =>
    intro s t hst
    rw [events_snoc_ev]
    have hll := inv_live_last hrunls t₀ rfl
    by_cases htn : t = t₀
    · subst htn
      exact Or.inl (live α (Label.set l v t) t rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) s hst)
    · by_cases hsn : s = t₀
      · subst hsn
        exact Or.inr (live α (Label.set l v s) s rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) t
          (fun hc => hst hc.symm))
      · rcases ih s t hst with hb | hb
        · exact Or.inl (mono _ s t (fun hc => hsn hc.symm) (fun hc => htn hc.symm) hb)
        · exact Or.inr (mono _ t s (fun hc => htn hc.symm) (fun hc => hsn hc.symm) hb)
  | @eend σ i t₀ E snap body n u α hfresh =>
    intro s t hst
    rw [events_snoc_ev]
    have hll := inv_live_last hrunls t₀ rfl
    by_cases htn : t = t₀
    · subst htn
      exact Or.inl (live α (Label.eend t) t rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) s hst)
    · by_cases hsn : s = t₀
      · subst hsn
        exact Or.inr (live α (Label.eend s) s rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) t
          (fun hc => hst hc.symm))
      · rcases ih s t hst with hb | hb
        · exact Or.inl (mono _ s t (fun hc => hsn hc.symm) (fun hc => htn hc.symm) hb)
        · exact Or.inr (mono _ t s (fun hc => htn hc.symm) (fun hc => hsn hc.symm) hb)
  | @retry σ i t₀ E snap body n u α hfresh =>
    intro s t hst
    rw [events_snoc_ev]
    have hll := inv_live_last hrunls t₀ rfl
    by_cases htn : t = t₀
    · subst htn
      exact Or.inl (live α (Label.retry t) t rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) s hst)
    · by_cases hsn : s = t₀
      · subst hsn
        exact Or.inr (live α (Label.retry s) s rfl (fun a ha b hb h1 h2 => hll a ha b hb h1 h2) t
          (fun hc => hst hc.symm))
      · rcases ih s t hst with hb | hb
        · exact Or.inl (mono _ s t (fun hc => hsn hc.symm) (fun hc => htn hc.symm) hb)
        · exact Or.inr (mono _ t s (fun hc => htn hc.symm) (fun hc => hsn hc.symm) hb)


/-! ## `ar` is not a choice

`HistoryOf` asks only that `ar` be a total order containing real-time order.
Under the lock that pins it down completely, because real-time order is already
total on a run's transactions — so anything `ar` says, the trace said first. -/

theorem eend_of_committed {es : List Event} {t : TxId} (h : statusOf es t = .Committed) :
    ∃ c ∈ es, c.label = .eend t := by
  by_cases hany : es.any (fun e => e.label == .eend t) = true
  · obtain ⟨c, hc, hcl⟩ := List.any_eq_true.mp hany
    exact ⟨c, hc, by simpa using hcl⟩
  · rw [statusOf, if_neg hany] at h
    split at h <;> simp at h

theorem committed_of_eend {es : List Event} {t : TxId} {c : Event}
    (hc : c ∈ es) (hcl : c.label = .eend t) : statusOf es t = .Committed := by
  have : es.any (fun e => e.label == .eend t) = true :=
    List.any_eq_true.mpr ⟨c, hc, by simp [hcl]⟩
  rw [statusOf, if_pos this]

/-- A block order between two distinct transactions *is* real-time order: the
earlier one has already finished (only the live transaction has not, and the
live one owns the tail), and the later one has begun. -/
theorem rtb_of_block {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (hrun : Run (initConfig E₀) τ C) {s t : TxId}
    (hs : ∃ a ∈ events τ, a.label.tx = s) (ht : ∃ b ∈ events τ, b.label.tx = t)
    (hst : s ≠ t) (hb : BlockBefore (events τ) s t) : RealTimeBefore (events τ) s t := by
  obtain ⟨a₀, ha₀, ha₀s⟩ := hs
  obtain ⟨b₀, hb₀, hb₀t⟩ := ht
  have hu : UniqueIds (events τ) := (inv_ids hrun).2
  -- `s` is not the live transaction: the live one owns the tail, and `s` does not
  have hnotlive : C.activeTx ≠ some s := by
    intro hlive
    have hll := inv_live_last hrun s hlive b₀ hb₀ a₀ ha₀ (by rw [hb₀t]; exact fun hc => hst hc.symm) ha₀s
    exact OccursBefore.irrefl hu (OccursBefore.trans hu (hb a₀ ha₀ ha₀s b₀ hb₀ hb₀t) hll)
  obtain ⟨a, ham, hal⟩ := inv_terminated hrun a₀ ha₀ (by rw [ha₀s]; exact hnotlive)
  obtain ⟨b, hbm, hbl⟩ := inv_begun hrun b₀ hb₀
  rw [ha₀s] at hal
  rw [hb₀t] at hbl
  refine ⟨a, b, ⟨ham, hal⟩, ⟨hbm, hbl⟩, hb a ham ?_ b hbm (by rw [hbl]; rfl)⟩
  rcases hal with h' | h' <;> rw [h'] <;> rfl

/-- `ar` between two distinct transactions is the block order, so every `ar`
edge the history reports was already laid down by the run. -/
theorem block_of_ar {E₀ : ThreadMap} {τ : Trace} {C : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C) (hH : HistoryOf τ H) {s t : TxId}
    (hs : ∃ a ∈ events τ, a.label.tx = s) (ht : ∃ b ∈ events τ, b.label.tx = t)
    (hst : s ≠ t)
    (har : H.ar (transactionOf (events τ) s) (transactionOf (events τ) t)) :
    BlockBefore (events τ) s t := by
  obtain ⟨htxs, -, hasym, -, hrt⟩ := hH
  rcases inv_block hrun s t hst with hbst | hbts
  · exact hbst
  · exfalso
    have hS : H.txs (transactionOf (events τ) s) := (htxs _).mpr ⟨s, hs, rfl⟩
    have hT : H.txs (transactionOf (events τ) t) := (htxs _).mpr ⟨t, ht, rfl⟩
    exact hasym _ _ hT hS
      (hrt _ _ hT hS (fun hc => hst (congrArg Transaction.txid hc).symm)
        (rtb_of_block hrun ht hs (fun hc => hst hc.symm) hbts)) har

end Reagent
