/-
  P: the witness history of `τ` satisfies `Ext_c`. Every committed `T` and
  every external read `get(x, v)` of `T` returns the value of the AR-latest
  committed writer of `x`, or `σ₀(x)` if there is none.

  One step `es' = es ++ [n]` splits into two cases (L3):
    Com unchanged   n is not an end. Every committed T is an old transaction,
                    and its reads, its writers and AR before it are unchanged
                    (Lemma B).                                         ext_noend
    Com ∪ {t}       n = end t. Old committed T as above; t's commit is last,
                    so t is in no old W_x(T). For t itself:
                      R       Λ_t(x) = (v, _)    the log remembers what t read
                      KCasOk  σ(x) = v           validation at commit
                      Store   σ(x) = latest committed writer's value   ext_commit

  The table (one line per rule) is the P field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtConsistencyReads

namespace Optimistic

open Reagent (Loc TxId EvId Store)

-- The witness history of an event list: `witness τ = hist (events τ)`.
def hist (es : List Event) : History := ⟨txsOf es, finishOrder es⟩

/-! ## Commit events and status -/

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

/-! ## Old transactions (tag ≠ tag n) are unchanged by the step -/

-- An event of `es'` tagged `s ≠ tag(n)` is in `es`.
theorem mem_old {es : List Event} {n a : Event} {s : TxId} (hs : s ≠ n.label.tx)
    (ha : a ∈ es ++ [n]) (hat : a.label.tx = s) : a ∈ es := by
  sorry

theorem Terminates.snoc_iff {es : List Event} {n a : Event} {s : TxId} (hs : s ≠ n.label.tx) :
    Terminates (es ++ [n]) s a ↔ Terminates es s a := by
  sorry

theorem Begins.snoc_iff {es : List Event} {n a : Event} {s : TxId} (hs : s ≠ n.label.tx) :
    Begins (es ++ [n]) s a ↔ Begins es s a := by
  sorry

theorem Finished.snoc_iff {es : List Event} {n : Event} {s : TxId} (hs : s ≠ n.label.tx) :
    Finished (es ++ [n]) s ↔ Finished es s := by
  sorry

-- AR between old transactions is unchanged (B1 for the order of their events).
theorem finishOrder_snoc_iff {es : List Event} {n : Event} {S T : Transaction}
    (hu : UniqueIds (es ++ [n])) (hS : S.txid ≠ n.label.tx) (hT : T.txid ≠ n.label.tx) :
    finishOrder (es ++ [n]) S T ↔ finishOrder es S T := by
  unfold finishOrder
  rw [Finished.snoc_iff hS, Finished.snoc_iff hT]
  constructor
  · rintro (⟨a, b, ha, hb, hab⟩ | h | ⟨h1, h2, a, b, ha, hb, hab⟩)
    · rw [Terminates.snoc_iff hS] at ha
      rw [Terminates.snoc_iff hT] at hb
      exact Or.inl ⟨a, b, ha, hb, (B1 hu ha.1 hb.1).mp hab⟩
    · exact Or.inr (Or.inl h)
    · rw [Begins.snoc_iff hS] at ha
      rw [Begins.snoc_iff hT] at hb
      exact Or.inr (Or.inr ⟨h1, h2, a, b, ha, hb, (B1 hu ha.1 hb.1).mp hab⟩)
  · rintro (⟨a, b, ha, hb, hab⟩ | h | ⟨h1, h2, a, b, ha, hb, hab⟩)
    · exact Or.inl ⟨a, b, (Terminates.snoc_iff hS).mpr ha, (Terminates.snoc_iff hT).mpr hb,
        hab.snoc_mono⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, h2, a, b, (Begins.snoc_iff hS).mpr ha,
        (Begins.snoc_iff hT).mpr hb, hab.snoc_mono⟩)

theorem statusOf_snoc {es : List Event} {n : Event} {s : TxId} (hs : s ≠ n.label.tx) :
    statusOf (es ++ [n]) s = statusOf es s := by
  have h1 : (n.label == Label.eend s) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    apply hs
    rw [h]
    rfl
  have h2 : (n.label == Label.retry s) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    apply hs
    rw [h]
    rfl
  simp [statusOf, List.any_append, h1, h2]

-- B5: an old transaction is literally the same object after the step
-- (its events by B3, its po by B1, its status since n is not its terminator).
theorem transactionOf_snoc {es : List Event} {n : Event} {s : TxId}
    (hu : UniqueIds (es ++ [n])) (hs : s ≠ n.label.tx) :
    transactionOf (es ++ [n]) s = transactionOf es s := by
  have key : ∀ (P : Event → Prop) (st : Status), P = events_of_isAccess es s →
      (∀ a b, P a → P b → (OccursBefore (es ++ [n]) a b ↔ OccursBefore es a b)) →
      ({ E := P, po := fun a b => OccursBefore (es ++ [n]) a.val b.val, status := st,
          txid := s } : Transaction)
        = { E := events_of_isAccess es s, po := fun a b => OccursBefore es a.val b.val,
            status := st, txid := s } := by
    intro P st hP hr
    subst hP
    congr 1
    funext a b
    exact propext (hr a.val b.val a.property b.property)
  have h := key (events_of_isAccess (es ++ [n]) s) (statusOf es s) (B3 hs)
    (fun a b ha hb => B1 hu (mem_old hs ha.1 ha.2.1) (mem_old hs hb.1 hb.2.1))
  unfold transactionOf
  rw [statusOf_snoc hs]
  exact h

-- A transaction committed in `es` does not have the tag of `n`, if tag(n) has
-- no terminator in `es`.
theorem ne_tag_of_committed {es : List Event} {n : Event} {s : TxId}
    (htn : ∀ a, ¬ Terminates es n.label.tx a) (hc : ∃ c ∈ es, c.label = .eend s) :
    s ≠ n.label.tx := by
  rintro rfl
  obtain ⟨c, hc, hcl⟩ := hc
  exact htn c ⟨hc, Or.inl hcl⟩

/-! ## W_x(T) and max_AR W_x(T) for an old committed T -/

-- `S ∈ W_x(T)` is the same before and after. A transaction tagged tag(n) is
-- never AR-before T: its only terminator, if any, is n, the last event.
theorem inW_snoc_iff {es : List Event} {n : Event} (hu : UniqueIds (es ++ [n]))
    (htn : ∀ a, ¬ Terminates es n.label.tx a) {t : TxId} (ht : t ≠ n.label.tx)
    (hTfin : ∃ c ∈ es, c.label = .eend t) {x : Loc} {S : Transaction} :
    (hist (es ++ [n])).InW x (transactionOf es t) S ↔ (hist es).InW x (transactionOf es t) S := by
  constructor
  · rintro ⟨⟨s, -, rfl⟩, hSc, hne, har, hw⟩
    by_cases hs : s = n.label.tx
    · -- S has the tag of n: not AR-before T
      exfalso
      subst hs
      obtain ⟨c, hc, hcl⟩ := hTfin
      have hTt : Terminates (es ++ [n]) t c := ⟨List.mem_append_left _ hc, Or.inl hcl⟩
      rcases har with ⟨a, b, ha, hb, hab⟩ | ⟨-, hnf⟩ | ⟨-, hnf, -⟩
      · have hb' : b ∈ es := mem_old ht hb.1 hb.tx
        rcases List.mem_append.mp ha.1 with ha' | ha'
        · exact htn a ⟨ha', ha.2⟩
        · rw [List.mem_singleton.mp ha'] at hab
          exact not_occursBefore_snoc hu hb' hab
      · exact hnf ⟨c, hTt⟩
      · exact hnf ⟨c, hTt⟩
    · -- S is old
      rw [transactionOf_snoc hu hs] at hSc hne hw ⊢
      obtain ⟨c, hc, hcl⟩ := eend_of_committed hSc
      exact ⟨⟨s, ⟨c, hc, by rw [hcl]; rfl⟩, rfl⟩, hSc, hne,
        (finishOrder_snoc_iff hu hs ht).mp (by rw [← transactionOf_snoc hu hs]; exact har), hw⟩
  · rintro ⟨⟨s, ⟨e, he, het⟩, rfl⟩, hSc, hne, har, hw⟩
    have hs : s ≠ n.label.tx := ne_tag_of_committed htn (eend_of_committed hSc)
    refine ⟨⟨s, ⟨e, List.mem_append_left _ he, het⟩, (transactionOf_snoc hu hs).symm⟩,
      hSc, hne, (finishOrder_snoc_iff hu hs ht).mpr har, hw⟩

theorem maxW_snoc_iff {es : List Event} {n : Event} (hu : UniqueIds (es ++ [n]))
    (htn : ∀ a, ¬ Terminates es n.label.tx a) {t : TxId} (ht : t ≠ n.label.tx)
    (hTfin : ∃ c ∈ es, c.label = .eend t) {x : Loc} {S : Transaction} :
    (hist (es ++ [n])).MaxW x (transactionOf es t) S ↔ (hist es).MaxW x (transactionOf es t) S := by
  have hInW := fun U => inW_snoc_iff hu htn ht hTfin (x := x) (S := U)
  -- a member of W_x(T) is committed in es, so its tag is not tag(n)
  have htx : ∀ U, (hist es).InW x (transactionOf es t) U → U.txid ≠ n.label.tx := by
    rintro U ⟨⟨u, -, rfl⟩, hUc, -⟩
    exact ne_tag_of_committed htn (eend_of_committed hUc)
  constructor
  · rintro ⟨hS, hmax⟩
    have hS' := (hInW S).mp hS
    refine ⟨hS', fun U hU => ?_⟩
    rcases hmax U ((hInW U).mpr hU) with h | h
    · exact Or.inl h
    · exact Or.inr ((finishOrder_snoc_iff hu (htx U hU) (htx S hS')).mp h)
  · rintro ⟨hS, hmax⟩
    refine ⟨(hInW S).mpr hS, fun U hU => ?_⟩
    have hU' := (hInW U).mp hU
    rcases hmax U hU' with h | h
    · exact Or.inl h
    · exact Or.inr ((finishOrder_snoc_iff hu (htx U hU') (htx S hS)).mpr h)

/-! ## The two cases of L3 -/

-- An old committed T (tag ≠ tag n): its reads, W_x(T) and max_AR are unchanged.
theorem ext_old {es : List Event} {n : Event} (hu : UniqueIds (es ++ [n]))
    (htn : ∀ a, ¬ Terminates es n.label.tx a) (h : (hist es).ExtC)
    {t : TxId} (ht : t ≠ n.label.tx)
    (hcom : (transactionOf (es ++ [n]) t).status = .Committed) (x : Loc) (v : Nat)
    (hread : (transactionOf (es ++ [n]) t).ReadsExt x v) :
    ((¬ ∃ S, (hist (es ++ [n])).InW x (transactionOf (es ++ [n]) t) S) ∧ v = Store.init_store x)
      ∨ ∃ S, (hist (es ++ [n])).MaxW x (transactionOf (es ++ [n]) t) S ∧ S.WritesVal x v := by
  rw [transactionOf_snoc hu ht] at hcom hread ⊢
  obtain ⟨c, hc, hcl⟩ := eend_of_committed hcom
  have hT : (hist es).txs (transactionOf es t) := ⟨t, ⟨c, hc, by rw [hcl]; rfl⟩, rfl⟩
  rcases h _ hT hcom x v hread with ⟨hno, hinit⟩ | ⟨S, hmax, hw⟩
  · exact Or.inl ⟨fun ⟨S, hS⟩ => hno ⟨S, (inW_snoc_iff hu htn ht ⟨c, hc, hcl⟩).mp hS⟩, hinit⟩
  · exact Or.inr ⟨S, (maxW_snoc_iff hu htn ht ⟨c, hc, hcl⟩).mpr hmax, hw⟩

-- Com unchanged: n is not an end, so every committed T is old.
theorem ext_noend {es : List Event} {n : Event} (hu : UniqueIds (es ++ [n]))
    (htn : ∀ a, ¬ Terminates es n.label.tx a) (hn : ∀ t, n.label ≠ .eend t)
    (h : (hist es).ExtC) : (hist (es ++ [n])).ExtC := by
  rintro T ⟨t, -, rfl⟩ hcom x v hread
  have ht : t ≠ n.label.tx := by
    rintro rfl
    obtain ⟨c, hc, hcl⟩ := eend_of_committed hcom
    rcases List.mem_append.mp hc with hc | hc
    · exact htn c ⟨hc, Or.inl hcl⟩
    · rw [List.mem_singleton.mp hc] at hcl
      exact hn _ hcl
  exact ext_old hu htn h ht hcom x v hread

-- The newly committed t: its external read get(x, v) sees the latest
-- committed writer of x (R, KCasOk, Store).
theorem ext_new {es : List Event} {n : Event} {t : TxId} {σ : Store} {Λ : Log}
    (hu : UniqueIds (es ++ [n])) (hn : n.label = .eend t)
    (hlive : ∀ a, ¬ Terminates es t a) (hR : RLog es t Λ) (hok : KCasOk σ Λ)
    (hst : StoreInv es σ) (x : Loc) (v : Nat)
    (hread : (transactionOf (es ++ [n]) t).ReadsExt x v) :
    ((¬ ∃ S, (hist (es ++ [n])).InW x (transactionOf (es ++ [n]) t) S) ∧ v = Store.init_store x)
      ∨ ∃ S, (hist (es ++ [n])).MaxW x (transactionOf (es ++ [n]) t) S ∧ S.WritesVal x v := by
  -- R: the read is an old, external read of t, so Λ(x) = (v, _)
  obtain ⟨⟨e, heE⟩, ⟨t', hle⟩, hnoprior⟩ := hread
  replace hle : e.label = .get x v t' := hle
  have htt : t' = t := by
    have het : e.label.tx = t := heE.2.1
    rw [hle] at het
    exact het
  subst htt
  have he : e ∈ es := by
    rcases List.mem_append.mp heE.1 with he | he
    · exact he
    · rw [List.mem_singleton.mp he, hn] at hle
      cases hle
  have hext : IsExt es e := ⟨x, v, t', hle, fun ⟨a, ha, hat, hacc, hae⟩ =>
    hnoprior ⟨⟨a, List.mem_append_left _ ha, hat, isAccess_of_accesses hacc⟩, hae.snoc_mono, hacc⟩⟩
  obtain ⟨c, hc⟩ := hR e x v he hle hext
  -- KCasOk: σ(x) = v
  have hσ : σ x = v := hok x v c hc
  -- a committed U ≠ T in es' committed in es (its end is not n)
  have hold : ∀ u b, b ∈ es ++ [n] → b.label = .eend u → u ≠ t' → b ∈ es := by
    intro u b hb hbl hut
    rcases List.mem_append.mp hb with hb | hb
    · exact hb
    · rw [List.mem_singleton.mp hb, hn] at hbl
      cases hbl
      exact absurd rfl hut
  have hnset : ∀ u w, n.label ≠ .set x w u := by
    intro u w h
    rw [hn] at h
    cases h
  -- Store: σ(x) is the latest committed writer's value, or σ₀(x)
  rcases hst x with ⟨s, cs, hcs, -, hsv, hmax⟩ | ⟨hnone, hinit⟩
  · -- s is max_AR W_x(T), and it wrote v
    rw [hσ] at hsv
    have hst' : s ≠ t' := by
      intro h
      subst h
      exact hlive cs ⟨hcs.1, Or.inl hcs.2⟩
    have hW : (transactionOf (es ++ [n]) s).WritesVal x v :=
      writesVal_of_lastSetVal (((B4' hu (hnset s)).2 v).mpr hsv)
    refine Or.inr ⟨transactionOf (es ++ [n]) s, ⟨⟨⟨s, ⟨cs, List.mem_append_left _ hcs.1,
      by rw [hcs.2]; rfl⟩, rfl⟩, committed_of_eend (List.mem_append_left _ hcs.1) hcs.2,
      fun h => hst' (congrArg Transaction.txid h),
      Or.inl ⟨cs, n, ⟨List.mem_append_left _ hcs.1, Or.inl hcs.2⟩,
        ⟨List.mem_append_right _ (List.mem_singleton_self _), Or.inl hn⟩,
        OccursBefore.snoc_last hcs.1⟩, ⟨v, hW⟩⟩, ?_⟩, hW⟩
    -- every other committed writer U committed before s
    rintro U ⟨⟨u, -, rfl⟩, hUc, hUne, -, ⟨w, hUw⟩⟩
    obtain ⟨b, hb, hbl⟩ := eend_of_committed hUc
    have hb' := hold u b hb hbl (fun h => hUne (by rw [h]))
    have hU : HasSet es u x := ((B4' hu (hnset u)).1).mp (hasSet_of_writesVal hUw)
    rcases hmax u b ⟨hb', hbl⟩ hU with hbc | hba
    · subst hbc
      have hus : u = s := by
        have := hbl.symm.trans hcs.2
        cases this
        rfl
      exact Or.inl (by rw [hus])
    · exact Or.inr (Or.inl ⟨b, cs, ⟨List.mem_append_left _ hb', Or.inl hbl⟩,
        ⟨List.mem_append_left _ hcs.1, Or.inl hcs.2⟩, hba.snoc_mono⟩)
  · -- no committed writer of x, and v = σ(x) = σ₀(x)
    refine Or.inl ⟨?_, by rw [← hσ]; exact hinit⟩
    rintro ⟨U, ⟨u, -, rfl⟩, hUc, hUne, -, ⟨w, hUw⟩⟩
    obtain ⟨b, hb, hbl⟩ := eend_of_committed hUc
    have hb' := hold u b hb hbl (fun h => hUne (by rw [h]))
    exact hnone u b ⟨hb', hbl⟩ (((B4' hu (hnset u)).1).mp (hasSet_of_writesVal hUw))

-- Com ∪ {t}: n = end t. Old committed T by ext_old, t itself by ext_new.
theorem ext_commit {es : List Event} {n : Event} {t : TxId} {σ : Store} {Λ : Log}
    (hu : UniqueIds (es ++ [n])) (hn : n.label = .eend t)
    (hlive : ∀ a, ¬ Terminates es t a) (h : (hist es).ExtC)
    (hR : RLog es t Λ) (hok : KCasOk σ Λ) (hst : StoreInv es σ) :
    (hist (es ++ [n])).ExtC := by
  have hntx : n.label.tx = t := by rw [hn]; rfl
  have htn : ∀ a, ¬ Terminates es n.label.tx a := by rw [hntx]; exact hlive
  rintro T ⟨t', -, rfl⟩ hcom x v hread
  by_cases ht : t' = t
  · subst ht
    exact ext_new hu hn hlive hR hok hst x v hread
  · exact ext_old hu htn h (by rw [hntx]; exact ht) hcom x v hread

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

theorem ExtP.snoc {τ : Trace} {n : Event} (h : (hist (events τ ++ [n])).ExtC) :
    ExtP (τ ++ [.ev n]) := by
  unfold ExtP witness txsOfTrace
  rw [events_snoc_ev]
  exact h

-- begin. Com unchanged; the fresh tag has no terminator (F).
theorem ext_begin {τ : Trace} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .begin t⟩]))) (h : ExtP τ)
    (hF : ∀ e ∈ events τ, e.label.tx < t) :
    ExtP (τ ++ [.ev ⟨α, .begin t⟩]) := by
  simp only [events_snoc_ev] at hu
  refine ExtP.snoc (ext_noend hu (fun a ha => ?_) (by simp) h)
  have := hF a ha.1
  rw [ha.tx] at this
  simp [Label.tx] at this

-- Get-Log / Get-Mem. Com unchanged; t is live (T).
theorem ext_get {τ : Trace} {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : ExtP τ)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    ExtP (τ ++ [.ev ⟨α, .get l v t⟩]) := by
  simp only [events_snoc_ev] at hu
  exact ExtP.snoc (ext_noend hu hlive (by simp) h)

-- Set-Log / Set-Mem. Com unchanged; t is live (T).
theorem ext_set {τ : Trace} {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : ExtP τ)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    ExtP (τ ++ [.ev ⟨α, .set l v t⟩]) := by
  simp only [events_snoc_ev] at hu
  exact ExtP.snoc (ext_noend hu hlive (by simp) h)

-- KCas-Retry / Retry. Com unchanged; t is live (T).
theorem ext_retry {τ : Trace} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .retry t⟩]))) (h : ExtP τ)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    ExtP (τ ++ [.ev ⟨α, .retry t⟩]) := by
  simp only [events_snoc_ev] at hu
  exact ExtP.snoc (ext_noend hu hlive (by simp) h)

-- Commit. Com ∪ {t}; t's reads by R, KCasOk and Store.
theorem ext_end {τ : Trace} {α : EvId} {t : TxId} {σ : Store} {Λ : Log}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .eend t⟩]))) (h : ExtP τ)
    (hlive : ∀ a, ¬ Terminates (events τ) t a) (hR : RLog (events τ) t Λ)
    (hok : KCasOk σ Λ) (hst : StoreInv (events τ) σ) :
    ExtP (τ ++ [.ev ⟨α, .eend t⟩]) := by
  simp only [events_snoc_ev] at hu
  exact ExtP.snoc (ext_commit hu rfl hlive h hR hok hst)

-- Adm. no event.
theorem ext_adm {τ : Trace} (h : ExtP τ) : ExtP (τ ++ [.adm]) := by
  unfold ExtP witness txsOfTrace at *
  rw [events_snoc_adm]
  exact h

end Optimistic
