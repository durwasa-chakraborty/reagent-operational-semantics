/-
  U (part (b)): every external read of every transaction, committed or not,
  returns the value of the latest writer committed before it, or σ₀(x).
  `Ext_u` is U restricted to uncommitted transactions.

  U is stated on the event list (`UInv`) and translated to the history once, at
  the end (`extOp_of_uinv`). This is the design pattern from prompt.org: the
  step never rebuilds transactions.

  One step `es' = es ++ [n]` splits into two worlds:
    old reads       keep their obligation: Ext status (B2), W_e and the latest
                    writer (B1, B4). n comes last, so it is never before an old
                    read, and tag(n) has no terminator in es (T or F).
    the new read    only Get-Mem makes one: v = σ(l), the latest committed
                    value (Store). A Get-Log read is never external (L⁻).

  The table (one line per rule) is the U field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtConsistencyLogBack

namespace Optimistic

open Reagent (Loc TxId ThId EvId Expr Store)

/-! ## The invariant (on the event list) -/

-- `s ∈ W_e`, with commit event `c`: `s` committed before `e`, and `s` set `x`.
def WVis (es : List Event) (e : Event) (x : Loc) (s : TxId) (c : Event) : Prop :=
  CommitEv es s c ∧ OccursBefore es c e ∧ HasSet es s x

-- `e`'s obligation: `v` is the last set of the latest writer in `W_e`, or
-- `σ₀(x)` if `W_e = ∅`.
def ReadOk (es : List Event) (e : Event) (x : Loc) (v : Nat) : Prop :=
  (∃ s c, WVis es e x s c ∧ LastSetVal es s x v ∧
      ∀ s' c', WVis es e x s' c' → c' = c ∨ OccursBefore es c' c)
  ∨ ((∀ s c, ¬ WVis es e x s c) ∧ v = Store.init_store x)

-- U: every external read in `es` is ReadOk.
def UInv (es : List Event) : Prop :=
  ∀ e x v t, e ∈ es → e.label = .get x v t → IsExt es e → ReadOk es e x v

/-! ## Old reads keep their obligation -/

-- `W_e` is unchanged for an old read `e`.
theorem WVis.snoc_iff {es : List Event} {n e : Event} {x : Loc} {s : TxId} {c : Event}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a) (he : e ∈ es) :
    WVis (es ++ [n]) e x s c ↔ WVis es e x s c := by
  constructor
  · rintro ⟨⟨hc, hcl⟩, hce, hs⟩
    -- c comes before the old e, so c is not n
    have hc' : c ∈ es := by
      rcases List.mem_append.mp hc with hc | hc
      · exact hc
      · rw [List.mem_singleton.mp hc] at hce
        exact absurd hce (not_occursBefore_snoc hu he)
    have hsn : s ≠ n.label.tx := ne_tag_of_committed htn ⟨c, hc', hcl⟩
    exact ⟨⟨hc', hcl⟩, (B1 hu hc' he).mp hce, (B4 hu hsn).1.mp hs⟩
  · rintro ⟨⟨hc, hcl⟩, hce, hs⟩
    have hsn : s ≠ n.label.tx := ne_tag_of_committed htn ⟨c, hc, hcl⟩
    exact ⟨⟨List.mem_append_left _ hc, hcl⟩, hce.snoc_mono, (B4 hu hsn).1.mpr hs⟩

-- An old read's obligation carries over.
theorem ReadOk.snoc {es : List Event} {n e : Event} {x : Loc} {v : Nat}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a) (he : e ∈ es)
    (h : ReadOk es e x v) : ReadOk (es ++ [n]) e x v := by
  have hW := fun s c => WVis.snoc_iff (x := x) (s := s) (c := c) hu htn he
  rcases h with ⟨s, c, hsc, hv, hmax⟩ | ⟨hnone, hinit⟩
  · -- the same latest writer, with the same last set (B4)
    have hsn : s ≠ n.label.tx := ne_tag_of_committed htn ⟨c, hsc.1.1, hsc.1.2⟩
    refine Or.inl ⟨s, c, (hW s c).mpr hsc, ((B4 hu hsn).2 v).mpr hv, fun s' c' h' => ?_⟩
    rcases hmax s' c' ((hW s' c').mp h') with heq | hlt
    · exact Or.inl heq
    · exact Or.inr hlt.snoc_mono
  · -- still no writer
    exact Or.inr ⟨fun s c h' => hnone s c ((hW s c).mp h'), hinit⟩

-- Every old external read: Ext status by B2, obligation by ReadOk.snoc.
theorem uinv_old {es : List Event} {n e : Event} {x : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a)
    (h : UInv es) (he : e ∈ es) (hle : e.label = .get x v t) (hext : IsExt (es ++ [n]) e) :
    ReadOk (es ++ [n]) e x v :=
  (h e x v t he hle ((B2 hu he).mp hext)).snoc hu htn he

/-! ## The new read -/

-- n is no get: no new read.
theorem uinv_noget {es : List Event} {n : Event}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a)
    (hn : ∀ x v t, n.label ≠ .get x v t) (h : UInv es) : UInv (es ++ [n]) := by
  intro e x v t he hle hext
  rcases List.mem_append.mp he with he | he
  · exact uinv_old hu htn h he hle hext
  · rw [List.mem_singleton.mp he] at hle
    exact absurd hle (hn x v t)

-- Get-Log at `l`: the new read is not external, since `Λ(l) ≠ ⊥` and so `t`
-- already accessed `l` (L⁻).
theorem uinv_getLog {es : List Event} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {o c : Nat}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a)
    (hLB : LogBackAt es t Λ) (hl : Λ l = some (o, c)) (hn : n.label = .get l c t)
    (h : UInv es) : UInv (es ++ [n]) := by
  intro e x v t' he hle hext
  rcases List.mem_append.mp he with he | he
  · exact uinv_old hu htn h he hle hext
  · exfalso
    rw [List.mem_singleton.mp he] at hext
    obtain ⟨x', v', t'', hlab, hno⟩ := hext
    rw [hn] at hlab
    cases hlab
    obtain ⟨a, ha, hat, hacc⟩ := hLB l (by simp [hl])
    exact hno ⟨a, List.mem_append_left _ ha, hat, hacc, OccursBefore.snoc_last ha⟩

-- Get-Mem at `l`: the new read returns `σ(l)`, and Store says that is the last
-- set of the latest committed writer of `l`, or `σ₀(l)`. Every commit in `es`
-- comes before `n`.
theorem readOk_new {es : List Event} {n : Event} {t : TxId} {σ : Store} {l : Loc} {v : Nat}
    (hu : UniqueIds (es ++ [n])) (hn : n.label = .get l v t)
    (hst : StoreSpec es σ l) (hσ : σ l = v) : ReadOk (es ++ [n]) n l v := by
  have hnset : ∀ s w, n.label ≠ .set l w s := by
    intro s w h
    rw [hn] at h
    cases h
  -- W_n in es' is the committed writers of l in es
  have hold : ∀ s c, WVis (es ++ [n]) n l s c → CommitEv es s c ∧ HasSet es s l := by
    rintro s c ⟨⟨hc, hcl⟩, -, hs⟩
    have hc' : c ∈ es := by
      rcases List.mem_append.mp hc with hc | hc
      · exact hc
      · rw [List.mem_singleton.mp hc, hn] at hcl
        cases hcl
    exact ⟨⟨hc', hcl⟩, (B4' hu (hnset s)).1.mp hs⟩
  have hnew : ∀ s c, CommitEv es s c → HasSet es s l → WVis (es ++ [n]) n l s c :=
    fun s c hc hs => ⟨hc.snoc, OccursBefore.snoc_last hc.1, (B4' hu (hnset s)).1.mpr hs⟩
  rcases hst with ⟨s, c, hc, hs, hv, hmax⟩ | ⟨hnone, hinit⟩
  · -- the latest committed writer s wrote v
    rw [hσ] at hv
    refine Or.inl ⟨s, c, hnew s c hc hs, ((B4' hu (hnset s)).2 v).mpr hv, fun s' c' h' => ?_⟩
    obtain ⟨hc', hs'⟩ := hold s' c' h'
    rcases hmax s' c' hc' hs' with heq | hlt
    · exact Or.inl heq
    · exact Or.inr hlt.snoc_mono
  · -- no committed writer, and v = σ₀(l)
    refine Or.inr ⟨fun s c h' => ?_, by rw [← hσ]; exact hinit⟩
    obtain ⟨hc', hs'⟩ := hold s c h'
    exact hnone s c hc' hs'

theorem uinv_getMem {es : List Event} {n : Event} {t : TxId} {σ : Store} {l : Loc} {v : Nat}
    (hu : UniqueIds (es ++ [n])) (htn : ∀ a, ¬ Terminates es n.label.tx a)
    (hst : StoreSpec es σ l) (hσ : σ l = v) (hn : n.label = .get l v t)
    (h : UInv es) : UInv (es ++ [n]) := by
  intro e x w t' he hle hext
  rcases List.mem_append.mp he with he' | he'
  · exact uinv_old hu htn h he' hle hext
  · rw [List.mem_singleton.mp he'] at hle ⊢
    rw [hn] at hle
    cases hle
    exact readOk_new hu hn hst hσ

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

-- begin. new read: none. old reads: the fresh tag has no terminator (F).
theorem u_begin {τ : Trace} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .begin t⟩]))) (h : UInv (events τ))
    (hF : ∀ e ∈ events τ, e.label.tx < t) :
    UInv (events (τ ++ [.ev ⟨α, .begin t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  refine uinv_noget hu (fun a ha => ?_) (by simp) h
  have := hF a ha.1
  rw [ha.tx] at this
  simp [Label.tx] at this

-- Get-Log. new read: not external (L⁻). old reads: t live (T).
theorem u_getLog {τ : Trace} {α : EvId} {l : Loc} {v o : Nat} {t : TxId} {Λ : Log}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : UInv (events τ))
    (hlive : ∀ a, ¬ Terminates (events τ) t a) (hLB : LogBackAt (events τ) t Λ)
    (hl : Λ l = some (o, v)) :
    UInv (events (τ ++ [.ev ⟨α, .get l v t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  exact uinv_getLog hu hlive hLB hl rfl h

-- Get-Mem. new read: σ(l) is the latest committed value (Store). old reads: t live (T).
theorem u_getMem {τ : Trace} {α : EvId} {l : Loc} {v : Nat} {t : TxId} {σ : Store}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : UInv (events τ))
    (hlive : ∀ a, ¬ Terminates (events τ) t a) (hst : StoreInv (events τ) σ)
    (hσ : σ l = v) :
    UInv (events (τ ++ [.ev ⟨α, .get l v t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  exact uinv_getMem hu hlive (hst l) hσ rfl h

-- Set-Log / Set-Mem. new read: none. old reads: t live (T).
theorem u_set {τ : Trace} {α : EvId} {l : Loc} {v : Nat} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : UInv (events τ))
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    UInv (events (τ ++ [.ev ⟨α, .set l v t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  exact uinv_noget hu hlive (by simp) h

-- Commit. new read: none; U is over all T, so committing adds no obligation.
-- old reads: t live (T).
theorem u_commit {τ : Trace} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .eend t⟩]))) (h : UInv (events τ))
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    UInv (events (τ ++ [.ev ⟨α, .eend t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  exact uinv_noget hu hlive (by simp) h

-- KCas-Retry / Retry. new read: none. old reads: t live (T).
theorem u_retry {τ : Trace} {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .retry t⟩]))) (h : UInv (events τ))
    (hlive : ∀ a, ¬ Terminates (events τ) t a) :
    UInv (events (τ ++ [.ev ⟨α, .retry t⟩])) := by
  simp only [events_snoc_ev] at hu ⊢
  exact uinv_noget hu hlive (by simp) h

-- Adm. no event.
theorem u_adm {τ : Trace} (h : UInv (events τ)) : UInv (events (τ ++ [.adm])) := by
  sorry

/-! ## Projection: U on the list gives Ext_op on the history -/

-- The one place the list is translated to the history: W_e on the list is
-- W_e = VIS⁻¹(e) ∩ writers of x, and the latest commit is max_AR.
theorem extOp_of_uinv {es : List Event} (h : UInv es) : (hist es).ExtOp (visOf es) := by
  intro T hT x v ⟨e, heE⟩ ⟨t', hle⟩ hnoprior
  obtain ⟨t, -, rfl⟩ := hT
  replace hle : e.label = .get x v t' := hle
  -- e is external on the list
  have hext : IsExt es e := ⟨x, v, t', hle, fun ⟨a, ha, hat, hacc, hae⟩ => by
    have htt : t' = t := by
      have het : e.label.tx = t := heE.2.1
      rw [hle] at het
      exact het
    subst htt
    exact hnoprior ⟨⟨a, ha, hat, isAccess_of_accesses hacc⟩, hae, hacc⟩⟩
  rcases h e x v t' heE.1 hle hext with ⟨s, c, ⟨hc, hce, hs⟩, hv, hmax⟩ | ⟨hnone, hinit⟩
  · -- S = transactionOf es s is max_AR W_e, and it wrote v
    refine Or.inr ⟨transactionOf es s, ⟨⟨⟨s, ⟨c, hc.1, by rw [hc.2]; rfl⟩, rfl⟩,
      ⟨committed_of_eend hc.1 hc.2, c, hc.1, hc.2, hce⟩,
      ⟨v, writesVal_of_lastSetVal hv⟩⟩, ?_⟩, writesVal_of_lastSetVal hv⟩
    rintro U ⟨⟨u, -, rfl⟩, ⟨-, c', hc', hcl', hc'e⟩, w, hw⟩
    rcases hmax u c' ⟨⟨hc', hcl'⟩, hc'e, hasSet_of_writesVal hw⟩ with hcc | hlt
    · -- the same commit event, so the same transaction
      subst hcc
      have hus : u = s := by
        have := hcl'.symm.trans hc.2
        cases this
        rfl
      exact Or.inl (by rw [hus])
    · -- an earlier commit: AR's first clause
      exact Or.inr (Or.inl ⟨c', c, ⟨hc', Or.inl hcl'⟩, ⟨hc.1, Or.inl hc.2⟩, hlt⟩)
  · -- W_e = ∅ and v = σ₀(x)
    refine Or.inl ⟨?_, hinit⟩
    rintro ⟨S, ⟨s, -, rfl⟩, ⟨-, c, hc, hcl, hce⟩, w, hw⟩
    exact hnone s c ⟨⟨hc, hcl⟩, hce, hasSet_of_writesVal hw⟩

end Optimistic
