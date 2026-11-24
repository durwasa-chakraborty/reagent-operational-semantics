/-
  R: the log remembers what each live transaction read from memory. For every
  live `t` with log `Λ` and every external (first) read `get(x, v)@t`,
  `Λ(x) = (v, _)`.

  One step splits into two worlds, as for Cur:
    others' frame   another thread's log is untouched; the new event is not
                    one of its reads (no get, or a different tag by D), and
                    old reads keep their Ext status (B2)
    my frame        the stepping thread's own log

  The table (one line per rule) is the R field of `inv_ext`;
  the per-rule lemmas it calls are at the bottom of this file.
-/
import Optimistic.ExtConsistencyStore

namespace Optimistic

open Reagent (Loc TxId ThId EvId Expr update update_other)

/-! ## The invariant -/

-- R for one log: every external read `get(x, v)@t` in `es` has `Λ(x) = (v, _)`.
def RLog (es : List Event) (t : TxId) (Λ : Log) : Prop :=
  ∀ e x v, e ∈ es → e.label = .get x v t → IsExt es e → ∃ c, Λ x = some (v, c)

-- R for every live thread.
def ReadsInv (es : List Event) (θ : ThId → Option (TxId × Log × Expr)) : Prop :=
  ∀ i t Λ Ê, θ i = some (t, Λ, Ê) → RLog es t Λ

/-! ## Frame for one log -/

-- `n` is no read of `t`: old reads keep their Ext status (B2), so R carries over.
theorem RLog.frame {es : List Event} {n : Event} {t : TxId} {Λ : Log}
    (hu : UniqueIds (es ++ [n])) (hn : ∀ x v, n.label ≠ .get x v t)
    (h : RLog es t Λ) : RLog (es ++ [n]) t Λ := by
  intro e x v he hl hext
  rcases List.mem_append.mp he with he | he
  · exact h e x v he hl ((B2 hu he).mp hext)
  · rw [List.mem_singleton.mp he] at hl
    exact absurd hl (hn x v)

/-! ## Others' frame -/

-- `n` is no get: nobody's R changes.
theorem reads_noget {τ : Trace} {n : Event} {θ : ThId → Option (TxId × Log × Expr)}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hn : ∀ x v t, n.label ≠ .get x v t)
    (h : ReadsInv (events τ) θ) : ReadsInv (events (τ ++ [.ev n])) θ := by
  simp only [events_snoc_ev] at hu ⊢
  intro i t Λ Ê hi
  exact (h i t Λ Ê hi).frame hu (fun x v => hn x v t)

-- `n` is emitted by thread `i` running `t₀`: every other live thread `k` runs
-- a different tag (D), so `n` is none of its reads.
theorem reads_others {τ : Trace} {n : Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t₀ : TxId} {Λ₀ : Log} {Ê₀ : Expr}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (h : ReadsInv (events τ) θ)
    (hD : LiveDistinct θ) (hi : θ i = some (t₀, Λ₀, Ê₀)) (htag : n.label.tx = t₀) :
    ∀ k t Λ Ê, k ≠ i → θ k = some (t, Λ, Ê) → RLog (events (τ ++ [.ev n])) t Λ := by
  simp only [events_snoc_ev] at hu ⊢
  intro k t Λ Ê hki hk
  have hne : t ≠ t₀ := by
    intro heq
    subst heq
    exact hki (hD k i t Λ Λ₀ Ê Ê₀ hk hi)
  exact (h k t Λ Ê hk).frame hu (fun x v hv => hne (by rw [← htag, hv]; rfl))

/-! ## My frame -/

-- My log stays `Λ`: others as given, mine as given.
theorem reads_same {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Λ : Log} {Ê : Expr} (hi : θ i = some (t, Λ, Ê))
    (hothers : ∀ k t' Λ' Ê', k ≠ i → θ k = some (t', Λ', Ê') → RLog es t' Λ')
    (hmine : RLog es t Λ) : ReadsInv es θ := by
  intro k t' Λ' Ê' hk
  by_cases hki : k = i
  · subst hki
    rw [hi] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    exact hmine
  · exact hothers k t' Λ' Ê' hki hk

-- My log becomes `Λ₁`: others as given, mine as given.
theorem reads_mine {es : List Event} {θ : ThId → Option (TxId × Log × Expr)}
    {i : ThId} {t : TxId} {Λ₁ : Log} {Ê : Expr}
    (hothers : ∀ k t' Λ Ê', k ≠ i → θ k = some (t', Λ, Ê') → RLog es t' Λ)
    (hmine : RLog es t Λ₁) : ReadsInv es (update θ i (some (t, Λ₁, Ê))) := by
  intro k t' Λ Ê' hk
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨hki, hk⟩
  · obtain ⟨rfl, rfl, -⟩ := hv
    exact hmine
  · exact hothers k t' Λ Ê' hki hk

-- end / retry: my thread leaves.
theorem reads_leave {es : List Event} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    (h : ReadsInv es θ) : ReadsInv es (update θ i none) := by
  intro k t Λ Ê hk
  rcases update_eq_some hk with ⟨-, hv⟩ | ⟨-, hk⟩
  · cases hv
  · exact h k t Λ Ê hk

-- Get-Log at `l` with `Λ(l) = (o, c)`: the log is unchanged, and the new read
-- `get(l, c)@t` is fine. By Cur, either t set l (an earlier access, so the
-- read is not external) or `c = o` (so `Λ(l) = (c, _)`).
theorem mine_getLog {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {o c : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hR : RLog (events τ) t Λ)
    (hcur : ∀ x, CurVal (events τ) t Λ x) (hl : Λ l = some (o, c))
    (hn : n.label = .get l c t) : RLog (events (τ ++ [.ev n])) t Λ := by
  simp only [events_snoc_ev] at hu ⊢
  intro e x v he hle hext
  rcases List.mem_append.mp he with he | he
  · -- an old read: B2
    exact hR e x v he hle ((B2 hu he).mp hext)
  · -- the new read n = get(l, c)@t
    rw [List.mem_singleton.mp he] at hle hext
    rw [hn] at hle
    cases hle
    obtain ⟨-, hr⟩ := hcur l o c hl
    by_cases hs : HasSet (events τ) t l
    · -- t set l earlier: that set is an earlier access, so n is not external
      exfalso
      obtain ⟨a, ha, w, haw⟩ := hs
      obtain ⟨x', v', t', hlab, hno⟩ := hext
      rw [hn] at hlab
      cases hlab
      exact hno ⟨a, List.mem_append_left _ ha, by rw [haw]; rfl,
        by rw [haw]; simp [Label.accesses], OccursBefore.snoc_last ha⟩
    · -- t did not set l: c = o
      exact ⟨c, by rw [hl, hr hs]⟩

-- Get-Mem at `l`: my log gets `(v, v)` at `l`, which is right for the new read.
-- By L, t had no earlier read of `l`.
theorem mine_getMem_reads {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {v : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hR : RLog (events τ) t Λ)
    (hL : NoAccess (events τ) t l) (hn : n.label = .get l v t) :
    RLog (events (τ ++ [.ev n])) t (update Λ l (some (v, v))) := by
  simp only [events_snoc_ev] at hu ⊢
  intro e x w he hle hext
  by_cases hlx : l = x
  · -- at l: only the new read, which returns v
    subst hlx
    rcases List.mem_append.mp he with he | he
    · exfalso
      have := hL e he (by rw [hle]; rfl)
      rw [hle] at this
      simp [Label.accesses] at this
    · rw [List.mem_singleton.mp he, hn] at hle
      cases hle
      exact ⟨v, by simp [update]⟩
  · -- elsewhere: the log is unchanged, old reads by B2
    rw [update_other Λ l x _ hlx]
    rcases List.mem_append.mp he with he | he
    · exact hR e x w he hle ((B2 hu he).mp hext)
    · rw [List.mem_singleton.mp he, hn] at hle
      cases hle
      exact absurd rfl hlx

-- Set-Log at `l` with `Λ(l) = (o, c)`: my log gets `(o, v)`, keeping `o`.
theorem mine_setLog_reads {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc}
    {o c v : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hR : RLog (events τ) t Λ)
    (hl : Λ l = some (o, c)) (hn : n.label = .set l v t) :
    RLog (events (τ ++ [.ev n])) t (update Λ l (some (o, v))) := by
  simp only [events_snoc_ev] at hu ⊢
  intro e x w he hle hext
  rcases List.mem_append.mp he with he | he
  · obtain ⟨c', hc'⟩ := hR e x w he hle ((B2 hu he).mp hext)
    by_cases hlx : l = x
    · -- at l: the read value is o, and o is kept
      subst hlx
      rw [hl] at hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨rfl, -⟩ := hc'
      exact ⟨v, by simp [update]⟩
    · exact ⟨c', by rw [update_other Λ l x _ hlx]; exact hc'⟩
  · -- the new event is a set, not a read
    rw [List.mem_singleton.mp he, hn] at hle
    cases hle

-- Set-Mem at `l` with `Λ(l) = ⊥`: my log gets `(u, v)` at `l`. By L, t had
-- no earlier read of `l`, so there is nothing to remember there.
theorem mine_setMem_reads {τ : Trace} {n : Event} {t : TxId} {Λ : Log} {l : Loc} {u v : Nat}
    (hu : UniqueIds (events (τ ++ [.ev n]))) (hR : RLog (events τ) t Λ)
    (hL : NoAccess (events τ) t l) (hn : n.label = .set l v t) :
    RLog (events (τ ++ [.ev n])) t (update Λ l (some (u, v))) := by
  simp only [events_snoc_ev] at hu ⊢
  intro e x w he hle hext
  rcases List.mem_append.mp he with he | he
  · by_cases hlx : l = x
    · -- at l: no old read (L)
      subst hlx
      exfalso
      have := hL e he (by rw [hle]; rfl)
      rw [hle] at this
      simp [Label.accesses] at this
    · rw [update_other Λ l x _ hlx]
      exact hR e x w he hle ((B2 hu he).mp hext)
  · -- the new event is a set, not a read
    rw [List.mem_singleton.mp he, hn] at hle
    cases hle

/-! ## One lemma per rule (used by the table in `inv_ext`) -/

-- begin. mine: new empty log, and no event is tagged with the fresh `t` (F).
-- others: begin is no get.
theorem reads_begin {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId} {Ê : Expr}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .begin t⟩]))) (h : ReadsInv (events τ) θ)
    (hF : ∀ e ∈ events τ, e.label.tx < t) :
    ReadsInv (events (τ ++ [.ev ⟨α, .begin t⟩])) (update θ i (some (t, Log.empty, Ê))) := by
  have hall := reads_noget hu (by simp) h
  refine reads_mine (fun k t' Λ Ê' _ hk => hall k t' Λ Ê' hk) ?_
  simp only [events_snoc_ev]
  intro e x v he hle _
  rcases List.mem_append.mp he with he | he
  · have := hF e he
    rw [hle] at this
    simp [Label.tx] at this
  · rw [List.mem_singleton.mp he] at hle
    cases hle

-- Get-Log. mine: log unchanged, new read checked by Cur. others: other tag.
theorem reads_getLog {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {o v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : ReadsInv (events τ) θ)
    (hD : LiveDistinct θ) (hcur : Cur (events τ) θ)
    (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = some (o, v)) :
    ReadsInv (events (τ ++ [.ev ⟨α, .get l v t⟩])) θ :=
  reads_same hi (reads_others hu h hD hi rfl)
    (mine_getLog hu (h _ _ _ _ hi) (hcur _ _ _ _ hi) hl rfl)

-- Get-Mem. mine: (v, v) at l, the new read. others: other tag.
theorem reads_getMem {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .get l v t⟩]))) (h : ReadsInv (events τ) θ)
    (hD : LiveDistinct θ) (hL : LogMirrors (events τ) θ)
    (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = none) :
    ReadsInv (events (τ ++ [.ev ⟨α, .get l v t⟩]))
      (update θ i (some (t, update Λ l (some (v, v)), Ê))) :=
  reads_mine (reads_others hu h hD hi rfl)
    (mine_getMem_reads hu (h _ _ _ _ hi) ((hL _ _ _ _ hi _).1 hl) rfl)

-- Set-Log. mine: (o, v) at l keeps o. others: set is no get.
theorem reads_setLog {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {o c v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : ReadsInv (events τ) θ)
    (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = some (o, c)) :
    ReadsInv (events (τ ++ [.ev ⟨α, .set l v t⟩]))
      (update θ i (some (t, update Λ l (some (o, v)), Ê))) :=
  reads_mine (fun k t' Λ' Ê' _ hk => reads_noget hu (by simp) h k t' Λ' Ê' hk)
    (mine_setLog_reads hu (h _ _ _ _ hi) hl rfl)

-- Set-Mem. mine: (u, v) at l, never read before (L). others: set is no get.
theorem reads_setMem {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {t : TxId} {Λ : Log} {Ê : Expr} {l : Loc} {u v : Nat} {α : EvId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .set l v t⟩]))) (h : ReadsInv (events τ) θ)
    (hL : LogMirrors (events τ) θ) (hi : θ i = some (t, Λ, Ê)) (hl : Λ l = none) :
    ReadsInv (events (τ ++ [.ev ⟨α, .set l v t⟩]))
      (update θ i (some (t, update Λ l (some (u, v)), Ê))) :=
  reads_mine (fun k t' Λ' Ê' _ hk => reads_noget hu (by simp) h k t' Λ' Ê' hk)
    (mine_setMem_reads hu (h _ _ _ _ hi) ((hL _ _ _ _ hi _).1 hl) rfl)

-- Commit. mine: leaves. others: end is no get.
theorem reads_commit {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .eend t⟩]))) (h : ReadsInv (events τ) θ) :
    ReadsInv (events (τ ++ [.ev ⟨α, .eend t⟩])) (update θ i none) :=
  reads_leave (reads_noget hu (by simp) h)

-- KCas-Retry / Retry. mine: leaves. others: retry is no get.
theorem reads_retry {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)} {i : ThId}
    {α : EvId} {t : TxId}
    (hu : UniqueIds (events (τ ++ [.ev ⟨α, .retry t⟩]))) (h : ReadsInv (events τ) θ) :
    ReadsInv (events (τ ++ [.ev ⟨α, .retry t⟩])) (update θ i none) :=
  reads_leave (reads_noget hu (by simp) h)

-- Adm. no event, no log changes.
theorem reads_adm {τ : Trace} {θ : ThId → Option (TxId × Log × Expr)}
    (h : ReadsInv (events τ) θ) : ReadsInv (events (τ ++ [.adm])) θ := by
  sorry

end Optimistic
