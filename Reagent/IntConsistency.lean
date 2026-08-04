/-
  Internal consistency for Reagent (Section "Internal consistency").

  Every trace of the operational semantics satisfies `Int`: for every read
  `get(x,n)@t`, if the same transaction already accessed `x`, the
  program-order-latest such access carries `n`.

  The proof is a store-tracking induction. Within a transaction the store on `x`
  equals the value of the latest earlier access to `x`, because the single lock
  isolates the transaction and, since `retry` releases the lock as it rolls the
  store back, no rollback ever happens *inside* a live transaction.

  Administrative steps appear in traces but are not events, so they add nothing
  to a transaction's `E` and disturb neither the store nor `θ` — they are
  carried through the induction as no-ops.
-/
import Reagent.Trace

namespace Reagent

/-! ## Internal consistency (§Internal consistency) -/

/-- `HEvent_x`: the label is a `get` or `set` on `x`. -/
def Label.accesses (x : Loc) : Label → Bool
  | .get l _ _ => l == x
  | .set l _ _ => l == x
  | _          => false

/-- The value a `get` or `set` carries; `none` otherwise. -/
def Label.accessVal : Label → Option Nat
  | .get _ v _ => some v
  | .set _ v _ => some v
  | _          => none

/-- `po⁻¹(e) ∩ HEvent_x`: the events of `T` that `po`-precede `e` and access `x`. -/
def Transaction.priorAccesses (T : Transaction) (e : Event) (x : Loc) : List Event :=
  T.events.filter (fun a => decide (a.id < e.id) && a.label.accesses x)

/-- `max_po(po⁻¹(e) ∩ HEvent_x)`; `none` exactly when that set is empty. -/
def Transaction.maxPriorAccess (T : Transaction) (e : Event) (x : Loc) : Option Event :=
  (T.priorAccesses e x).reverse.head?

/-- Internal consistency for a single transaction:

`∀ e ∈ E. ∀ x n. (e = (_, get(x,n)) ∧ po⁻¹(e) ∩ HEvent_x ≠ ∅)
   ⟹ max_po(po⁻¹(e) ∩ HEvent_x) = (_, _(x,n))`

The non-emptiness premise is carried by `maxPriorAccess … = some a`: on an empty
set `maxPriorAccess` is `none` and the statement is vacuous. The conclusion
`(_, _(x,n))` is spelled out as its two parts — the event accesses `x`, and the
value it carries is `n`. -/
def Transaction.Int (T : Transaction) : Prop :=
  ∀ e ∈ T.events, ∀ x n t, e.label = .get x n t →
    ∀ a, T.maxPriorAccess e x = some a →
      a.label.accesses x = true ∧ a.label.accessVal = some n

/-- `Int` for a history, ranging over *every* transaction of the trace,
committed or not — committedness never enters (§Internal consistency). -/
def History.Int (H : History) : Prop := ∀ T ∈ H.txs, T.Int

/-! ### Trace-level machinery for the proof -/

/-- The `t`-tagged accesses to `x` in `ℓs`, in trace order. -/
def accessesOf (t : TxId) (x : Loc) (ℓs : List TLabel) : List Event :=
  (traceEvents ℓs).filter (fun a => a.label.tx == t && a.label.accesses x)

/-- The value of the `po`-last `t`-tagged access to `x` in `ℓs`. -/
def lastAccessVal (t : TxId) (x : Loc) (ℓs : List TLabel) : Option Nat :=
  ((accessesOf t x ℓs).reverse.head?).bind (fun a => a.label.accessVal)

/-! Extending a trace by one label: a transition label contributes one event, at
position `|ℓs|`; an administrative step contributes none, though it still
advances the position counter. -/

theorem traceEventsFrom_append_ev (s : Nat) (ℓs : List TLabel) (ℓ : Label) :
    traceEventsFrom s (ℓs ++ [.ev ℓ])
      = traceEventsFrom s ℓs ++ [⟨s + ℓs.length, ℓ⟩] := by
  induction ℓs generalizing s with
  | nil => simp [traceEventsFrom]
  | cons a as ih =>
    have hs : s + 1 + as.length = s + (as.length + 1) := by omega
    cases a with
    | adm  => simp [traceEventsFrom, ih (s + 1), hs]
    | ev _ => simp [traceEventsFrom, ih (s + 1), hs]

theorem traceEventsFrom_append_adm (s : Nat) (ℓs : List TLabel) :
    traceEventsFrom s (ℓs ++ [.adm]) = traceEventsFrom s ℓs := by
  induction ℓs generalizing s with
  | nil => simp [traceEventsFrom]
  | cons a as ih =>
    cases a with
    | adm  => simp [traceEventsFrom, ih (s + 1)]
    | ev _ => simp [traceEventsFrom, ih (s + 1)]

theorem traceEvents_append_ev (ℓs : List TLabel) (ℓ : Label) :
    traceEvents (ℓs ++ [.ev ℓ]) = traceEvents ℓs ++ [⟨ℓs.length, ℓ⟩] := by
  simpa [traceEvents] using traceEventsFrom_append_ev 0 ℓs ℓ

theorem traceEvents_append_adm (ℓs : List TLabel) :
    traceEvents (ℓs ++ [.adm]) = traceEvents ℓs :=
  traceEventsFrom_append_adm 0 ℓs

theorem id_lt_of_mem_traceEventsFrom {s : Nat} {ℓs : List TLabel} {e : Event}
    (h : e ∈ traceEventsFrom s ℓs) : e.id < s + ℓs.length := by
  induction ℓs generalizing s with
  | nil => cases h
  | cons a as ih =>
    cases a with
    | adm => have := ih h; simp; omega
    | ev _ =>
      cases h with
      | head => simp
      | tail _ h => have := ih h; simp; omega

theorem id_lt_of_mem_traceEvents {ℓs : List TLabel} {e : Event}
    (h : e ∈ traceEvents ℓs) : e.id < ℓs.length := by
  simpa using id_lt_of_mem_traceEventsFrom (s := 0) h

theorem accessesOf_append_ev (t : TxId) (x : Loc) (ℓs : List TLabel) (ℓ : Label) :
    accessesOf t x (ℓs ++ [.ev ℓ]) =
      accessesOf t x ℓs ++
        (if ℓ.tx == t && ℓ.accesses x then [(⟨ℓs.length, ℓ⟩ : Event)] else []) := by
  simp only [accessesOf, traceEvents_append_ev, List.filter_append]
  congr 1
  by_cases h : (ℓ.tx == t && ℓ.accesses x) = true <;> simp [h]

theorem accessesOf_append_adm (t : TxId) (x : Loc) (ℓs : List TLabel) :
    accessesOf t x (ℓs ++ [.adm]) = accessesOf t x ℓs := by
  simp only [accessesOf, traceEvents_append_adm]

theorem lastAccessVal_append_of_access {t : TxId} {x : Loc} {ℓs : List TLabel}
    {ℓ : Label} (h : (ℓ.tx == t && ℓ.accesses x) = true) :
    lastAccessVal t x (ℓs ++ [.ev ℓ]) = ℓ.accessVal := by
  simp [lastAccessVal, accessesOf_append_ev, h]

theorem lastAccessVal_append_of_not_access {t : TxId} {x : Loc} {ℓs : List TLabel}
    {ℓ : Label} (h : (ℓ.tx == t && ℓ.accesses x) = false) :
    lastAccessVal t x (ℓs ++ [.ev ℓ]) = lastAccessVal t x ℓs := by
  simp [lastAccessVal, accessesOf_append_ev, h]

/-- An administrative step leaves the accesses, and so the last access value,
untouched. -/
theorem lastAccessVal_append_adm (t : TxId) (x : Loc) (ℓs : List TLabel) :
    lastAccessVal t x (ℓs ++ [.adm]) = lastAccessVal t x ℓs := by
  simp [lastAccessVal, accessesOf_append_adm]

/-- If no event of `ℓs` is tagged `t`, that transaction has no accesses. -/
theorem accessesOf_eq_nil {t : TxId} {x : Loc} {ℓs : List TLabel}
    (h : ∀ e ∈ traceEvents ℓs, e.label.tx ≠ t) : accessesOf t x ℓs = [] := by
  simp only [accessesOf, List.filter_eq_nil_iff]
  intro a ha
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro htx
  exact absurd htx (h _ ha)

theorem lastAccessVal_eq_none {t : TxId} {x : Loc} {ℓs : List TLabel}
    (h : ∀ e ∈ traceEvents ℓs, e.label.tx ≠ t) : lastAccessVal t x ℓs = none := by
  simp [lastAccessVal, accessesOf_eq_nil h]

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

/-- Every transaction id occurring in the trace so far, and the live one, lies
below `nextTx`. This is what makes `Begin`'s minted id genuinely fresh. -/
theorem inv_nextTx {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    (∀ e ∈ traceEvents ℓs, e.label.tx < C.nextTx) ∧
      (∀ t, C.activeTx = some t → t < C.nextTx) := by
  refine Trace.reverseRecOn (motive := fun ℓs C =>
      (∀ e ∈ traceEvents ℓs, e.label.tx < C.nextTx) ∧
        (∀ t, C.activeTx = some t → t < C.nextTx))
    ⟨by simp [traceEvents, traceEventsFrom], by simp [initConfig]⟩ ?_ h
  rintro ls C ℓ C' _ ⟨ih1, ih2⟩ hstep
  cases hstep with
  | @get i l v t K he hl ht hv =>
    refine ⟨fun e he' => ?_, ih2⟩
    rw [traceEvents_append_ev] at he'
    rcases List.mem_append.mp he' with h' | h'
    · exact ih1 _ h'
    · simp at h'; subst h'; exact ih2 _ ht
  | @set i l v t K he hl ht =>
    refine ⟨fun e he' => ?_, ih2⟩
    rw [traceEvents_append_ev] at he'
    rcases List.mem_append.mp he' with h' | h'
    · exact ih1 _ h'
    · simp at h'; subst h'; exact ih2 _ ht
  | @eend i t K he hl ht =>
    refine ⟨fun e he' => ?_, by simp⟩
    rw [traceEvents_append_ev] at he'
    rcases List.mem_append.mp he' with h' | h'
    · exact ih1 _ h'
    · simp at h'; subst h'; exact ih2 _ ht
  | @retry i t K he hl ht =>
    refine ⟨fun e he' => ?_, by simp⟩
    rw [traceEvents_append_ev] at he'
    rcases List.mem_append.mp he' with h' | h'
    · exact ih1 _ h'
    · simp at h'; subst h'; exact ih2 _ ht
  | @begin i eb K he hl =>
    refine ⟨fun e he' => ?_, ?_⟩
    · rw [traceEvents_append_ev] at he'
      rcases List.mem_append.mp he' with h' | h'
      · exact Nat.lt_succ_of_lt (ih1 _ h')
      · simp at h'; subst h'; exact Nat.lt_succ_self _
    · intro t' ht'
      have : C.nextTx = t' := Option.some.inj ht'
      subst this
      exact Nat.lt_succ_self _
  | @adm i r eb K he hloc =>
    -- no event is added, and neither `nextTx` nor `θ` moves
    refine ⟨fun e he' => ?_, ih2⟩
    rw [traceEvents_append_adm] at he'
    exact ih1 _ he'

/-- The store agrees with the `po`-last access made by the *live* transaction.
This is the semantic content of `Int`: a `get` reads what its own transaction
last left at that location. -/
theorem inv_store {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ t, C.activeTx = some t → ∀ x v, lastAccessVal t x ℓs = some v → C.store x = v := by
  refine Trace.reverseRecOn (motive := fun ℓs C =>
      ∀ t, C.activeTx = some t → ∀ x v, lastAccessVal t x ℓs = some v → C.store x = v)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C ℓ C' hrun ih hstep
  cases hstep with
  | @get i l v t K he hl ht hv =>
    intro t' ht' x v' hv'
    have ht2 : C.activeTx = some t' := ht'
    rw [ht] at ht2
    have htt : t = t' := Option.some.inj ht2
    subst htt
    show C.store x = v'
    by_cases hlx : l = x
    · subst hlx
      rw [lastAccessVal_append_of_access (by simp [Label.tx, Label.accesses])] at hv'
      simp only [Label.accessVal, Option.some.injEq] at hv'
      subst hv'
      exact hv
    · rw [lastAccessVal_append_of_not_access
        (by simp [Label.tx, Label.accesses, hlx])] at hv'
      exact ih _ ht x v' hv'
  | @set i l v t K he hl ht =>
    intro t' ht' x v' hv'
    have ht2 : C.activeTx = some t' := ht'
    rw [ht] at ht2
    have htt : t = t' := Option.some.inj ht2
    subst htt
    show update C.store l v x = v'
    by_cases hlx : l = x
    · subst hlx
      rw [lastAccessVal_append_of_access (by simp [Label.tx, Label.accesses])] at hv'
      simp only [Label.accessVal, Option.some.injEq] at hv'
      subst hv'
      simp [update]
    · rw [lastAccessVal_append_of_not_access
        (by simp [Label.tx, Label.accesses, hlx])] at hv'
      rw [update, if_neg (fun hc => hlx hc.symm)]
      exact ih _ ht x v' hv'
  | @begin i eb K he hl =>
    intro t' ht' x v' hv'
    have : C.nextTx = t' := Option.some.inj ht'
    subst this
    rw [lastAccessVal_append_of_not_access (by simp [Label.accesses])] at hv'
    rw [lastAccessVal_eq_none
      (fun e he' => Nat.ne_of_lt ((inv_nextTx hrun).1 _ he'))] at hv'
    exact absurd hv' (by simp)
  | @eend i t K he hl ht =>
    intro t' ht' x v' hv'
    exact absurd ht' (by simp)
  | @retry i t K he hl ht =>
    -- `Retry` rolls the store back, but it clears `θ` in the same step, so no
    -- live transaction is left for the invariant to constrain
    intro t' ht' x v' hv'
    exact absurd ht' (by simp)
  | @adm i r eb K he hloc =>
    -- an administrative step touches neither the store nor `θ`, and adds no event
    intro t' ht' x v' hv'
    rw [lastAccessVal_append_adm] at hv'
    exact ih t' ht' x v' hv'

@[simp] theorem transactionOf_events (ℓs : List TLabel) (t : TxId) :
    (transactionOf ℓs t).events
      = (traceEvents ℓs).filter (fun e => e.label.tx == t) := rfl

theorem Transaction.mem_of_maxPriorAccess {T : Transaction} {e a : Event} {x : Loc}
    (h : T.maxPriorAccess e x = some a) : a ∈ T.priorAccesses e x :=
  List.mem_reverse.mp (head?_mem h)

theorem Transaction.accesses_of_maxPriorAccess {T : Transaction} {e a : Event}
    {x : Loc} (h : T.maxPriorAccess e x = some a) : a.label.accesses x = true := by
  have hm := List.mem_filter.mp (mem_of_maxPriorAccess h)
  simpa using (Bool.and_eq_true _ _ |>.mp hm.2).2

/-- An event that accesses a location carries a value. -/
theorem accessVal_isSome {ℓ : Label} {x : Loc} (h : ℓ.accesses x = true) :
    ∃ v, ℓ.accessVal = some v := by
  cases ℓ with
  | begin _   => simp [Label.accesses] at h
  | eend _    => simp [Label.accesses] at h
  | retry _   => simp [Label.accesses] at h
  | get l v t => exact ⟨v, rfl⟩
  | set l v t => exact ⟨v, rfl⟩

/-- `po⁻¹(e) ∩ HEvent_x` as a single filter over the trace's events. -/
theorem priorAccesses_eq (L : List TLabel) (t : TxId) (e : Event) (x : Loc) :
    (transactionOf L t).priorAccesses e x
      = (traceEvents L).filter
          (fun a => decide (a.id < e.id) && a.label.accesses x && (a.label.tx == t)) := by
  simp only [Transaction.priorAccesses, transactionOf_events, List.filter_filter]

/-- Events already in `ls` keep their prior-access set when a transition label is
appended. -/
theorem priorAccesses_append_of_lt {ls : List TLabel} {ℓ : Label} {t : TxId}
    {e : Event} {x : Loc} (hlt : e.id < ls.length) :
    (transactionOf (ls ++ [.ev ℓ]) t).priorAccesses e x
      = (transactionOf ls t).priorAccesses e x := by
  rw [priorAccesses_eq, priorAccesses_eq, traceEvents_append_ev, List.filter_append]
  have hne : ¬ (ls.length < e.id) := Nat.not_lt.mpr (Nat.le_of_lt hlt)
  simp [hne]

/-- An administrative step changes no prior-access set at all — it is not an
event, so it never enters `po⁻¹(e) ∩ HEvent_x`. -/
theorem priorAccesses_append_adm (ls : List TLabel) (t : TxId) (e : Event) (x : Loc) :
    (transactionOf (ls ++ [.adm]) t).priorAccesses e x
      = (transactionOf ls t).priorAccesses e x := by
  rw [priorAccesses_eq, priorAccesses_eq, traceEvents_append_adm]

/-- The prior accesses of a *newly appended* `get` are exactly that
transaction's accesses to `x` in the trace so far. -/
theorem priorAccesses_new (ls : List TLabel) (ℓ : Label) (t : TxId) (x : Loc) :
    (transactionOf (ls ++ [.ev ℓ]) t).priorAccesses ⟨ls.length, ℓ⟩ x
      = accessesOf t x ls := by
  rw [priorAccesses_eq, traceEvents_append_ev, List.filter_append]
  have hnil : List.filter
      (fun a : Event => decide (a.id < (⟨ls.length, ℓ⟩ : Event).id)
        && a.label.accesses x && (a.label.tx == t)) [⟨ls.length, ℓ⟩] = [] := by simp
  rw [hnil, List.append_nil, accessesOf]
  apply List.filter_congr
  intro a ha
  have h1 : a.id < ls.length := id_lt_of_mem_traceEvents ha
  cases hb : a.label.accesses x <;> cases hc : (a.label.tx == t) <;> simp [h1]

/-- **Internal consistency.** Every transaction of every trace of every program
satisfies `Int`: a `get` of `x` returns the value of the `po`-latest earlier
access to `x` by the *same* transaction. -/
theorem int_transactionOf {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) (t : TxId) : (transactionOf ℓs t).Int := by
  refine Trace.reverseRecOn (motive := fun ℓs _ => ∀ t, (transactionOf ℓs t).Int)
    (by intro t e he; simp [traceEvents, traceEventsFrom] at he)
    ?_ h t
  intro ls C ℓ C' hrun ih hstep u e he x n s hlabel a ha
  cases ℓ with
  | adm =>
    -- an administrative step is not an event: nothing joins `E`, and no
    -- prior-access set moves, so the IH applies unchanged
    have hpa : (transactionOf ls u).maxPriorAccess e x = some a := by
      rw [Transaction.maxPriorAccess, ← priorAccesses_append_adm ls u e x]
      exact ha
    refine ih u e ?_ x n s hlabel a hpa
    simpa [traceEvents_append_adm] using he
  | ev ℓ' =>
    have hmem : e ∈ traceEvents (ls ++ [TLabel.ev ℓ']) ∧ e.label.tx = u := by
      simpa using he
    rw [traceEvents_append_ev] at hmem
    rcases List.mem_append.mp hmem.1 with hold | hnew
    · -- `e` was already present: its prior accesses are unchanged, so use the IH
      have hlt : e.id < ls.length := id_lt_of_mem_traceEvents hold
      have hpa : (transactionOf ls u).maxPriorAccess e x = some a := by
        rw [Transaction.maxPriorAccess, ← priorAccesses_append_of_lt (ℓ := ℓ') hlt]
        exact ha
      exact ih u e (by simpa using ⟨hold, hmem.2⟩) x n s hlabel a hpa
    · -- `e` is the label just appended, so the step that produced it is a `get`
      cases hnew with
      | tail _ hcon => cases hcon
      | head =>
        have hu : s = u := by
          have := hmem.2; rw [hlabel] at this; simpa [Label.tx] using this
        subst hu
        have hℓ : ℓ' = Label.get x n s := hlabel
        subst hℓ
        cases hstep with
        | @get i l v t2 K hthr hlam hth hst =>
          refine ⟨Transaction.accesses_of_maxPriorAccess ha, ?_⟩
          obtain ⟨w, hw⟩ := accessVal_isSome (Transaction.accesses_of_maxPriorAccess ha)
          have hlav : lastAccessVal s x ls = some w := by
            rw [lastAccessVal, ← priorAccesses_new ls (Label.get x n s) s x,
              ← Transaction.maxPriorAccess, ha]
            simpa using hw
          have hcw := inv_store hrun s hth x w hlav
          rw [hw, ← hcw, hst]

/-- The history of any trace satisfies `Int`. -/
theorem int_historyOf {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) : (historyOf ℓs).Int := by
  intro T hT
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hT
  exact int_transactionOf h t

end Reagent
