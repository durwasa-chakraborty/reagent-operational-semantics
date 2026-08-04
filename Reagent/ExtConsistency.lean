/-
  External consistency for Reagent (Section "External consistency").

  An *external* get — one whose transaction has not touched `x` before it — is
  exactly the get `Int` leaves free. `Ext` fixes it: it returns the value set by
  the `AR`-latest *committed* setter of `x`, or the initial `0` if there is none.

  The proof runs in two halves.

  * **Operational half.** A fold `cv` over the trace tracks a pair
    `(committed value of x, pending value of the live transaction)`. The
    invariant `StoreEnc` says the store agrees with that pair, and it is
    preserved by every rule — `retry` included, because the snapshot it restores
    was taken when the store held the committed value.

  * **Declarative half.** The first component of `cv` is characterised as
    "the value of the `AR`-latest committed setter of `x`, or `0`", which is the
    right-hand side of `Ext`.

  The single lock ties the two together: transactional events of different
  transactions never interleave, so `AR` — defined by where a terminator sits
  relative to a `begin` — is exactly the order in which the fold visits
  transactions.
-/
import Reagent.IntConsistency

namespace Reagent

/-! ## The two judgements (§External consistency) -/

/-- The label is a `set` on `x`. -/
def Label.isSetOn (x : Loc) : Label → Bool
  | .set l _ _ => l == x
  | _          => false

theorem Label.accesses_of_isSetOn {x : Loc} {ℓ : Label} (h : ℓ.isSetOn x = true) :
    ℓ.accesses x = true := by
  cases ℓ <;> simp [Label.isSetOn, Label.accesses] at h ⊢ <;> exact h

namespace Transaction

/-- The `set` events of `T` on `x`, in program order. -/
def setsOn (T : Transaction) (x : Loc) : List Event :=
  T.events.filter (fun e => e.label.isSetOn x)

/-- The accesses of `T` to `x`, in program order. -/
def accessesOn (T : Transaction) (x : Loc) : List Event :=
  T.events.filter (fun e => e.label.accesses x)

/-- The value `T` leaves in `x`: the value of its `po`-last set of `x`. -/
def lastSetVal (T : Transaction) (x : Loc) : Option Nat :=
  ((T.setsOn x).reverse.head?).bind (fun e => e.label.accessVal)

/-- `T ⊢ Set x : n` — `T` sets `x`, and its `po`-last set of `x` has value `n`. -/
def SetVal (T : Transaction) (x : Loc) (n : Nat) : Prop := T.lastSetVal x = some n

/-- `T ⊢ Get x : n` — `T`'s `po`-first access to `x` is a get returning `n`.
This is precisely an *external* get of `x` by `T`: nothing in `T` touched `x`
earlier, so `Int`'s premise is vacuous and the value must come from elsewhere. -/
def GetVal (T : Transaction) (x : Loc) (n : Nat) : Prop :=
  ∃ e t, (T.accessesOn x).head? = some e ∧ e.label = .get x n t

end Transaction

/-- **External consistency** (`Ext`), as the document states it:

`∀ T ∈ fst(H). ∀ x n. T ⊢ Get x : n ⟹`
`  (AR⁻¹(T) ∩ Wₓ = ∅ ∧ n = 0) ∨ max_AR(AR⁻¹(T) ∩ Wₓ) ⊢ Set x : n`
`where Wₓ = { S | S ∈ Committed(fst(H)) ∧ S ⊢ Set x : _ }`.

`max_AR` is spelled out rather than introduced as a function: the witness `S` is
required to be `AR`-above every other member of `AR⁻¹(T) ∩ Wₓ`. Restricting `Wₓ`
to *committed* transactions is what stops an aborted set being observed; `AR`
itself orders committed and aborted transactions alike. -/
def History.Ext (H : History) : Prop :=
  ∀ T ∈ H.txs, ∀ x n, T.GetVal x n →
    ((¬ ∃ S ∈ H.txs, AR S T ∧ S.Committed ∧ ∃ m, S.SetVal x m) ∧ n = 0) ∨
    (∃ S ∈ H.txs, AR S T ∧ S.Committed ∧ S.SetVal x n ∧
      ∀ S' ∈ H.txs, AR S' T → S'.Committed → (∃ m, S'.SetVal x m) →
        S' = S ∨ AR S' S)

/-! ## The committed-value fold -/

/-- Fold state `(c, p)`: `c` is the committed value of `x`, `p` the live
transaction's pending write to `x` (`none` if it has not written `x`, or if no
transaction is live). `begin` clears the pending value, `end` commits it, and
`retry` discards it. -/
def cvStep (x : Loc) (s : Nat × Option Nat) : TLabel → Nat × Option Nat
  | .ev (.begin _)   => (s.1, none)
  | .ev (.set l v _) => if l = x then (s.1, some v) else s
  | .ev (.eend _)    => match s.2 with
                        | some v => (v, none)
                        | none   => (s.1, none)
  | .ev (.retry _)   => (s.1, none)
  | .ev (.get _ _ _) => s
  | .adm             => s

/-- The fold state after the trace `ℓs`. -/
def cv (x : Loc) (ℓs : List TLabel) : Nat × Option Nat :=
  ℓs.foldl (cvStep x) (0, none)

/-- The invariant tying a configuration to the fold:

* the store holds the pending value if there is one, else the committed value;
* outside a transaction there is no pending value;
* inside one, the snapshot holds the committed value — which is what makes
  `retry`'s rollback land exactly on `c`. -/
def StoreEnc (C : Config) (x : Loc) (s : Nat × Option Nat) : Prop :=
  C.store x = s.2.getD s.1 ∧
  (C.activeThread = none → s.2 = none) ∧
  (∀ i, C.activeThread = some i → C.snapshot x = s.1)

theorem storeEnc_init (E₀ : ThreadMap) (x : Loc) :
    StoreEnc (initConfig E₀) x (0, none) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro i hi
  simp [initConfig] at hi

/-- Every rule preserves the invariant. -/
theorem storeEnc_step {C C' : Config} {ℓ : TLabel} {x : Loc} {s : Nat × Option Nat}
    (tr : Trans C ℓ C') (h : StoreEnc C x s) : StoreEnc C' x (cvStep x s ℓ) := by
  obtain ⟨c, p⟩ := s
  obtain ⟨hstore, hnone, hsnap⟩ := h
  cases tr with
  | @begin i e K he hl =>
    have hp : p = none := hnone hl
    subst hp
    refine ⟨?_, ?_, ?_⟩
    · simpa [cvStep] using hstore
    · intro hc; simp at hc
    · intro j _; simpa [cvStep] using hstore
  | @get i l v t K he hl ht hv => exact ⟨hstore, hnone, hsnap⟩
  | @set i l v t K he hl ht =>
    by_cases hlx : l = x
    · subst hlx
      refine ⟨?_, ?_, ?_⟩
      · simp [cvStep, update]
      · intro hc; rw [hl] at hc; exact absurd hc (by simp)
      · intro j _; simpa [cvStep] using hsnap i hl
    · refine ⟨?_, ?_, ?_⟩
      · simp only [cvStep, if_neg hlx]
        show (update C.store l v) x = p.getD c
        rw [update_other C.store l x v hlx]; exact hstore
      · intro hc; rw [hl] at hc; exact absurd hc (by simp)
      · intro j _; simp only [cvStep, if_neg hlx]; exact hsnap i hl
  | @eend i t K he hl ht =>
    cases p with
    | none =>
      refine ⟨by simpa [cvStep] using hstore, fun _ => rfl, ?_⟩
      intro j hj; simp at hj
    | some v =>
      refine ⟨by simpa [cvStep] using hstore, fun _ => rfl, ?_⟩
      intro j hj; simp at hj
  | @retry i t K he hl ht =>
    refine ⟨?_, fun _ => rfl, ?_⟩
    · show C.snapshot x = _
      simpa [cvStep] using hsnap i hl
    · intro j hj; simp at hj
  | @adm i r e K he hloc => exact ⟨hstore, hnone, hsnap⟩

/-- The invariant is preserved along a whole run. -/
theorem storeEnc_fold {C C' : Config} {w : List TLabel} (x : Loc)
    (h : Trace C w C') :
    ∀ s, StoreEnc C x s → StoreEnc C' x (w.foldl (cvStep x) s) := by
  induction h with
  | nil => intro s hs; exact hs
  | @cons C ℓ C₁ w' Cf tr _ ih =>
    intro s hs
    rw [List.foldl_cons]
    exact ih _ (storeEnc_step tr hs)

/-- At any reachable configuration the store agrees with the fold. -/
theorem storeEnc_of_trace {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (x : Loc) (h : Trace (initConfig E₀) ℓs C) : StoreEnc C x (cv x ℓs) :=
  storeEnc_fold x h _ (storeEnc_init E₀ x)

@[simp] theorem cv_append (x : Loc) (ls : List TLabel) (ℓ : TLabel) :
    cv x (ls ++ [ℓ]) = cvStep x (cv x ls) ℓ := by
  simp [cv, List.foldl_append]

/-! ## Locating an event in the trace -/

theorem traceEventsFrom_append (s : Nat) (l₁ l₂ : List TLabel) :
    traceEventsFrom s (l₁ ++ l₂)
      = traceEventsFrom s l₁ ++ traceEventsFrom (s + l₁.length) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [traceEventsFrom]
  | cons a as ih =>
    have hs : s + 1 + as.length = s + (as.length + 1) := by omega
    cases a with
    | adm  => simp [traceEventsFrom, ih (s + 1), hs]
    | ev _ => simp [traceEventsFrom, ih (s + 1), hs]

/-- An event of a prefix is an event of the whole trace. -/
theorem mem_traceEvents_of_prefix {l₁ l₂ : List TLabel} {e : Event}
    (h : e ∈ traceEvents l₁) : e ∈ traceEvents (l₁ ++ l₂) := by
  rw [traceEvents, traceEventsFrom_append]
  exact List.mem_append.mpr (.inl h)

/-- Every event splits its trace: it *is* the label at its own position. -/
theorem exists_split_of_mem_traceEventsFrom :
    ∀ (s : Nat) (ℓs : List TLabel) (e : Event), e ∈ traceEventsFrom s ℓs →
      ∃ pre post, ℓs = pre ++ .ev e.label :: post ∧ s + pre.length = e.id := by
  intro s ℓs
  induction ℓs generalizing s with
  | nil => intro e he; cases he
  | cons a as ih =>
    intro e he
    cases a with
    | adm =>
      obtain ⟨pre, post, hsplit, hlen⟩ := ih (s + 1) e he
      refine ⟨.adm :: pre, post, by rw [hsplit]; rfl, ?_⟩
      simp; omega
    | ev ℓ =>
      rcases List.mem_cons.mp he with h | h
      · subst h; exact ⟨[], as, rfl, by simp⟩
      · obtain ⟨pre, post, hsplit, hlen⟩ := ih (s + 1) e h
        refine ⟨.ev ℓ :: pre, post, by rw [hsplit]; rfl, ?_⟩
        simp; omega

theorem exists_split_of_mem_traceEvents {ℓs : List TLabel} {e : Event}
    (h : e ∈ traceEvents ℓs) :
    ∃ pre post, ℓs = pre ++ .ev e.label :: post ∧ pre.length = e.id := by
  obtain ⟨pre, post, hsplit, hlen⟩ := exists_split_of_mem_traceEventsFrom 0 ℓs e h
  exact ⟨pre, post, hsplit, by omega⟩

/-- A run passes through the configurations either side of any of its steps. -/
theorem Trace.locate {C₀ C : Config} {pre post : List TLabel} {ℓ : TLabel}
    (h : Trace C₀ (pre ++ ℓ :: post) C) :
    ∃ D D', Trace C₀ pre D ∧ Trans D ℓ D' ∧ Trace D' post C := by
  obtain ⟨D, h1, h2⟩ := Trace.split h
  cases h2 with
  | cons hstep hrest => exact ⟨D, _, h1, hstep, hrest⟩

/-! ## The pending value is the live transaction's last set -/

/-- The `t`-tagged sets of `x` in `ℓs`, in trace order. -/
def setsOf (t : TxId) (x : Loc) (ℓs : List TLabel) : List Event :=
  (traceEvents ℓs).filter (fun a => a.label.tx == t && a.label.isSetOn x)

/-- The value of the `po`-last `t`-tagged set of `x` in `ℓs`. -/
def lastSetValOf (t : TxId) (x : Loc) (ℓs : List TLabel) : Option Nat :=
  ((setsOf t x ℓs).reverse.head?).bind (fun a => a.label.accessVal)

theorem setsOf_append_ev (t : TxId) (x : Loc) (ℓs : List TLabel) (ℓ : Label) :
    setsOf t x (ℓs ++ [.ev ℓ]) =
      setsOf t x ℓs ++
        (if ℓ.tx == t && ℓ.isSetOn x then [(⟨ℓs.length, ℓ⟩ : Event)] else []) := by
  simp only [setsOf, traceEvents_append_ev, List.filter_append]
  congr 1
  by_cases h : (ℓ.tx == t && ℓ.isSetOn x) = true <;> simp [h]

theorem setsOf_append_adm (t : TxId) (x : Loc) (ℓs : List TLabel) :
    setsOf t x (ℓs ++ [.adm]) = setsOf t x ℓs := by
  simp only [setsOf, traceEvents_append_adm]

theorem lastSetValOf_append_of_set {t : TxId} {x : Loc} {ℓs : List TLabel}
    {ℓ : Label} (h : (ℓ.tx == t && ℓ.isSetOn x) = true) :
    lastSetValOf t x (ℓs ++ [.ev ℓ]) = ℓ.accessVal := by
  simp [lastSetValOf, setsOf_append_ev, h]

theorem lastSetValOf_append_of_not_set {t : TxId} {x : Loc} {ℓs : List TLabel}
    {ℓ : Label} (h : (ℓ.tx == t && ℓ.isSetOn x) = false) :
    lastSetValOf t x (ℓs ++ [.ev ℓ]) = lastSetValOf t x ℓs := by
  simp [lastSetValOf, setsOf_append_ev, h]

theorem lastSetValOf_append_adm (t : TxId) (x : Loc) (ℓs : List TLabel) :
    lastSetValOf t x (ℓs ++ [.adm]) = lastSetValOf t x ℓs := by
  simp [lastSetValOf, setsOf_append_adm]

theorem setsOf_eq_nil {t : TxId} {x : Loc} {ℓs : List TLabel}
    (h : ∀ e ∈ traceEvents ℓs, e.label.tx ≠ t) : setsOf t x ℓs = [] := by
  simp only [setsOf, List.filter_eq_nil_iff]
  intro a ha
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro htx
  exact absurd htx (h _ ha)

theorem lastSetValOf_eq_none {t : TxId} {x : Loc} {ℓs : List TLabel}
    (h : ∀ e ∈ traceEvents ℓs, e.label.tx ≠ t) : lastSetValOf t x ℓs = none := by
  simp [lastSetValOf, setsOf_eq_nil h]

/-- The weaker premise that matters for an external get: `t` may well have other
events in `ℓs`, it just has not *set* `x`. -/
theorem lastSetValOf_eq_none_of_no_set {t : TxId} {x : Loc} {ℓs : List TLabel}
    (h : ∀ a ∈ traceEvents ℓs, a.label.tx = t → a.label.isSetOn x = false) :
    lastSetValOf t x ℓs = none := by
  have : setsOf t x ℓs = [] := by
    simp only [setsOf, List.filter_eq_nil_iff]
    intro a ha
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro htx
    simp [h a ha htx]
  simp [lastSetValOf, this]

/-- The fold's pending component is exactly the live transaction's `po`-last set
of `x`. This is what makes the pending value `none` for an *external* get. -/
theorem inv_pending {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config} (x : Loc)
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ t, C.activeTx = some t → (cv x ℓs).2 = lastSetValOf t x ℓs := by
  refine Trace.reverseRecOn (motive := fun ℓs C =>
      ∀ t, C.activeTx = some t → (cv x ℓs).2 = lastSetValOf t x ℓs)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C ℓ C' hrun ih hstep
  cases hstep with
  | @get i l v t K he hl ht hv =>
    intro t' ht'
    have ht2 : C.activeTx = some t' := ht'
    rw [cv_append, lastSetValOf_append_of_not_set (by simp [Label.isSetOn])]
    exact ih t' ht2
  | @set i l v t K he hl ht =>
    intro t' ht'
    have ht2 : C.activeTx = some t' := ht'
    rw [ht] at ht2
    have htt : t = t' := Option.some.inj ht2
    subst htt
    by_cases hlx : l = x
    · subst hlx
      rw [cv_append, lastSetValOf_append_of_set (by simp [Label.tx, Label.isSetOn])]
      simp [cvStep, Label.accessVal]
    · rw [cv_append,
        lastSetValOf_append_of_not_set (by simp [Label.tx, Label.isSetOn, hlx])]
      simp only [cvStep, if_neg hlx]
      exact ih t ht
  | @eend i t K he hl ht =>
    intro t' ht'
    exact absurd ht' (by simp)
  | @retry i t K he hl ht =>
    intro t' ht'
    exact absurd ht' (by simp)
  | @begin i e K he hl =>
    intro t' ht'
    have : C.nextTx = t' := Option.some.inj ht'
    subst this
    rw [cv_append, lastSetValOf_append_of_not_set (by simp [Label.isSetOn])]
    rw [lastSetValOf_eq_none
      (fun a ha => Nat.ne_of_lt ((inv_nextTx hrun).1 _ ha))]
    simp [cvStep]
  | @adm i r e K he hloc =>
    intro t' ht'
    rw [cv_append, lastSetValOf_append_adm]
    exact ih t' ht'

/-! ## An external get reads the committed value -/

theorem Transaction.accessesOn_sorted (T : Transaction) (x : Loc) :
    (T.accessesOn x).Pairwise (fun a b => a.id < b.id) :=
  List.Pairwise.sublist List.filter_sublist T.sorted

theorem Transaction.mem_events_of_mem_accessesOn {T : Transaction} {x : Loc}
    {a : Event} (h : a ∈ T.accessesOn x) : a ∈ T.events :=
  (List.mem_filter.mp h).1

/-- **The operational half of `Ext`.** An external get of `x` returns the
committed value of `x` at the moment it fires: the store holds it, because the
reading transaction has not written `x` (so the pending component is `none`). -/
theorem ext_get_value {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) {t : TxId} {x : Loc} {n : Nat}
    (hget : (transactionOf ℓs t).GetVal x n) :
    ∃ pre post, ℓs = pre ++ .ev (.get x n t) :: post ∧ n = (cv x pre).1 := by
  obtain ⟨e, t', hhead, hlbl⟩ := hget
  -- the tag on the get is `t`, since `e` is one of `T`'s events
  have heT : e ∈ (transactionOf ℓs t).events :=
    Transaction.mem_events_of_mem_accessesOn (head?_mem hhead)
  have hsame : e.label.tx = t := (transactionOf ℓs t).sameTx e heT
  have htt : t' = t := by rw [hlbl] at hsame; simpa [Label.tx] using hsame
  rw [htt] at hlbl
  -- `e` is the label at its own position, so the trace splits there
  have hmem : e ∈ traceEvents ℓs := (List.mem_filter.mp heT).1
  obtain ⟨pre, post, hsplit, hlen⟩ := exists_split_of_mem_traceEvents hmem
  rw [hlbl] at hsplit
  refine ⟨pre, post, hsplit, ?_⟩
  -- nothing `t`-tagged set `x` before the get: it is `T`'s *first* access to `x`
  have hnoset : lastSetValOf t x pre = none := by
    refine lastSetValOf_eq_none_of_no_set ?_
    intro a ha htx
    cases hset : a.label.isSetOn x with
    | false => rfl
    | true =>
      exfalso
      have haℓ : a ∈ traceEvents ℓs := by
        rw [hsplit]; exact mem_traceEvents_of_prefix ha
      have haT : a ∈ (transactionOf ℓs t).events := by
        simp only [transactionOf_events, List.mem_filter]
        exact ⟨haℓ, by simp [htx]⟩
      have haacc : a ∈ (transactionOf ℓs t).accessesOn x := by
        simp only [Transaction.accessesOn, List.mem_filter]
        exact ⟨haT, Label.accesses_of_isSetOn hset⟩
      have hlt : a.id < pre.length := id_lt_of_mem_traceEvents ha
      have hleast := head?_least ((transactionOf ℓs t).accessesOn_sorted x) hhead a haacc
      rcases hleast with hEq | hLt
      · rw [hEq] at hlt; omega
      · omega
  -- run to just before the get, and invert the step that produced it
  subst hsplit
  obtain ⟨D, D', hpre, hstep, _⟩ := Trace.locate h
  have hstore : D.store x = n := by
    cases hstep with | @get i l v u K _ _ _ hv => exact hv
  have hactive : D.activeTx = some t := by
    cases hstep with | @get i l v u K _ _ ht _ => exact ht
  have hst : D.store x = (cv x pre).1 := by
    have h1 := (storeEnc_of_trace x hpre).1
    rw [inv_pending x hpre t hactive, hnoset] at h1
    simpa using h1
  rw [hstore] at hst
  exact hst

/-! ## Structural facts: transactions occupy disjoint blocks

The single lock means a transaction's events are contiguous: while `θ = t` only
`t`-tagged events can be emitted, and `begin` requires `λ = ⊥`. The invariants
below are the parts of that picture the proof needs. -/

/-- `λ = ⊥ ↔ θ = ⊥`, the invariant the rules are designed to keep. -/
theorem inv_lock {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    (C.activeThread = none ↔ C.activeTx = none) := by
  refine Trace.reverseRecOn
    (motive := fun _ C => C.activeThread = none ↔ C.activeTx = none)
    (by simp [initConfig]) ?_ h
  intro ls C ℓ C' _ ih hstep
  cases hstep with
  | @begin i e K he hl => simp
  | @get i l v t K he hl ht hv => exact ih
  | @set i l v t K he hl ht => exact ih
  | @eend i t K he hl ht => simp
  | @retry i t K he hl ht => simp
  | @adm i r e K he hloc => exact ih

/-! ### Appending one label to a transaction's events -/

theorem transactionOf_append_adm (ls : List TLabel) (s : TxId) :
    (transactionOf (ls ++ [.adm]) s).events = (transactionOf ls s).events := by
  simp [traceEvents_append_adm]

theorem transactionOf_append_ne (ls : List TLabel) {lbl : Label} {s : TxId}
    (h : ¬ lbl.tx = s) :
    (transactionOf (ls ++ [.ev lbl]) s).events = (transactionOf ls s).events := by
  simp [traceEvents_append_ev, List.filter_append, h]

theorem transactionOf_append_eq (ls : List TLabel) {lbl : Label} {s : TxId}
    (h : lbl.tx = s) :
    (transactionOf (ls ++ [.ev lbl]) s).events
      = (transactionOf ls s).events ++ [⟨ls.length, lbl⟩] := by
  simp [traceEvents_append_ev, List.filter_append, h]

theorem head?_append_some {α : Type} {l : List α} {f a : α} (h : l.head? = some f) :
    (l ++ [a]).head? = some f := by
  cases l with
  | nil => simp at h
  | cons b bs => simp at h ⊢; exact h

theorem reverse_head?_append {α : Type} (l : List α) (a : α) :
    (l ++ [a]).reverse.head? = some a := by
  simp

/-- The live transaction opened with a `begin`, and no transaction has
terminated since: every terminator in the trace so far sits strictly before
that `begin`. -/
theorem inv_live_begin {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ t, C.activeTx = some t →
      ∃ f, (transactionOf ℓs t).minPo = some f ∧ f.label = .begin t ∧
        ∀ c ∈ traceEvents ℓs, c.label.isTerminator = true → c.id < f.id := by
  refine Trace.reverseRecOn (motive := fun ℓs C =>
      ∀ t, C.activeTx = some t →
        ∃ f, (transactionOf ℓs t).minPo = some f ∧ f.label = .begin t ∧
          ∀ c ∈ traceEvents ℓs, c.label.isTerminator = true → c.id < f.id)
    (by intro t ht; simp [initConfig] at ht) ?_ h
  intro ls C ℓ C' hrun ih hstep
  cases hstep with
  | @begin i e K he hl =>
    intro t ht
    have htn : C.nextTx = t := Option.some.inj ht
    subst htn
    -- the minted id is fresh, so `t`'s only event is this `begin`
    have hempty : (transactionOf ls C.nextTx).events = [] := by
      simp only [transactionOf_events, List.filter_eq_nil_iff]
      intro a ha
      simp only [beq_iff_eq]
      exact Nat.ne_of_lt ((inv_nextTx hrun).1 _ ha)
    refine ⟨⟨ls.length, .begin C.nextTx⟩, ?_, rfl, ?_⟩
    · show (transactionOf (ls ++ [.ev (.begin C.nextTx)]) C.nextTx).events.head? = _
      rw [transactionOf_append_eq ls (lbl := .begin C.nextTx) (s := C.nextTx) rfl,
        hempty]
      rfl
    · intro c hc hterm
      rw [traceEvents_append_ev] at hc
      rcases List.mem_append.mp hc with h' | h'
      · exact id_lt_of_mem_traceEvents h'
      · simp at h'; subst h'; simp [Label.isTerminator] at hterm
  | @get i l v t K he hl ht hv =>
    intro t' ht'
    obtain ⟨f, hmin, hlbl, hterm⟩ := ih t' ht'
    refine ⟨f, ?_, hlbl, ?_⟩
    · by_cases hst : (Label.get l v t).tx = t'
      · show (transactionOf (ls ++ [.ev (.get l v t)]) t').events.head? = _
        rw [transactionOf_append_eq ls hst]
        exact head?_append_some hmin
      · show (transactionOf (ls ++ [.ev (.get l v t)]) t').events.head? = _
        rw [transactionOf_append_ne ls hst]
        exact hmin
    · intro c hc hct
      rw [traceEvents_append_ev] at hc
      rcases List.mem_append.mp hc with h' | h'
      · exact hterm c h' hct
      · simp at h'; subst h'; simp [Label.isTerminator] at hct
  | @set i l v t K he hl ht =>
    intro t' ht'
    obtain ⟨f, hmin, hlbl, hterm⟩ := ih t' ht'
    refine ⟨f, ?_, hlbl, ?_⟩
    · by_cases hst : (Label.set l v t).tx = t'
      · show (transactionOf (ls ++ [.ev (.set l v t)]) t').events.head? = _
        rw [transactionOf_append_eq ls hst]
        exact head?_append_some hmin
      · show (transactionOf (ls ++ [.ev (.set l v t)]) t').events.head? = _
        rw [transactionOf_append_ne ls hst]
        exact hmin
    · intro c hc hct
      rw [traceEvents_append_ev] at hc
      rcases List.mem_append.mp hc with h' | h'
      · exact hterm c h' hct
      · simp at h'; subst h'; simp [Label.isTerminator] at hct
  | @eend i t K he hl ht => intro t' ht'; exact absurd ht' (by simp)
  | @retry i t K he hl ht => intro t' ht'; exact absurd ht' (by simp)
  | @adm i r e K he hloc =>
    intro t' ht'
    obtain ⟨f, hmin, hlbl, hterm⟩ := ih t' ht'
    refine ⟨f, ?_, hlbl, ?_⟩
    · show (transactionOf (ls ++ [TLabel.adm]) t').events.head? = _
      rw [transactionOf_append_adm]
      exact hmin
    · intro c hc hct
      rw [traceEvents_append_adm] at hc
      exact hterm c hc hct

/-- The live transaction has not terminated: no `end` or `retry` tagged `t`
appears while `θ = t`. -/
theorem inv_no_terminator_live {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ t, C.activeTx = some t →
      ∀ c ∈ traceEvents ℓs, c.label.tx = t → c.label.isTerminator = false := by
  intro t ht c hc htx
  obtain ⟨f, hmin, hlbl, hterm⟩ := inv_live_begin h t ht
  cases hct : c.label.isTerminator with
  | false => rfl
  | true =>
    exfalso
    have hlt : c.id < f.id := hterm c hc hct
    have hcT : c ∈ (transactionOf ℓs t).events := by
      simp only [transactionOf_events, List.mem_filter]
      exact ⟨hc, by simp [htx]⟩
    rcases Transaction.minPo_least hmin c hcT with hEq | hLt
    · rw [hEq] at hlt; omega
    · simp only [Transaction.po_def] at hLt; omega

/-- Once a transaction terminates it is finished for good: no event of that tag
appears later in the trace. `begin` mints a fresh id, so a terminated id is
never reopened. -/
theorem no_tag_after_terminator {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ c ∈ traceEvents ℓs, c.label.isTerminator = true →
      ∀ a ∈ traceEvents ℓs, a.label.tx = c.label.tx → a.id ≤ c.id := by
  refine Trace.reverseRecOn (motive := fun ℓs _ =>
      ∀ c ∈ traceEvents ℓs, c.label.isTerminator = true →
        ∀ a ∈ traceEvents ℓs, a.label.tx = c.label.tx → a.id ≤ c.id)
    (by intro c hc; simp [traceEvents, traceEventsFrom] at hc) ?_ h
  intro ls C ℓ C' hrun ih hstep
  -- the appended label either is administrative, or is an event whose tag
  -- cannot already have terminated
  have main : ∀ (lbl : Label),
      (∀ c ∈ traceEvents ls, c.label.tx = lbl.tx → c.label.isTerminator = false) →
      ∀ c ∈ traceEvents (ls ++ [.ev lbl]), c.label.isTerminator = true →
        ∀ a ∈ traceEvents (ls ++ [.ev lbl]), a.label.tx = c.label.tx →
          a.id ≤ c.id := by
    intro lbl hfresh c hc hct a ha hatx
    rw [traceEvents_append_ev] at hc ha
    rcases List.mem_append.mp hc with hc' | hc' <;>
      rcases List.mem_append.mp ha with ha' | ha'
    · exact ih c hc' hct a ha' hatx
    · -- `a` is the new event; its tag would have to have terminated already
      simp at ha'; subst ha'
      exact absurd (hfresh c hc' hatx.symm) (by simp [hct])
    · -- `c` is the new event, `a` an old one
      simp at hc'; subst hc'
      exact Nat.le_of_lt (id_lt_of_mem_traceEvents ha')
    · simp at hc' ha'; subst hc'; subst ha'; exact Nat.le_refl _
  cases hstep with
  | @begin i e K he hl =>
    refine main (.begin C.nextTx) ?_
    intro c hc htx
    exact absurd htx (Nat.ne_of_lt ((inv_nextTx hrun).1 c hc))
  | @get i l v t K he hl ht hv =>
    exact main (.get l v t) (inv_no_terminator_live hrun t ht)
  | @set i l v t K he hl ht =>
    exact main (.set l v t) (inv_no_terminator_live hrun t ht)
  | @eend i t K he hl ht =>
    exact main (.eend t) (inv_no_terminator_live hrun t ht)
  | @retry i t K he hl ht =>
    exact main (.retry t) (inv_no_terminator_live hrun t ht)
  | @adm i r e K he hloc =>
    intro c hc hct a ha hatx
    rw [traceEvents_append_adm] at hc ha
    exact ih c hc hct a ha hatx

/-- A transaction that has terminated inside a prefix gains no further events,
so its `Transaction` is the same whether read off the prefix or the whole
trace. -/
theorem transactionOf_prefix {E₀ : ThreadMap} {pre rest : List TLabel}
    {C : Config} (h : Trace (initConfig E₀) (pre ++ rest) C) {s : TxId} {c : Event}
    (hc : c ∈ traceEvents pre) (hct : c.label.isTerminator = true)
    (hcs : c.label.tx = s) :
    (transactionOf (pre ++ rest) s).events = (transactionOf pre s).events := by
  simp only [transactionOf_events, traceEvents, traceEventsFrom_append,
    List.filter_append, Nat.zero_add]
  have hnil : (traceEventsFrom pre.length rest).filter
      (fun e => e.label.tx == s) = [] := by
    simp only [List.filter_eq_nil_iff]
    intro a ha
    simp only [beq_iff_eq]
    intro hatx
    have hge : pre.length ≤ a.id := traceEventsFrom_id_ge _ _ a ha
    have hcin : c ∈ traceEvents (pre ++ rest) := mem_traceEvents_of_prefix hc
    have hain : a ∈ traceEvents (pre ++ rest) := by
      rw [traceEvents, traceEventsFrom_append]
      refine List.mem_append.mpr (.inr ?_)
      simpa using ha
    have := no_tag_after_terminator h c hcin hct a hain (by rw [hatx, hcs])
    have hclt : c.id < pre.length := id_lt_of_mem_traceEvents hc
    omega
  rw [hnil, List.append_nil]

/-! ## Characterising the fold's committed value

`Committed`, `SetVal` and the extremes depend only on a transaction's event
list, so they are stable under any trace extension that leaves those events
alone. -/

namespace Transaction

theorem minPo_congr {T T' : Transaction} (h : T.events = T'.events) :
    T.minPo = T'.minPo := by simp only [minPo, h]

theorem maxPo_congr {T T' : Transaction} (h : T.events = T'.events) :
    T.maxPo = T'.maxPo := by simp only [maxPo, h]

theorem lastSetVal_congr {T T' : Transaction} (h : T.events = T'.events) (x : Loc) :
    T.lastSetVal x = T'.lastSetVal x := by simp only [lastSetVal, setsOn, h]

theorem committed_congr {T T' : Transaction} (h : T.events = T'.events) :
    T.Committed ↔ T'.Committed := by
  simp only [Committed, minPo_congr h, maxPo_congr h]

/-- A committed transaction's greatest event is a terminator. -/
theorem isTerminator_of_committed {T : Transaction} {e : Event}
    (hc : T.Committed) (h : T.maxPo = some e) : e.label.isTerminator = true := by
  obtain ⟨-, e', t', hmax, hlbl⟩ := hc
  rw [h] at hmax
  cases hmax
  simp [hlbl, Label.isTerminator]

end Transaction

/-- `Wₓ` read off a trace: `s` is committed in `ℓs`, and it sets `x`. -/
def CommittedSetter (ℓs : List TLabel) (x : Loc) (s : TxId) : Prop :=
  (transactionOf ℓs s).Committed ∧ ∃ m, (transactionOf ℓs s).SetVal x m

/-- Where `s`'s terminator sits in `ℓs` (`0` if `s` has no events). -/
def termPos (ℓs : List TLabel) (s : TxId) : Nat :=
  ((transactionOf ℓs s).maxPo.map Event.id).getD 0

theorem committedSetter_congr {ls ls' : List TLabel} {x : Loc} {s : TxId}
    (h : (transactionOf ls s).events = (transactionOf ls' s).events) :
    CommittedSetter ls x s ↔ CommittedSetter ls' x s := by
  simp only [CommittedSetter, Transaction.committed_congr h, Transaction.SetVal,
    Transaction.lastSetVal_congr h]

theorem termPos_congr {ls ls' : List TLabel} {s : TxId}
    (h : (transactionOf ls s).events = (transactionOf ls' s).events) :
    termPos ls s = termPos ls' s := by
  simp only [termPos, Transaction.maxPo_congr h]

/-- The live transaction is not committed: everything it has emitted so far is
a non-terminator. -/
theorem inv_live_not_committed {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) :
    ∀ t, C.activeTx = some t → ¬ (transactionOf ℓs t).Committed := by
  intro t ht hc
  obtain ⟨-, e, t', hmax, hlbl⟩ := hc
  have hmem := Transaction.maxPo_mem hmax
  have hin : e ∈ traceEvents ℓs := (List.mem_filter.mp hmem).1
  have htx : e.label.tx = t := (transactionOf ℓs t).sameTx e hmem
  have := inv_no_terminator_live h t ht e hin htx
  rw [hlbl] at this
  simp [Label.isTerminator] at this

/-- A transaction whose greatest event is not an `end` is not committed. -/
theorem not_committed_of_maxPo {T : Transaction} {e : Event}
    (hmax : T.maxPo = some e) (h : e.label.isEnd = false) : ¬ T.Committed := by
  intro hc
  obtain ⟨-, e', t', hmax', hlbl⟩ := hc
  rw [hmax] at hmax'
  cases hmax'
  rw [hlbl] at h
  simp [Label.isEnd] at h

/-- The trace-level sets of `x` by `t` are exactly `t`'s set-events on `x`. -/
theorem setsOn_eq_setsOf (ℓs : List TLabel) (t : TxId) (x : Loc) :
    (transactionOf ℓs t).setsOn x = setsOf t x ℓs := by
  simp only [Transaction.setsOn, transactionOf_events, setsOf, List.filter_filter]
  exact List.filter_congr (fun a _ => Bool.and_comm _ _)

theorem lastSetVal_eq_lastSetValOf (ℓs : List TLabel) (t : TxId) (x : Loc) :
    (transactionOf ℓs t).lastSetVal x = lastSetValOf t x ℓs := by
  simp only [Transaction.lastSetVal, lastSetValOf, setsOn_eq_setsOf]

theorem not_committed_of_no_events {T : Transaction} (h : T.events = []) :
    ¬ T.Committed := by
  intro hc
  obtain ⟨-, e, t', hmax, -⟩ := hc
  rw [Transaction.maxPo, h] at hmax
  simp at hmax

/-- The appended event becomes the transaction's greatest. -/
theorem maxPo_append_ev (ls : List TLabel) (lbl : Label) :
    (transactionOf (ls ++ [.ev lbl]) lbl.tx).maxPo = some ⟨ls.length, lbl⟩ := by
  show ((transactionOf (ls ++ [.ev lbl]) lbl.tx).events).reverse.head? = _
  rw [transactionOf_append_eq ls (s := lbl.tx) rfl]
  exact reverse_head?_append _ _

theorem not_committed_append_of_not_end (ls : List TLabel) {lbl : Label}
    (h : lbl.isEnd = false) : ¬ (transactionOf (ls ++ [.ev lbl]) lbl.tx).Committed :=
  not_committed_of_maxPo (maxPo_append_ev ls lbl) h

/-- Appending a label that is not a set on `x` leaves every transaction's last
set of `x` alone. -/
theorem lastSetVal_append_not_set (ls : List TLabel) {lbl : Label} (s : TxId)
    {x : Loc} (h : lbl.isSetOn x = false) :
    (transactionOf (ls ++ [.ev lbl]) s).lastSetVal x
      = (transactionOf ls s).lastSetVal x := by
  simp [Transaction.lastSetVal, setsOn_eq_setsOf, setsOf_append_ev, h]

theorem termPos_lt_length {ls : List TLabel} {s : TxId}
    (hc : (transactionOf ls s).Committed) : termPos ls s < ls.length := by
  obtain ⟨-, e, t', hmax, -⟩ := hc
  simp only [termPos, hmax, Option.map_some, Option.getD_some]
  exact id_lt_of_mem_traceEvents (List.mem_filter.mp (Transaction.maxPo_mem hmax)).1

/-- Appending an event to a transaction that is uncommitted before *and* after
disturbs neither the set of committed setters nor any of their event lists. -/
theorem committedSetter_append_ev {ls : List TLabel} {x : Loc} {lbl : Label}
    (hu1 : ¬ (transactionOf ls lbl.tx).Committed)
    (hu2 : ¬ (transactionOf (ls ++ [.ev lbl]) lbl.tx).Committed) (s : TxId) :
    (CommittedSetter (ls ++ [.ev lbl]) x s ↔ CommittedSetter ls x s) ∧
    (CommittedSetter ls x s →
      (transactionOf (ls ++ [.ev lbl]) s).events = (transactionOf ls s).events) := by
  by_cases hs : lbl.tx = s
  · subst hs
    exact ⟨⟨fun hcs => absurd hcs.1 hu2, fun hcs => absurd hcs.1 hu1⟩,
      fun hcs => absurd hcs.1 hu1⟩
  · have hev := transactionOf_append_ne ls hs
    exact ⟨committedSetter_congr hev, fun _ => hev⟩

/-- **The declarative half of `Ext`.** The fold's committed value is the value
left by the committed setter of `x` with the latest terminator — or `0` when
there is no committed setter at all. -/
theorem cv_fst_spec {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) (x : Loc) :
    ((∀ s, ¬ CommittedSetter ℓs x s) ∧ (cv x ℓs).1 = 0) ∨
    (∃ s, CommittedSetter ℓs x s ∧ (transactionOf ℓs s).SetVal x ((cv x ℓs).1) ∧
      ∀ s', CommittedSetter ℓs x s' → s' = s ∨ termPos ℓs s' < termPos ℓs s) := by
  refine Trace.reverseRecOn (motive := fun ℓs _ =>
      ((∀ s, ¬ CommittedSetter ℓs x s) ∧ (cv x ℓs).1 = 0) ∨
      (∃ s, CommittedSetter ℓs x s ∧ (transactionOf ℓs s).SetVal x ((cv x ℓs).1) ∧
        ∀ s', CommittedSetter ℓs x s' → s' = s ∨ termPos ℓs s' < termPos ℓs s))
    ?_ ?_ h
  · left
    refine ⟨fun s hcs => ?_, rfl⟩
    exact not_committed_of_no_events (by simp [traceEvents, traceEventsFrom]) hcs.1
  intro ls C ℓ C' hrun ih hstep
  -- every rule but `end` leaves both the committed value and the committed
  -- setters exactly as they were
  have unchanged : ∀ lbl : Label,
      ¬ (transactionOf ls lbl.tx).Committed → lbl.isEnd = false →
      (cv x (ls ++ [.ev lbl])).1 = (cv x ls).1 →
      ((∀ s, ¬ CommittedSetter (ls ++ [.ev lbl]) x s) ∧
          (cv x (ls ++ [.ev lbl])).1 = 0) ∨
      (∃ s, CommittedSetter (ls ++ [.ev lbl]) x s ∧
        (transactionOf (ls ++ [.ev lbl]) s).SetVal x ((cv x (ls ++ [.ev lbl])).1) ∧
        ∀ s', CommittedSetter (ls ++ [.ev lbl]) x s' →
          s' = s ∨ termPos (ls ++ [.ev lbl]) s' < termPos (ls ++ [.ev lbl]) s) := by
    intro lbl hu1 hend hcv
    have hu2 := not_committed_append_of_not_end ls hend
    rcases ih with ⟨hnone, hzero⟩ | ⟨s, hcs, hsv, hmax⟩
    · left
      exact ⟨fun s hcs => hnone s ((committedSetter_append_ev hu1 hu2 s).1.mp hcs),
        by rw [hcv]; exact hzero⟩
    · right
      have hev := (committedSetter_append_ev hu1 hu2 s).2 hcs
      refine ⟨s, (committedSetter_append_ev hu1 hu2 s).1.mpr hcs, ?_, ?_⟩
      · rw [hcv]
        simpa [Transaction.SetVal, Transaction.lastSetVal_congr hev] using hsv
      · intro s' hcs'
        have hcs'' := (committedSetter_append_ev hu1 hu2 s').1.mp hcs'
        have hev' := (committedSetter_append_ev hu1 hu2 s').2 hcs''
        rcases hmax s' hcs'' with heq | hlt
        · exact .inl heq
        · exact .inr (by rw [termPos_congr hev', termPos_congr hev]; exact hlt)
  cases hstep with
  | @begin i e K he hl =>
    refine unchanged (.begin C.nextTx) ?_ rfl (by simp [cvStep])
    refine not_committed_of_no_events ?_
    simp only [transactionOf_events, List.filter_eq_nil_iff]
    intro a ha
    simp only [beq_iff_eq]
    exact Nat.ne_of_lt ((inv_nextTx hrun).1 _ ha)
  | @get i l v t K he hl ht hv =>
    exact unchanged (.get l v t) (inv_live_not_committed hrun t ht) rfl (by simp [cvStep])
  | @set i l v t K he hl ht =>
    refine unchanged (.set l v t) (inv_live_not_committed hrun t ht) rfl ?_
    by_cases hlx : l = x <;> simp [cvStep, hlx]
  | @retry i t K he hl ht =>
    exact unchanged (.retry t) (inv_live_not_committed hrun t ht) rfl (by simp [cvStep])
  | @adm i r e K he hloc =>
    have hev : ∀ s, (transactionOf (ls ++ [TLabel.adm]) s).events
        = (transactionOf ls s).events := transactionOf_append_adm ls
    have hcv : cv x (ls ++ [TLabel.adm]) = cv x ls := by simp [cvStep]
    rcases ih with ⟨hnone, hzero⟩ | ⟨s, hcs, hsv, hmax⟩
    · left
      exact ⟨fun s hcs => hnone s ((committedSetter_congr (hev s)).mp hcs),
        by rw [hcv]; exact hzero⟩
    · right
      refine ⟨s, (committedSetter_congr (hev s)).mpr hcs, ?_, ?_⟩
      · rw [hcv]
        simpa [Transaction.SetVal, Transaction.lastSetVal_congr (hev s)] using hsv
      · intro s' hcs'
        rcases hmax s' ((committedSetter_congr (hev s')).mp hcs') with heq | hlt
        · exact .inl heq
        · exact .inr (by rw [termPos_congr (hev s'), termPos_congr (hev s)]; exact hlt)
  | @eend i t K he hl ht =>
    -- `t` commits here: it becomes the AR-latest committed transaction
    obtain ⟨f, hmin, hflbl, hterm⟩ := inv_live_begin hrun t ht
    have hevT := transactionOf_append_eq ls (lbl := Label.eend t) (s := t) rfl
    have hmaxnew : (transactionOf (ls ++ [.ev (.eend t)]) t).maxPo
        = some ⟨ls.length, .eend t⟩ := maxPo_append_ev ls (.eend t)
    have hminnew : (transactionOf (ls ++ [.ev (.eend t)]) t).minPo = some f := by
      show ((transactionOf (ls ++ [.ev (.eend t)]) t).events).head? = _
      rw [hevT]; exact head?_append_some hmin
    have hcommT : (transactionOf (ls ++ [.ev (.eend t)]) t).Committed :=
      ⟨⟨f, t, hminnew, hflbl⟩, ⟨⟨ls.length, .eend t⟩, t, hmaxnew, rfl⟩⟩
    have hother : ∀ s, ¬ (t = s) →
        (transactionOf (ls ++ [.ev (.eend t)]) s).events
          = (transactionOf ls s).events := fun s hs => transactionOf_append_ne ls hs
    have hnotc : ¬ (transactionOf ls t).Committed := inv_live_not_committed hrun t ht
    have hlsv : (transactionOf (ls ++ [.ev (.eend t)]) t).lastSetVal x
        = lastSetValOf t x ls := by
      rw [lastSetVal_append_not_set ls t (by simp [Label.isSetOn]),
        lastSetVal_eq_lastSetValOf]
    have hpend := inv_pending x hrun t ht
    cases hp : (cv x ls).2 with
    | none =>
      have hcvnew : (cv x (ls ++ [.ev (.eend t)])).1 = (cv x ls).1 := by
        rw [cv_append]; simp [cvStep, hp]
      have hTnoset : ¬ ∃ m, (transactionOf (ls ++ [.ev (.eend t)]) t).SetVal x m := by
        rintro ⟨m, hm⟩
        rw [Transaction.SetVal, hlsv, ← hpend, hp] at hm
        exact absurd hm (by simp)
      have hiff : ∀ s, CommittedSetter (ls ++ [.ev (.eend t)]) x s ↔
          CommittedSetter ls x s := by
        intro s
        by_cases hs : t = s
        · subst hs
          exact ⟨fun hcs => absurd hcs.2 hTnoset, fun hcs => absurd hcs.1 hnotc⟩
        · exact committedSetter_congr (hother s hs)
      have hevs : ∀ s, CommittedSetter ls x s →
          (transactionOf (ls ++ [.ev (.eend t)]) s).events
            = (transactionOf ls s).events := by
        intro s hcs
        by_cases hs : t = s
        · subst hs; exact absurd hcs.1 hnotc
        · exact hother s hs
      rcases ih with ⟨hnone, hzero⟩ | ⟨s, hcs, hsv, hmax⟩
      · left
        exact ⟨fun s hcs => hnone s ((hiff s).mp hcs), by rw [hcvnew]; exact hzero⟩
      · right
        have hev := hevs s hcs
        refine ⟨s, (hiff s).mpr hcs, ?_, ?_⟩
        · rw [hcvnew]
          simpa [Transaction.SetVal, Transaction.lastSetVal_congr hev] using hsv
        · intro s' hcs'
          have hcs'' := (hiff s').mp hcs'
          have hev' := hevs s' hcs''
          rcases hmax s' hcs'' with heq | hlt
          · exact .inl heq
          · exact .inr (by rw [termPos_congr hev', termPos_congr hev]; exact hlt)
    | some v =>
      right
      have hcvnew : (cv x (ls ++ [.ev (.eend t)])).1 = v := by
        rw [cv_append]; simp [cvStep, hp]
      have hsvT : (transactionOf (ls ++ [.ev (.eend t)]) t).SetVal x v := by
        show (transactionOf (ls ++ [.ev (.eend t)]) t).lastSetVal x = some v
        rw [hlsv, ← hpend, hp]
      refine ⟨t, ⟨hcommT, ⟨v, hsvT⟩⟩, by rw [hcvnew]; exact hsvT, ?_⟩
      intro s' hcs'
      by_cases hs : t = s'
      · exact .inl hs.symm
      · right
        have hev' := hother s' hs
        have hcs'' : CommittedSetter ls x s' := (committedSetter_congr hev').mp hcs'
        have h2 : termPos (ls ++ [.ev (.eend t)]) t = ls.length := by
          simp [termPos, hmaxnew]
        rw [termPos_congr hev', h2]
        exact termPos_lt_length hcs''.1

/-! ## From terminator positions to `AR` -/

theorem head?_append_gen {α : Type} {l₁ l₂ : List α} {f : α} (h : l₁.head? = some f) :
    (l₁ ++ l₂).head? = some f := by
  cases l₁ with
  | nil => simp at h
  | cons b bs => simp at h ⊢; exact h

/-- A transaction's `po`-least event is fixed once the prefix that contains it
is fixed. -/
theorem minPo_prefix {pre rest : List TLabel} {s : TxId} {f : Event}
    (h : (transactionOf pre s).minPo = some f) :
    (transactionOf (pre ++ rest) s).minPo = some f := by
  show ((transactionOf (pre ++ rest) s).events).head? = _
  simp only [transactionOf_events, traceEvents, traceEventsFrom_append,
    List.filter_append, Nat.zero_add]
  exact head?_append_gen h

theorem mem_prefix_of_id_lt {pre rest : List TLabel} {e : Event}
    (h : e ∈ traceEvents (pre ++ rest)) (hlt : e.id < pre.length) :
    e ∈ traceEvents pre := by
  rw [traceEvents, traceEventsFrom_append] at h
  rcases List.mem_append.mp h with h' | h'
  · exact h'
  · have := traceEventsFrom_id_ge _ _ e (by simpa using h')
    omega

/-- A committed transaction's greatest event is its `end`, tagged with its own
identifier. -/
theorem committed_maxPo {ℓs : List TLabel} {s : TxId}
    (hc : (transactionOf ℓs s).Committed) :
    ∃ c, (transactionOf ℓs s).maxPo = some c ∧ c.label = .eend s ∧
      c ∈ traceEvents ℓs ∧ termPos ℓs s = c.id := by
  obtain ⟨-, c, t₀, hmax, hlbl⟩ := hc
  have hmem := Transaction.maxPo_mem hmax
  have htx : c.label.tx = s := (transactionOf ℓs s).sameTx c hmem
  rw [hlbl] at htx
  simp only [Label.tx] at htx
  subst htx
  exact ⟨c, hmax, hlbl, (List.mem_filter.mp hmem).1, by simp [termPos, hmax]⟩

/-- **Terminator order is arbitration order.** For two committed transactions,
`S'` terminating before `S` means `S'` terminated before `S` even *began* — the
lock leaves no room for them to overlap — which is exactly `S' <_AR S`. -/
theorem ar_of_termPos_lt {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) {s s' : TxId}
    (hc : (transactionOf ℓs s).Committed)
    (hc' : (transactionOf ℓs s').Committed)
    (hlt : termPos ℓs s' < termPos ℓs s) :
    AR (transactionOf ℓs s') (transactionOf ℓs s) := by
  obtain ⟨c, hmax, hclbl, hcmem, hcpos⟩ := committed_maxPo hc
  obtain ⟨c', hmax', hclbl', hcmem', hcpos'⟩ := committed_maxPo hc'
  -- split the trace at `s`'s `end`
  obtain ⟨pre₁, post₁, hsplit, hlen⟩ := exists_split_of_mem_traceEvents hcmem
  rw [hclbl] at hsplit
  subst hsplit
  obtain ⟨D, D', hpre, hstep, -⟩ := Trace.locate h
  have hact : D.activeTx = some s := by
    cases hstep with | @eend i t K _ _ ht => exact ht
  obtain ⟨f, hminf, hflbl, hterm⟩ := inv_live_begin hpre s hact
  -- `s'` terminated before `s`'s `end`, hence inside that prefix
  have hc'lt : c'.id < pre₁.length := by omega
  have hc'pre : c' ∈ traceEvents pre₁ := mem_prefix_of_id_lt hcmem' hc'lt
  have hc'term : c'.label.isTerminator = true := by
    rw [hclbl']; simp [Label.isTerminator]
  refine ⟨c', f, s, hmax', by rw [hclbl']; simp [Label.isTerminator],
    minPo_prefix hminf, hflbl, hterm c' hc'pre hc'term⟩

/-- Every tag that has an event in the trace is one of its transaction ids. -/
theorem mem_txIds_of_mem_traceEventsFrom :
    ∀ (k : Nat) (ℓs : List TLabel) (e : Event),
      e ∈ traceEventsFrom k ℓs → e.label.tx ∈ txIds ℓs := by
  intro k ℓs
  induction ℓs generalizing k with
  | nil => intro e he; cases he
  | cons a as ih =>
    intro e he
    cases a with
    | adm => exact ih (k + 1) e he
    | ev lbl =>
      rcases List.mem_cons.mp he with h' | h'
      · subst h'; exact List.mem_cons_self ..
      · have hrec := ih (k + 1) e h'
        by_cases hq : e.label.tx = lbl.tx
        · rw [hq]; exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ ?_
          exact List.mem_filter.mpr ⟨hrec, by simp [hq]⟩

theorem mem_txIds_of_mem_traceEvents {ℓs : List TLabel} {e : Event}
    (h : e ∈ traceEvents ℓs) : e.label.tx ∈ txIds ℓs :=
  mem_txIds_of_mem_traceEventsFrom 0 ℓs e h

/-- A committed setter that finished inside a prefix reads the same off the
whole trace: it gains no further events. -/
theorem committedSetter_transfer {E₀ : ThreadMap} {pre rest : List TLabel}
    {C : Config} (h : Trace (initConfig E₀) (pre ++ rest) C) {x : Loc} {s : TxId}
    (hcs : CommittedSetter pre x s) :
    (transactionOf (pre ++ rest) s).events = (transactionOf pre s).events := by
  obtain ⟨c, hmax, hclbl, hcmem, -⟩ := committed_maxPo hcs.1
  exact transactionOf_prefix h hcmem (by rw [hclbl]; simp [Label.isTerminator])
    (by rw [hclbl]; simp [Label.tx])

/-- **External consistency.** The history of every trace of every program
satisfies `Ext`: an external get returns the value written by the `AR`-latest
committed setter of that location, or `0` if there is none. -/
theorem ext_historyOf {E₀ : ThreadMap} {ℓs : List TLabel} {C : Config}
    (h : Trace (initConfig E₀) ℓs C) : (historyOf ℓs).Ext := by
  intro T hT x n hget
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hT
  -- an external get reads the committed value of `x` at the point it fires
  obtain ⟨pre, post, hsplit, hn⟩ := ext_get_value h hget
  subst hsplit
  -- `T`'s `begin`, and the fact that nothing has terminated since
  obtain ⟨D, D', hpre, hstep, -⟩ := Trace.locate h
  have hact : D.activeTx = some t := by
    cases hstep with | @get i l v u K _ _ ht _ => exact ht
  obtain ⟨f, hminf, hflbl, hterm⟩ := inv_live_begin hpre t hact
  have hfmem : f ∈ traceEvents pre :=
    (List.mem_filter.mp (Transaction.minPo_mem hminf)).1
  have hflt : f.id < pre.length := id_lt_of_mem_traceEvents hfmem
  have hminT : (transactionOf (pre ++ .ev (.get x n t) :: post) t).minPo = some f :=
    minPo_prefix hminf
  -- `AR`-before `T` is the same as "finished inside `pre`"
  have hAR_of : ∀ s, CommittedSetter pre x s →
      AR (transactionOf (pre ++ .ev (.get x n t) :: post) s)
        (transactionOf (pre ++ .ev (.get x n t) :: post) t) := by
    intro s hcs
    obtain ⟨c, hmax, hclbl, hcmem, -⟩ := committed_maxPo hcs.1
    have hev := committedSetter_transfer h hcs
    refine ⟨c, f, t, ?_, by rw [hclbl]; simp [Label.isTerminator], hminT, hflbl, ?_⟩
    · rw [Transaction.maxPo_congr hev]; exact hmax
    · exact hterm c hcmem (by rw [hclbl]; simp [Label.isTerminator])
  have hof_AR : ∀ s', AR (transactionOf (pre ++ .ev (.get x n t) :: post) s')
        (transactionOf (pre ++ .ev (.get x n t) :: post) t) →
      (transactionOf (pre ++ .ev (.get x n t) :: post) s').Committed →
      (∃ m, (transactionOf (pre ++ .ev (.get x n t) :: post) s').SetVal x m) →
      CommittedSetter pre x s' ∧
        (transactionOf (pre ++ .ev (.get x n t) :: post) s').events
          = (transactionOf pre s').events := by
    intro s' har hcomm hsv
    obtain ⟨c', g, u, hmax', -, hming, -, hltg⟩ := har
    obtain ⟨c, hmaxc, hclbl, hcmem, -⟩ := committed_maxPo hcomm
    have heqc : c' = c := by
      rw [hmaxc] at hmax'; exact (Option.some.inj hmax').symm
    have hgf : g = f := by
      rw [hminT] at hming; exact (Option.some.inj hming).symm
    have hcid : c.id < pre.length := by
      have h1 : c'.id < g.id := hltg
      rw [heqc, hgf] at h1
      omega
    have hcpre : c ∈ traceEvents pre := mem_prefix_of_id_lt hcmem hcid
    have hev : (transactionOf (pre ++ .ev (.get x n t) :: post) s').events
        = (transactionOf pre s').events :=
      transactionOf_prefix h hcpre (by rw [hclbl]; simp [Label.isTerminator])
        (by rw [hclbl]; simp [Label.tx])
    refine ⟨⟨(Transaction.committed_congr hev).mp hcomm, ?_⟩, hev⟩
    obtain ⟨m, hm⟩ := hsv
    exact ⟨m, by rwa [Transaction.SetVal, Transaction.lastSetVal_congr hev] at hm⟩
  rcases cv_fst_spec hpre x with ⟨hnone, hzero⟩ | ⟨s, hcs, hsv, hmax⟩
  · -- no committed setter of `x` at all: the get returns the initial `0`
    left
    refine ⟨?_, by rw [hn, hzero]⟩
    rintro ⟨S, hSmem, har, hcomm, hsv⟩
    obtain ⟨s', -, rfl⟩ := List.mem_map.mp hSmem
    exact hnone s' (hof_AR s' har hcomm hsv).1
  · -- the AR-latest committed setter of `x` fixes the value
    right
    have hev := committedSetter_transfer h hcs
    have hcommS : (transactionOf (pre ++ .ev (.get x n t) :: post) s).Committed :=
      (Transaction.committed_congr hev).mpr hcs.1
    obtain ⟨c, hmaxc, hclbl, hcmem, -⟩ := committed_maxPo hcs.1
    refine ⟨transactionOf (pre ++ .ev (.get x n t) :: post) s, ?_, hAR_of s hcs,
      hcommS, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨s, ?_, rfl⟩
      have := mem_txIds_of_mem_traceEvents (mem_traceEvents_of_prefix hcmem
        (l₂ := .ev (.get x n t) :: post))
      rwa [hclbl] at this
    · show (transactionOf _ s).lastSetVal x = some n
      rw [Transaction.lastSetVal_congr hev, hn]
      exact hsv
    · intro S' hS'mem har' hcomm' hsv'
      obtain ⟨s', -, rfl⟩ := List.mem_map.mp hS'mem
      obtain ⟨hcs', hev'⟩ := hof_AR s' har' hcomm' hsv'
      rcases hmax s' hcs' with heq | hlt
      · exact .inl (by rw [heq])
      · refine .inr (ar_of_termPos_lt h hcommS
          ((Transaction.committed_congr hev').mpr hcs'.1) ?_)
        rw [termPos_congr hev', termPos_congr hev]
        exact hlt

end Reagent
