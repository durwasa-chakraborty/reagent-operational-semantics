import Optimistic.ExtConsistencyU

namespace Optimistic

open Reagent (Loc TxId ThId ThreadMap Expr Store update update_other)

/-! ## Ext_c -/

-- `Inv(τ, C)`: every invariant, carried together along the run.
structure ExtInv (τ : Trace) (C : Config) : Prop where
  -- Ids: event ids are unique.
  ids : (∀ e ∈ events τ, e.id ∈ C.usedIds) ∧ UniqueIds (events τ)
  -- F: used and live tags are below `nextTx`; a `begin` precedes its terminator.
  fresh : (∀ e ∈ events τ, e.label.tx < C.nextTx)
  -- WARN multiple threads are executing tx concurrently, so a single thread can
  -- execute multiple tx one after the other. θ so the question is C.txs j will return
  -- which θ  ? Are we assuming that we each thread executes only one transaction?
  -- NOTE each thread is in atmost one live transaction at a time.
    ∧ (∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → t < C.nextTx)
    ∧ BeginsBeforeTerm (events τ)
  -- D: two live threads never share a `t`.
  distinct : LiveDistinct C.txs
  -- T: a live `t` has no terminator in `τ`, `Live ∩ Term = ∅`.
  live : ∀ j t Λ Ê, C.txs j = some (t, Λ, Ê) → ∀ a, ¬ Terminates (events τ) t a
  -- L: the log mirrors `t`'s accesses.
  log : LogMirrors (events τ) C.txs
  -- L⁻ (part (b)): a log entry comes from an access, `Λ_t(x) ≠ ⊥ → t accessed x`.
  logBack : LogBack (events τ) C.txs
  -- Cur: `Λ(x) = (o, c)` with `c` the current value of `x` for `t`.
  cur : Cur (events τ) C.txs
  -- Store: `σ(x)` is the latest committed writer's value, or `σ₀(x)`.
  store : StoreInv (events τ) C.store
  -- P: `Ext_c` for the witness history.
  ext : ExtP τ
  -- R: the log remembers what each live `t` read from memory.
  reads : ReadsInv (events τ) C.txs
  -- U (part (b)): every external read returns the latest value committed before it.
  uread : UInv (events τ)

-- `Run C₀ τ C → Inv(τ, C)`, by induction on the run.
theorem inv_ext {E₀ : ThreadMap} {τ : Trace} {C : Config}
    (hrun : Run (initConfig E₀) τ C) : ExtInv τ C := by
  refine Run.reverseRecOn (motive := fun τ C => ExtInv τ C) ?_ ?_ hrun
  · -- Inv([], C₀)
    refine
      { ids := inv_ids .nil
        fresh := inv_bbt .nil
        distinct := inv_distinct .nil
        live := inv_closed .nil
        log := inv_log .nil
        logBack := ?_
        cur := ?_
        store := fun x => Or.inr ⟨fun s c hc => by simp [events, CommitEv] at hc, rfl⟩
        ext := ?_
        reads := ?_
        uread := ?_ }
    · -- L⁻: no live transactions
      intro i t Λ Ê hi
      simp [initConfig] at hi
    · -- Cur: no live transactions
      intro i t Λ Ê hi
      simp [initConfig] at hi
    · -- P([]): no transactions
      intro T hT
      obtain ⟨t, ⟨e, he, -⟩, -⟩ := hT
      cases he
    · -- R([], C₀): no live transactions
      intro i t Λ Ê hi
      simp [initConfig] at hi
    · -- U([]): no events
      intro e x v t he
      cases he
  · -- Inv(τ, C) ∧ C --ℓ--> C'  →  Inv(τ ++ [ℓ], C')
    intro ls C ℓ C' hrun ih hstep
    -- the run extended by the new step
    have hrun' : Run (initConfig E₀) (ls ++ [ℓ]) C' := hrun.snoc hstep
    refine
      { ids := inv_ids hrun'
        fresh := inv_bbt hrun'
        distinct := inv_distinct hrun'
        live := inv_closed hrun'
        log := inv_log hrun'
        logBack := ?_
        cur := ?_
        store := ?_
        ext := ?_
        reads := ?_
        uread := ?_ }
    · -- L⁻. mine = the stepping thread's log; others = every other live log
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 mine          others
        | begin _ _        => exact lb_begin  ih.logBack                                -- new log       frame
        | getLog _ _ _     => exact lb_getLog ih.logBack                                -- unchanged     frame
        | getMem hi _ _ _  => exact lb_getMem ih.logBack hi                             -- n accesses l  frame
        | setLog hi hl _   => exact lb_setLog ih.logBack hi hl                          -- entry kept    frame
        | setMem hi _ _ _  => exact lb_setMem ih.logBack hi                             -- n accesses l  frame
        | commit _ _ _     => exact lb_end    ih.logBack                                -- leaves        frame
        | adm _            => exact lb_adm    ih.logBack                                -- no event
      | kcasRetry _ _ _ _  => exact lb_end    ih.logBack                                -- leaves        frame
      | retry _ _ _        => exact lb_end    ih.logBack                                -- leaves        frame
    · -- Cur. mine = the stepping thread's log; others = every other live log
      have hu := (inv_ids hrun').2
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 mine          others
        | begin _ _        => exact cur_begin  hu ih.cur                                -- new log       no set
        | getLog _ _ _     => exact cur_getLog hu ih.cur                                -- unchanged     no set
        | getMem hi hl _ _ => exact cur_getMem hu ih.cur ih.distinct ih.log hi hl       -- (v,v) at l    other tag
        | setLog hi _ _    => exact cur_set    hu ih.cur ih.distinct hi                 -- (o,v) at l    other tag
        | setMem hi _ _ _  => exact cur_set    hu ih.cur ih.distinct hi                 -- (u,v) at l    other tag
        | commit _ _ _     => exact cur_commit hu ih.cur                                -- leaves        no set
        | adm _            => exact cur_adm    ih.cur                                   -- no event
      | kcasRetry _ _ _ _  => exact cur_retry  hu ih.cur                                -- leaves        no set
      | retry _ _ _        => exact cur_retry  hu ih.cur                                -- leaves        no set
    · -- Store. σ = the shared store; writers = committed writers of each x
      have hu := (inv_ids hrun').2
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 σ             writers
        | begin _ _        => exact store_begin  hu ih.store                            -- unchanged     no set
        | getLog _ _ _     => exact store_get    hu ih.store                            -- unchanged     no set
        | getMem _ _ _ _   => exact store_get    hu ih.store                            -- unchanged     no set
        | setLog hi _ _    => exact store_set    hu ih.store (ih.live _ _ _ _ hi)       -- unchanged     t live
        | setMem hi _ _ _  => exact store_set    hu ih.store (ih.live _ _ _ _ hi)       -- unchanged     t live
        | commit hi hok _  => exact store_commit hu ih.store (ih.cur _ _ _ _ hi)        -- apply Λ       t joins
                                (ih.log _ _ _ _ hi) hok
        | adm _            => exact store_adm    ih.store                               -- no event
      | kcasRetry _ _ _ _  => exact store_retry  hu ih.store                            -- unchanged     no end
      | retry _ _ _        => exact store_retry  hu ih.store                            -- unchanged     no end
    · -- P. Com = the committed transactions (L3: unchanged, or grows by {t} at commit)
      have hu := (inv_ids hrun').2
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 Com           why
        | begin _ _        => exact ext_begin hu ih.ext ih.fresh.1                      -- unchanged     fresh tag (F)
        | getLog hi _ _    => exact ext_get   hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
        | getMem hi _ _ _  => exact ext_get   hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
        | setLog hi _ _    => exact ext_set   hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
        | setMem hi _ _ _  => exact ext_set   hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
        | commit hi hok _  => exact ext_end   hu ih.ext (ih.live _ _ _ _ hi)            -- ∪ {t}         R, KCasOk,
                                (ih.reads _ _ _ _ hi) hok ih.store                      --               Store
        | adm _            => exact ext_adm   ih.ext                                    -- no event
      | kcasRetry _ hi _ _ => exact ext_retry hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
      | retry _ hi _       => exact ext_retry hu ih.ext (ih.live _ _ _ _ hi)            -- unchanged     t live (T)
    · -- R. mine = the stepping thread's log; others = every other live log
      have hu := (inv_ids hrun').2
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 mine          others
        | begin _ _        => exact reads_begin  hu ih.reads ih.fresh.1                 -- new log       no get
        | getLog hi hl _   => exact reads_getLog hu ih.reads ih.distinct ih.cur hi hl   -- c = o by Cur  other tag
        | getMem hi hl _ _ => exact reads_getMem hu ih.reads ih.distinct ih.log hi hl   -- (v,v) at l    other tag
        | setLog hi hl _   => exact reads_setLog hu ih.reads hi hl                      -- o kept        no get
        | setMem hi hl _ _ => exact reads_setMem hu ih.reads ih.log hi hl               -- l unread (L)  no get
        | commit _ _ _     => exact reads_commit hu ih.reads                            -- leaves        no get
        | adm _            => exact reads_adm    ih.reads                               -- no event
      | kcasRetry _ _ _ _  => exact reads_retry  hu ih.reads                            -- leaves        no get
      | retry _ _ _        => exact reads_retry  hu ih.reads                            -- leaves        no get
    · -- U. new read = the step's own get, if external; old reads = every earlier one
      have hu := (inv_ids hrun').2
      cases hstep with
      | ctx _ hh =>
        cases hh with
        --                                                                                 new read      old reads
        | begin _ _        => exact u_begin  hu ih.uread ih.fresh.1                     -- none          fresh tag (F)
        | getLog hi hl _   => exact u_getLog hu ih.uread (ih.live _ _ _ _ hi)           -- not ext (L⁻)  t live (T)
                                (ih.logBack _ _ _ _ hi) hl
        | getMem hi _ hσ _ => exact u_getMem hu ih.uread (ih.live _ _ _ _ hi)           -- σ(l) (Store)  t live (T)
                                ih.store hσ
        | setLog hi _ _    => exact u_set    hu ih.uread (ih.live _ _ _ _ hi)           -- none          t live (T)
        | setMem hi _ _ _  => exact u_set    hu ih.uread (ih.live _ _ _ _ hi)           -- none          t live (T)
        | commit hi _ _    => exact u_commit hu ih.uread (ih.live _ _ _ _ hi)           -- none          t live (T)
        | adm _            => exact u_adm    ih.uread                                   -- no event
      | kcasRetry _ hi _ _ => exact u_retry  hu ih.uread (ih.live _ _ _ _ hi)           -- none          t live (T)
      | retry _ hi _       => exact u_retry  hu ih.uread (ih.live _ _ _ _ hi)           -- none          t live (T)

-- `Ext_c` for the witness history: the projection `Inv(τ, C) → P(τ)`.
theorem extC_witness {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : (witness τ).ExtC :=
  (inv_ext hrun).ext

-- `Ext_u` for the witness history: the projection `Inv(τ, C) → U → Ext_u`.
theorem extU_witness {E₀ : ThreadMap} {τ : Trace} {C' : Config}
    (hrun : Run (initConfig E₀) τ C') : (witness τ).ExtU (visOf (events τ)) :=
  History.extU_of_extOp (extOp_of_uinv (inv_ext hrun).uread)

end Optimistic
