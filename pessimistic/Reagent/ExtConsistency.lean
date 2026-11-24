import Reagent.ExtInvariants

namespace Reagent


-- NOTE
def Transaction.ExternalRead (T : Transaction) (x : Loc) (n : Nat) (e : Subtype T.E) : Prop :=
  (∃ t, e.val.label = .get x n t) ∧ ¬ ∃ a, T.PriorAccess x a e

-- NOTE a transaction `t` writes `v` to `x`
def Transaction.LastWrite (T : Transaction) (x : Loc) (v : Nat) : Prop :=
  ∃ a : Subtype T.E, (∃ t, a.val.label = .set x v t) ∧
    ¬ ∃ b : Subtype T.E, T.po a b ∧ (∃ u w, b.val.label = .set x w u)

-- NOTE totality is what makes ∃ S and assymetry makes it unique
def History.LatestWriter (H : History) (x : Loc) (S T : Transaction) : Prop :=
  H.txs S ∧ S.status = .Committed ∧ H.ar S T ∧ S ≠ T ∧ (∃ v, S.LastWrite x v) ∧
    ∀ U, H.txs U → U.status = .Committed → U ≠ T → H.ar S U → H.ar U T →
      (∃ v, U.LastWrite x v) → U = S

-- NOTE nothing committed writes before `x`
def History.NoWriterBefore (H : History) (x : Loc) (T : Transaction) : Prop :=
  ¬ ∃ S, H.LatestWriter x S T

-- NOTE
-- Entry point of the algorithm. We are modelling the following
-- ∀ T = (E,po) ∈ H. ∀ e ∈ E. ∀ x, n.
-- ( e = (_, get(x,n)) ∧ po⁻¹(e) ∩ HEventₓ = Φ ) ⇒
--      (W = φ ∧ max_ar(W) ⊢ Write(x,n))
--      ∨ (W = φ ∧ n = σ₀(x))
--
-- where
-- TODO Maybe discuss this next time :: S cannot be anything here, it has to be
-- committed. Even if its retried or uncommitted we will get wrong answer for Ext.
-- The counter example is in the notebook.
-- W = { S ∈ H | S committed, S ≠ T, S ar T, S writes x }
-- S ⊢ Write(x,v) ⇔ max_po(S ∩ HEvent_set(x)) = (_, set(x,v))
--
-- ( e = (_, get(x,n)) ∧ po⁻¹(e) ∩ HEventₓ = Φ ) = External Read
-- S ⊢ Write(x,v) :: LastWrite
-- S = max_ar(w) :: LatestWriter
-- W = φ :: NoWriterBefore
def History.Ext (H : History) : Prop :=
  ∀ T, H.txs T  →
    ∀ (x : Loc) (n : Nat) (e : Subtype T.E), T.ExternalRead x n e →
      (∃ S, H.LatestWriter x S T ∧ S.LastWrite x n)
        ∨ (H.NoWriterBefore x T ∧ n = Store.init_store x)


-- NOTE we are running a ∀ `H` only because ext in this case has to be quantized.
theorem ext_of_run {E₀ : ThreadMap} {τ : Trace} {C' : Config} {H : History}
    (hrun : Run (initConfig E₀) τ C') (hH : HistoryOf τ H) : H.Ext := by
  have hHc := hH
  obtain ⟨htxs, -, -, -, hrt⟩ := hHc
  intro T hT x n e hext
  obtain ⟨t, ⟨e₀, he₀, he₀t⟩, rfl⟩ := (htxs T).mp hT
  obtain ⟨⟨t', hlab⟩, hnoprior⟩ := hext
  have het : e.val.label.tx = t := e.property.2.1
  have htt : t' = t := by rw [hlab] at het; exact het
  subst htt
  have hem : e.val ∈ events τ := e.property.1
  have hte : ∃ b ∈ events τ, b.label.tx = t' := ⟨e.val, hem, het⟩
  -- NOTE the read is external, so its transaction has touched `x` in no way at all
  have hnp : NoPriorAccess (events τ) t' x e.val := by
    rintro ⟨a, ham, hat, hax, hae⟩
    exact hnoprior ⟨⟨a, ham, hat, isAccess_of_accesses hax⟩, hae, hax⟩
  rcases inv_ext hrun x n t' e.val hem hlab hnp with ⟨w, ⟨hcwb, hmax⟩, hval⟩ | ⟨hnone, hinit⟩
  · -- NOTE somebody committed a write to `x` before the read; that transaction is `S`
    obtain ⟨hwm, ⟨v, s, hwset, c, hcm, hcl, hce⟩, hwe⟩ := hcwb
    have hvn : v = n := by rw [hwset] at hval; simpa [Label.accessVal] using hval
    subst hvn
    have hws : w.label.tx = s := by rw [hwset]; rfl
    have hwacc : w.label.isAccess = true := by rw [hwset]; rfl
    have hsocc : ∃ a ∈ events τ, a.label.tx = s := ⟨w, hwm, hws⟩
    -- AI `s` is not the reader: a write of its own would have been a prior access
    have hst : s ≠ t' := by
      intro hc
      exact hnp ⟨w, hwm, by rw [hws, hc], by rw [hwset]; simp [Label.accesses], hwe⟩
    have hST : H.txs (transactionOf (events τ) s) := (htxs _).mpr ⟨s, hsocc, rfl⟩
    have hTT : H.txs (transactionOf (events τ) t') := (htxs _).mpr ⟨t', hte, rfl⟩
    -- AI `s` ran entirely before the reader
    have hblock : BlockBefore (events τ) s t' := by
      rcases inv_block hrun s t' hst with hb | hb
      · exact hb
      · exact absurd (OccursBefore.trans (inv_ids hrun).2 hwe (hb e.val hem het w hwm hws))
          (OccursBefore.irrefl (inv_ids hrun).2)
    have harST : H.ar (transactionOf (events τ) s) (transactionOf (events τ) t') :=
      hrt _ _ hST hTT (fun hc => hst (congrArg Transaction.txid hc))
        (rtb_of_block hrun hsocc hte hst hblock)
    have hwE : (transactionOf (events τ) s).E w := ⟨hwm, hws, hwacc⟩
    -- AI `w` is the last thing `s` wrote to `x`: a later one would also have been
    -- AI committed before the read, and `w` was the last of those
    have hlast : ¬ ∃ b : Subtype (transactionOf (events τ) s).E,
        (transactionOf (events τ) s).po ⟨w, hwE⟩ b ∧ ∃ u w', b.val.label = .set x w' u := by
      rintro ⟨b, hpo, u, w', hbset⟩
      have hbs : b.val.label.tx = s := b.property.2.1
      rw [hbset] at hbs
      have hbs' : u = s := hbs
      exact hmax b.val ⟨b.property.1, ⟨w', s, by rw [hbset, hbs'], c, hcm, hcl, hce⟩,
        hblock b.val b.property.1 b.property.2.1 e.val hem het⟩ hpo
    refine Or.inl ⟨transactionOf (events τ) s,
      ⟨hST, committed_of_eend hcm hcl, harST,
        fun hc => hst (congrArg Transaction.txid hc), ⟨v, ⟨w, hwE⟩, ⟨s, hwset⟩, hlast⟩, ?_⟩,
      ⟨w, hwE⟩, ⟨s, hwset⟩, hlast⟩
    -- and it is the *latest* such: anything `ar`-between would contradict that
    rintro U hU hUcom hUT harSU harUT ⟨vu, b, ⟨u, hbset⟩, -⟩
    obtain ⟨uu, ⟨f, hf, hfu⟩, rfl⟩ := (htxs U).mp hU
    by_cases hus : uu = s
    · rw [hus]
    · exfalso
      have hbm : b.val ∈ events τ := b.property.1
      have hbu : b.val.label.tx = uu := b.property.2.1
      have huocc : ∃ a ∈ events τ, a.label.tx = uu := ⟨b.val, hbm, hbu⟩
      have hut : uu ≠ t' := fun hc => hUT (by rw [hc])
      obtain ⟨cu, hcum, hcul⟩ := eend_of_committed hUcom
      have hbU : BlockBefore (events τ) uu t' := block_of_ar hrun hH huocc hte hut harUT
      have hbSU : BlockBefore (events τ) s uu :=
        block_of_ar hrun hH hsocc huocc (fun hc => hus hc.symm) harSU
      rw [hbset] at hbu
      have hbu' : u = uu := hbu
      exact hmax b.val
        ⟨hbm, ⟨vu, uu, by rw [hbset, hbu'], cu, hcum, hcul,
            hbU cu hcum (by rw [hcul]; rfl) e.val hem het⟩,
          hbU b.val hbm b.property.2.1 e.val hem het⟩
        (hbSU w hwm hws b.val hbm b.property.2.1)
  · -- AI nobody had committed a write to `x`, so the read saw the initial store
    refine Or.inr ⟨?_, hinit⟩
    rintro ⟨S, hSTx, hScom, harST, hSne, ⟨v, a, ⟨s', haset⟩, -⟩, -⟩
    obtain ⟨s, ⟨g, hg, hgs⟩, rfl⟩ := (htxs S).mp hSTx
    have ham : a.val ∈ events τ := a.property.1
    have has : a.val.label.tx = s := a.property.2.1
    have hss : s' = s := by rw [haset] at has; exact has
    subst hss
    have hsocc : ∃ b ∈ events τ, b.label.tx = s' := ⟨a.val, ham, has⟩
    have hst : s' ≠ t' := fun hc => hSne (by rw [hc])
    have hblock : BlockBefore (events τ) s' t' := block_of_ar hrun hH hsocc hte hst harST
    obtain ⟨c, hcm, hcl⟩ := eend_of_committed hScom
    exact hnone ⟨a.val, ham, ⟨v, s', haset, c, hcm, hcl,
        hblock c hcm (by rw [hcl]; rfl) e.val hem het⟩,
      hblock a.val ham has e.val hem het⟩

end Reagent
