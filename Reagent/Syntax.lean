/-
  Reagent — full core language.

  Abstract syntax, evaluation contexts, and configurations, following
  `docs/reagent-correctness.tex` §Abstract syntax and §Evaluation contexts.

  Commands are expressions (`e ::= … | c`), so there is no separate `Cmd` type:
  `set(l, e)` takes an *expression* argument, which the context `set(l, ECtx)`
  evaluates to a value before `Set` may fire.

  Configurations are the document's six-tuple `⟨σ, λ, θ, E, σ̂, Ê⟩` — `retry`
  needs the snapshot `σ̂` to roll the store back and the saved body `Ê` to
  re-run — together with the counter that mints fresh transaction ids.
-/

namespace Reagent

/-- Shared mutable locations. -/
abbrev Loc  : Type := Nat
/-- Transaction identifiers. -/
abbrev TxId : Type := Nat
/-- Thread identifiers. -/
abbrev ThId : Type := Nat
/-- Immutable, `let`-bound variables. -/
abbrev Var  : Type := Nat
/-- The shared store `σ : Loc → ℕ`. -/
abbrev Store : Type := Loc → Nat

/-- Values `v ::= n | () | true | false`. -/
inductive Val where
  | num  : Nat → Val
  | unit : Val
  | bool : Bool → Val
deriving DecidableEq, Repr

/-- Expressions

`e ::= v | x | e₁ + e₂ | e₁ == e₂ | let x = e₁ in e₂ | if e then e₁ else e₂
     | e₁ ; e₂ | get(l) | set(l,e) | begin | end | retry`

The last five are the commands `c`, which the grammar folds into `e`. The store
is ℕ-valued, so only a `num` may be written by `set`. -/
inductive Expr where
  | val   : Val → Expr                    -- v
  | var   : Var → Expr                    -- x
  | add   : Expr → Expr → Expr            -- e₁ + e₂
  | eqv   : Expr → Expr → Expr            -- e₁ == e₂
  | letx  : Var → Expr → Expr → Expr      -- let x = e₁ in e₂
  | ite   : Expr → Expr → Expr → Expr     -- if e then e₁ else e₂
  | seq   : Expr → Expr → Expr            -- e₁ ; e₂
  | getc  : Loc → Expr                    -- get(l)
  | setc  : Loc → Expr → Expr             -- set(l, e)
  | begin : Expr                          -- begin
  | eend  : Expr                          -- end
  | retry : Expr                          -- retry
deriving DecidableEq, Repr

/-- Substitution `e[v/x]`, used by the `let` reduction. Substituting a *value*
means there is nothing to capture, so the only care needed is shadowing: a
`let` that rebinds `x` stops the substitution in its body. -/
def Expr.subst (x : Var) (v : Val) : Expr → Expr
  | .val w      => .val w
  | .var y      => if y = x then .val v else .var y
  | .add a b    => .add (a.subst x v) (b.subst x v)
  | .eqv a b    => .eqv (a.subst x v) (b.subst x v)
  | .letx y a b => .letx y (a.subst x v) (if y = x then b else b.subst x v)
  | .ite c a b  => .ite (c.subst x v) (a.subst x v) (b.subst x v)
  | .seq a b    => .seq (a.subst x v) (b.subst x v)
  | .getc l     => .getc l
  | .setc l a   => .setc l (a.subst x v)
  | .begin      => .begin
  | .eend       => .eend
  | .retry      => .retry

/-- Evaluation contexts

`ECtx ::= [·] | ECtx ; e | let x = ECtx in e | ECtx + e | v + ECtx | ECtx == e | v == ECtx
     | if ECtx then e else e | set(l, ECtx)`

an expression with a single hole marking where the next reduction happens.
Named `Ctx`, kept deliberately apart from `E : ThreadMap` — the two are distinct
objects. The `v + ECtx` and `v == ECtx` forms are what make evaluation left-to-right:
the right operand is reached only once the left is a value. -/
inductive Ctx where
  | hole  : Ctx                           -- [·]
  | seq   : Ctx → Expr → Ctx              -- ECtx ; e
  | letx  : Var → Ctx → Expr → Ctx        -- let x = ECtx in e
  | addL  : Ctx → Expr → Ctx              -- ECtx + e
  | addR  : Val → Ctx → Ctx               -- v + ECtx
  | eqL   : Ctx → Expr → Ctx              -- ECtx == e
  | eqR   : Val → Ctx → Ctx               -- v == ECtx
  | ite   : Ctx → Expr → Expr → Ctx       -- if ECtx then e₁ else e₂
  | setc  : Loc → Ctx → Ctx               -- set(l, ECtx)
deriving DecidableEq, Repr

/-- `ECtx[e]`: plug `e` into the hole. -/
def Ctx.plug : Ctx → Expr → Expr
  | .hole,        e => e
  | .seq K e',    e => .seq (K.plug e) e'
  | .letx x K e', e => .letx x (K.plug e) e'
  | .addL K e',   e => .add (K.plug e) e'
  | .addR v K,    e => .add (.val v) (K.plug e)
  | .eqL K e',    e => .eqv (K.plug e) e'
  | .eqR v K,     e => .eqv (.val v) (K.plug e)
  | .ite K e₁ e₂, e => .ite (K.plug e) e₁ e₂
  | .setc l K,    e => .setc l (K.plug e)

/-- Split an expression into its evaluation context and the redex that context
locates: `e.split = some (K, r)` means `e = ECtx[r]` and `r` is where the next
step happens.

This is the recovery function for `K`. The context is not stored anywhere — a
configuration holds the *plugged* expression `ECtx[r]` — so `split` is what
takes it apart again. `split_plug` below says it takes it apart correctly.

`none` means there is nothing to do: the expression is a value, or it is stuck.
Stuck expressions are not an oversight — an ill-formed `get(l)` reached with no
enclosing `begin` decomposes fine but has no rule to fire, which is how the
document makes well-formedness structural (§"Worked example"). Cases here that
are stuck outright, with no redex at all: a free variable, a bare `begin`
(whose rule needs the redex `begin ; e`), and a non-unit value in statement
position such as `5 ; e`.

Note `split` is a purely syntactic notion: it locates a *potential* redex.
Whether a rule actually fires there depends on the machine state — `Get` still
needs `λ = i`. -/
def Expr.split : Expr → Option (Ctx × Expr)
  | .val _  => none
  | .var _  => none
  | .begin  => none
  | .eend   => some (.hole, .eend)
  | .retry  => some (.hole, .retry)
  | .getc l => some (.hole, .getc l)
  | .add a b =>
      match a, b with
      | .val _, .val _ => some (.hole, .add a b)
      | .val v, _      => (b.split).map (fun p => (.addR v p.1, p.2))
      | _, _           => (a.split).map (fun p => (.addL p.1 b, p.2))
  | .eqv a b =>
      match a, b with
      | .val _, .val _ => some (.hole, .eqv a b)
      | .val v, _      => (b.split).map (fun p => (.eqR v p.1, p.2))
      | _, _           => (a.split).map (fun p => (.eqL p.1 b, p.2))
  | .letx x a b =>
      match a with
      | .val _ => some (.hole, .letx x a b)
      | _      => (a.split).map (fun p => (.letx x p.1 b, p.2))
  | .ite c a b =>
      match c with
      | .val _ => some (.hole, .ite c a b)
      | _      => (c.split).map (fun p => (.ite p.1 a b, p.2))
  | .setc l a =>
      match a with
      | .val _ => some (.hole, .setc l a)
      | _      => (a.split).map (fun p => (.setc l p.1, p.2))
  | .seq a b =>
      match a with
      | .begin     => some (.hole, .seq .begin b)
      | .val .unit => some (.hole, .seq (.val .unit) b)
      | .val _     => none
      | _          => (a.split).map (fun p => (.seq p.1 b, p.2))

/-- **`split` is sound**: what it takes apart, `plug` puts back together. -/
theorem Expr.split_plug : ∀ {e : Expr} {K : Ctx} {r : Expr},
    e.split = some (K, r) → K.plug r = e := by
  intro e
  induction e with
  | val v => intro K r h; simp [Expr.split] at h
  | var x => intro K r h; simp [Expr.split] at h
  | begin => intro K r h; simp [Expr.split] at h
  | eend => intro K r h; simp [Expr.split] at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
  | retry => intro K r h; simp [Expr.split] at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
  | getc l => intro K r h; simp [Expr.split] at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
  | add a b iha ihb =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · rcases hb : b.split with _ | ⟨K', r'⟩ <;> rw [hb] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, ihb hb]
    · rcases ha : a.split with _ | ⟨K', r'⟩ <;> rw [ha] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, iha ha]
  | eqv a b iha ihb =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · rcases hb : b.split with _ | ⟨K', r'⟩ <;> rw [hb] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, ihb hb]
    · rcases ha : a.split with _ | ⟨K', r'⟩ <;> rw [ha] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, iha ha]
  | letx x a b iha ihb =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · rcases ha : a.split with _ | ⟨K', r'⟩ <;> rw [ha] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, iha ha]
  | ite c a b ihc iha ihb =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · rcases hc : c.split with _ | ⟨K', r'⟩ <;> rw [hc] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, ihc hc]
  | setc l a iha =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · rcases ha : a.split with _ | ⟨K', r'⟩ <;> rw [ha] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, iha ha]
  | seq a b iha ihb =>
    intro K r h
    simp only [Expr.split] at h
    split at h
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · simp at h; obtain ⟨hK, hr⟩ := h; subst hK; subst hr; rfl
    · simp at h
    · rcases ha : a.split with _ | ⟨K', r'⟩ <;> rw [ha] at h <;> simp at h
      obtain ⟨hK, hr⟩ := h; subst hK; subst hr
      simp [Ctx.plug, iha ha]

/-- `r` is a *redex*: `split` locates `r` itself, under the empty context. -/
def Expr.IsRedex (r : Expr) : Prop := r.split = some (.hole, r)

theorem Ctx.plug_eq_val {K : Ctx} {r : Expr} {w : Val} (h : K.plug r = .val w) :
    K = .hole ∧ r = .val w := by
  cases K <;> simp [Ctx.plug] at h ⊢ <;> exact h

theorem Ctx.plug_eq_begin {K : Ctx} {r : Expr} (h : K.plug r = .begin) :
    K = .hole ∧ r = .begin := by
  cases K <;> simp [Ctx.plug] at h ⊢ <;> exact h

/-- A redex is never a value, and never a bare `begin` — both split to `none`. -/
theorem Expr.IsRedex.ne_val {r : Expr} (h : r.IsRedex) (w : Val) : r ≠ .val w := by
  intro hw; rw [hw] at h; simp [Expr.IsRedex, Expr.split] at h

theorem Expr.IsRedex.ne_begin {r : Expr} (h : r.IsRedex) : r ≠ .begin := by
  intro hb; rw [hb] at h; simp [Expr.IsRedex, Expr.split] at h

/-- **Decomposition is unique.** If `e` factors as `ECtx[r]` with `r` a redex,
then `split` finds *that* factorisation — there is no other.

Together with `split_plug` this says `split` is the inverse of `plug` on redexes,
so the context in `Trans.ctx` is not a choice: it is a function of the thread's
expression. -/
theorem Expr.split_of_plug : ∀ (K : Ctx) {r : Expr}, r.IsRedex → (K.plug r).split = some (K, r) := by
  intro K
  induction K with
  | hole => intro r h; exact h
  | seq K' e' ih =>
    intro r h
    show (Expr.seq (K'.plug r) e').split = _
    simp only [Expr.split]
    have hb : K'.plug r ≠ .begin := fun hc =>
      (h.ne_begin) (Ctx.plug_eq_begin hc).2
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc =>
      (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› hb
    · exact absurd ‹_› (hv _)
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl
  | letx x K' e' ih =>
    intro r h
    show (Expr.letx x (K'.plug r) e').split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl
  | addL K' e' ih =>
    intro r h
    show (Expr.add (K'.plug r) e').split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl
  | addR v K' ih =>
    intro r h
    show (Expr.add (.val v) (K'.plug r)).split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · simp_all [ih h]
    · simp_all
  | eqL K' e' ih =>
    intro r h
    show (Expr.eqv (K'.plug r) e').split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl
  | eqR v K' ih =>
    intro r h
    show (Expr.eqv (.val v) (K'.plug r)).split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · simp_all [ih h]
    · simp_all
  | ite K' e₁ e₂ ih =>
    intro r h
    show (Expr.ite (K'.plug r) e₁ e₂).split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl
  | setc l K' ih =>
    intro r h
    show (Expr.setc l (K'.plug r)).split = _
    simp only [Expr.split]
    have hv : ∀ w, K'.plug r ≠ .val w := fun w hc => (h.ne_val w) (Ctx.plug_eq_val hc).2
    split
    · exact absurd ‹_› (hv _)
    · rw [ih h]; rfl

/-- Uniqueness, stated directly: two decompositions of the same expression into
a context and a redex are equal. -/
theorem Ctx.plug_inj {K₁ K₂ : Ctx} {r₁ r₂ : Expr}
    (h₁ : r₁.IsRedex) (h₂ : r₂.IsRedex) (h : K₁.plug r₁ = K₂.plug r₂) :
    K₁ = K₂ ∧ r₁ = r₂ := by
  have e₁ := Expr.split_of_plug K₁ h₁
  have e₂ := Expr.split_of_plug K₂ h₂
  rw [h, e₂] at e₁
  have := Option.some.inj e₁
  exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩

/-- The redex `split` locates, forgetting the context. -/
def Expr.redex (e : Expr) : Option Expr := (e.split).map Prod.snd

/-- `e` with its redex replaced by `r'`; the identity if `e` has no redex.
This is `plug` without ever naming the context — `split` supplies it. -/
def Expr.replace (e : Expr) (r' : Expr) : Expr :=
  match e.split with
  | some (K, _) => K.plug r'
  | none        => e

@[simp] theorem Expr.redex_plug {K : Ctx} {r : Expr} (h : r.IsRedex) :
    (K.plug r).redex = some r := by
  simp [Expr.redex, Expr.split_of_plug K h]

@[simp] theorem Expr.replace_plug {K : Ctx} {r : Expr} (h : r.IsRedex) (r' : Expr) :
    (K.plug r).replace r' = K.plug r' := by
  simp [Expr.replace, Expr.split_of_plug K h]

/-- A thread map `E : ThId → Expr`. -/
abbrev ThreadMap : Type := ThId → Expr

/-- Pointwise update `f[a ↦ b]`. -/
def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a' = a then b else f a'

@[simp] theorem update_other {α β : Type} [DecidableEq α] (f : α → β) (a a' : α)
    (b : β) (hne : a ≠ a') : update f a b a' = f a' := by
  simp [update, hne.symm]

/-- The all-zero initial store `σ₀`. -/
def Store.init_store : Store := fun _ => 0

/-- A configuration `⟨σ, λ, θ, E, σ̂, Ê⟩` together with the freshness counter:

* `store`        – the shared store `σ`;
* `activeThread` – `λ`, the thread holding the lock (`none` is `⊥`);
* `activeTx`     – `θ`, the live transaction id (`none` is `⊥`);
* `threadMap`    – the thread map `E`;
* `snapshot`     – `σ̂`, the store as it was when the live transaction began;
* `savedBody`    – `Ê`, the body to re-run after an abort;
* `nextTx`       – the id `Begin` mints next.

The rules maintain `activeThread = ⊥ ↔ activeTx = ⊥`. `Begin` records `σ̂` and
`Ê`; `Retry` rolls the store back to `σ̂` and re-arms the thread as `begin ; Ê`.

`nextTx` is how the `t_fresh` premise of `Begin` is realised: no id is ever
reused. That is not decoration — internal consistency is false without it, since
a reused id would splice two unrelated attempts into one "transaction" whose
read contradicts its own earlier write. It is also what keeps a retried attempt
a *separate* transaction from the attempt it replaces. -/
structure Config where
  store        : Store          -- σ
  activeThread : Option ThId    -- λ
  activeTx     : Option TxId    -- θ
  threadMap    : ThreadMap      -- E
  snapshot     : Store          -- σ̂
  savedBody    : Expr           -- Ê
  nextTx       : TxId

end Reagent
