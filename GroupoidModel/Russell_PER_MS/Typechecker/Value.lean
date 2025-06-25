import GroupoidModel.Russell_PER_MS.Injectivity
import GroupoidModel.Russell_PER_MS.SubstList

/-! # Values, neutral forms, closures, and evaluation environments

This module sets up definitions for normalization by evaluation (NbE).
We define values, neutral forms, closures, and evaluation environments,
as well as well-formedness judgments `WfVal/WfNeut/WfClos/WfEnv` for those.
We relate them to the core syntax with `Val.toExpr/Neut.toExpr/Clos.toExpr/sbOfEnv`.
-/

/-- Shorthand for `List.length` which is used a lot in this file. -/
local notation "‖" l "‖" => List.length l

mutual
/-- Values are produced by the evaluator during NbE.

The value type is obtained by:
1. carving out normal (generally introduction) and neutral (generally elimination) forms
   as sublanguages of expressions
2. replacing the bodies of binders in those languages by unevaluated closures
-/
inductive Val where
  | pi (l l' : Nat) (A : Val) (B : Clos)
  | sigma (l l' : Nat) (A : Val) (B : Clos)
  | lam (l l' : Nat) (A : Val) (b : Clos)
  | pair (l l' : Nat) (B : Clos) (t u : Val)
  | univ (l : Nat)
  /- TODO: to make the theory usable,
  we'll need to treat `code` and `el` as eliminators,
  adding `el (code A) ≡ A` and `code (el a) ≡ a`.
  For now, we treat them as introductions. -/
  | el (a : Val)
  | code (A : Val)
  /-- A neutral form. -/
  | neut (n : Neut)
  deriving Inhabited, Repr, Lean.ToExpr

/-- Neutral forms are elimination forms that are 'stuck',
i.e., contain no β-reducible subterm. -/
inductive Neut where
  /-- A de Bruijn *level*. -/
  | bvar (i : Nat)
  -- And maybe here?
  | app (l l' : Nat) (A : Val) (B : Clos) (f : Neut) (a : Val)
  /- 2025-06-24: there seems to be no issue with making `A B : Expr`;
  we then don't have to evaluate these types.
  To check equality, it hopefully suffices to check `p =?= p'`
  (equality checks are typed and `A, B` are determined by the type of `p`).
  TODO: also use `Expr` in `app`? What about intro forms: `lam`, `pair`? -/
  | fst (l l' : Nat) (A B : Expr) (p : Neut)
  | snd (l l' : Nat) (A B : Expr) (p : Neut)
  deriving Lean.ToExpr

/-- Recall that given `Γ.A ⊢ b : B` and a substitution `Δ ⊢ env : Γ`,
`Δ.A ⊢ b[(env∘↑).v₀] : B[(env∘↑).v₀]`.
A term closure stores the term `b` together with the substitution `env`.
We may view it as a term which is *almost* well-typed in `Δ`,
except that we are missing one more argument `Δ ⊢ a : A`
to fill in for `v₀` in `b`.

In NbE, closures are the runtime values of binder bodies.

In some NbE implementations, this would be an actual closure `Expr → Expr`;
the present variant is a defunctionalization of that due to Abel. -/
inductive Clos where
  | mk_tp (Γ : Ctx) (A : Expr) (env : List Val) (b : Expr)
  | mk_tm (Γ : Ctx) (l l' : Nat) (A B : Expr) (env : List Val) (b : Expr)
  deriving Lean.ToExpr
end

/-! ## Values as expressions -/

mutual
variable (d : Nat)
/-- The expression corresponding to a value well-typed in a context of length `d`. -/
def Val.toExpr : Val → Expr
  | .pi l l' A B => .pi l l' A.toExpr B.toExpr
  | .sigma l l' A B => .sigma l l' A.toExpr B.toExpr
  | .lam l l' A b => .lam l l' A.toExpr b.toExpr
  | .pair l l' B t u => .pair l l' B.toExpr t.toExpr u.toExpr
  | .univ l => .univ l
  | .el a => .el a.toExpr
  | .code A => .code A.toExpr
  | .neut n => n.toExpr
  termination_by v => sizeOf v

/-- The expression corresponding to a neutral form well-typed in a context of length `d`. -/
def Neut.toExpr : Neut → Expr
  | .bvar l => .bvar (d - l - 1)
  | .app l l' A B f a => .app l l' A.toExpr B.toExpr f.toExpr a.toExpr
  | .fst l l' A B p => .fst l l' A B p.toExpr
  | .snd l l' A B p => .snd l l' A B p.toExpr
  termination_by n => sizeOf n

/-- The expression corresponding to a closure
whose _domain_ is a context of length `d`
(i.e., `Δ ⊢ env : Γ` where `‖Δ‖ = d`).

Remark: we need `WfClos` judgments because this function is not injective:
it forgets the pre-substitution binder body `b/B`,
the environment,
and the additional type information.
Thus, the well-typedness of `C.toExpr` is not enough to conclude that `C` is well-formed. -/
def Clos.toExpr : Clos → Expr
  | .mk_tp _ _ env B => B.subst (Expr.up <| sbOfEnv env)
  | .mk_tm _ _ _ _ _ env b => b.subst (Expr.up <| sbOfEnv env)
  termination_by c => sizeOf c

/-- The substitution corresponding to an evaluation environment
whose _domain_ is a context of length `d`: `Δ ⊢ env : Γ` where `‖Δ‖ = d`.

See also `sbOfTms`. -/
def sbOfEnv (env : List Val) (k := 0) : Nat → Expr :=
  sbOfTms (env.map (·.toExpr)) k
  termination_by sizeOf env
end

/-! ## Substitutions from environments -/

@[autosubst]
theorem sbOfEnv_nil (d) : sbOfEnv d [] = Expr.bvar := by
  simp [sbOfEnv, autosubst]

@[autosubst]
theorem sbOfEnv_cons (d t ts k) :
    sbOfEnv d (t :: ts) k = Expr.snoc (sbOfEnv d ts (k + 1)) (t.toExpr d) := by
  simp [sbOfEnv, autosubst]

theorem sbOfEnv_get_eq {d ts k i} : i < ts.length → sbOfEnv d ts k i = sbOfEnv d ts 0 i := by
  intro h
  unfold sbOfEnv
  apply sbOfTms_get_eq
  simp [h]

theorem WfTp.sbOfEnv_irrel {Γ l A ts} (wf : Γ ⊢[l] A) (le : ‖Γ‖ ≤ ‖ts‖) (d k) :
    A.subst (sbOfEnv d ts k) = A.subst (sbOfEnv d ts 0) := by
  simp [sbOfEnv, wf.sbOfTms_irrel, le]

theorem WfTm.sbOfEnv_irrel {Γ l A t ts} (wf : Γ ⊢[l] t : A) (le : ‖Γ‖ ≤ ‖ts‖) (d k) :
     t.subst (sbOfEnv d ts k) = t.subst (sbOfEnv d ts 0) := by
  simp [sbOfEnv, wf.sbOfTms_irrel, le]

/-! ## Well-formed values -/

mutual
inductive WfValTp : Ctx → Nat → Val → Prop
  | pi {Γ A B l l'} :
    WfValTp Γ l A →
    WfClosTp Γ l l' (A.toExpr ‖Γ‖) B →
    WfValTp Γ (max l l') (.pi l l' A B)
  | sigma {Γ A B l l'} :
    WfValTp Γ l A →
    WfClosTp Γ l l' (A.toExpr ‖Γ‖) B →
    WfValTp Γ (max l l') (.sigma l l' A B)
  | univ {Γ l} :
    WfCtx Γ →
    l < univMax →
    WfValTp Γ (l + 1) (.univ l)
  | el {Γ a l} :
    WfValTm Γ (l + 1) a (.univ l) →
    WfValTp Γ l (.el a)

-- Note: no neutral types atm.

inductive WfValTm : Ctx → Nat → Val → Expr → Prop
  | lam {Γ A B b l l'} :
    WfValTp Γ l A →
    WfClosTm Γ l l' (A.toExpr ‖Γ‖) B b →
    WfValTm Γ (max l l') (.lam l l' A b) (.pi l l' (A.toExpr ‖Γ‖) B)
  | pair {Γ A B t u l l'} :
    WfClosTp Γ l l' A B →
    WfValTm Γ l t A →
    WfValTm Γ l' u (B.toExpr ‖Γ‖ |>.subst (t.toExpr ‖Γ‖).toSb) →
    WfValTm Γ (max l l') (.pair l l' B t u) (.sigma l l' A (B.toExpr ‖Γ‖))
  | code {Γ A l} :
    l < univMax →
    WfValTp Γ l A →
    WfValTm Γ (l + 1) (.code A) (.univ l)
  | neut_tm {Γ A n l} :
    WfNeutTm Γ l n A →
    WfValTm Γ l (.neut n) A
  | conv_nf {Γ A A' v l} :
    WfValTm Γ l v A →
    Γ ⊢[l] A ≡ A' →
    WfValTm Γ l v A'

-- Q: well-scope `Val`/`Neut`? a lot of `‖Γ‖` noise
inductive WfNeutTm : Ctx → Nat → Neut → Expr → Prop
  | bvar {Γ A i l} :
    WfCtx Γ →
    Lookup Γ i A l →
    WfNeutTm Γ l (.bvar (‖Γ‖ - i - 1)) A
  | app {Γ A B f a l l'} :
    WfClosTp Γ l l' (A.toExpr ‖Γ‖) B →
    WfNeutTm Γ (max l l') f (.pi l l' (A.toExpr ‖Γ‖) (B.toExpr ‖Γ‖)) →
    WfValTm Γ l a (A.toExpr ‖Γ‖) →
    WfNeutTm Γ l' (.app l l' A B f a) ((B.toExpr ‖Γ‖).subst (a.toExpr ‖Γ‖).toSb)
  | fst {Γ A B p l l'} :
    (A, l) :: Γ ⊢[l'] B →
    WfNeutTm Γ (max l l') p (.sigma l l' A B) →
    WfNeutTm Γ l (.fst l l' A B p) A
  | snd {Γ A B p l l'} :
    (A, l) :: Γ ⊢[l'] B →
    WfNeutTm Γ (max l l') p (.sigma l l' A B) →
    WfNeutTm Γ l' (.snd l l' A B p) (B.subst (Expr.fst l l' A B (p.toExpr ‖Γ‖)).toSb)
  | conv_neut {Γ A A' n l} :
    WfNeutTm Γ l n A →
    Γ ⊢[l] A ≡ A' →
    WfNeutTm Γ l n A'

/-- `WfClosTp Δ l l' A B` -/
inductive WfClosTp : Ctx → Nat → Nat → Expr → Clos → Prop
  | clos_tp {Δ Γ A B Aenv env l l'} :
    -- The equality argument builds in conversion.
    Δ ⊢[l] A.subst (sbOfEnv ‖Δ‖ env) ≡ Aenv →
    WfEnv Δ env Γ →
    (A, l) :: Γ ⊢[l'] B →
    WfClosTp Δ l l' Aenv (.mk_tp Γ A env B)

/-- `WfClosTm Δ l l' A B b` -/
inductive WfClosTm : Ctx → Nat → Nat → Expr → Expr → Clos → Prop
  | clos_tm {Δ Γ A B Aenv Benv b env l l'} :
    Δ ⊢[l] A.subst (sbOfEnv ‖Δ‖ env) ≡ Aenv →
    (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up (sbOfEnv ‖Δ‖ env)) ≡ Benv →
    WfEnv Δ env Γ →
    (A, l) :: Γ ⊢[l'] b : B →
    WfClosTm Δ l l' Aenv Benv (.mk_tm Γ l l' A B env b)

inductive WfEnv : Ctx → List Val → Ctx → Prop
  /- Possible optimization: allow `WfEnv Γ [] Γ`
  and replace `envOfLen ‖Γ‖` by `[]`. -/
  | nil {Γ} : WfCtx Γ → WfEnv Γ [] []
  | snoc {Δ Γ A v E l} :
    WfEnv Δ E Γ →
    Γ ⊢[l] A →
    WfValTm Δ l v (A.subst (sbOfEnv ‖Δ‖ E)) →
    WfEnv Δ (v :: E) ((A, l) :: Γ)
end

/-! ## Well-formed evaluation environments -/

namespace WfEnv

theorem wf_dom {Δ} : ∀ {E Γ}, WfEnv Δ E Γ → WfCtx Δ := by
  mutual_induction WfEnv
  all_goals grind

theorem wf_cod {Δ} : ∀ {E Γ}, WfEnv Δ E Γ → WfCtx Γ := by
  mutual_induction WfEnv
  all_goals grind [WfCtx.nil, WfCtx.snoc]

theorem eq_length {Δ} : ∀ {E Γ}, WfEnv Δ E Γ → ‖E‖ = ‖Γ‖ := by
  mutual_induction WfEnv
  all_goals intros; try exact True.intro
  all_goals simp; try grind

theorem lookup_lt {Δ Γ E i A l} : WfEnv Δ E Γ → Lookup Γ i A l → i < ‖E‖ :=
  fun env lk => env.eq_length ▸ lk.lt_length

theorem lookup_wf {Δ} : ∀ {E Γ}, (env : WfEnv Δ E Γ) →
    ∀ {A i l}, (lk : Lookup Γ i A l) →
    WfValTm Δ l (E[i]'(env.lookup_lt lk)) (A.subst (sbOfEnv ‖Δ‖ E)) := by
  mutual_induction WfEnv
  all_goals intros; try exact True.intro
  case nil lk => cases lk
  case snoc E A v ih _ _ _ _ lk =>
    rcases lk with _ | ⟨_, _, lk⟩
    . convert v using 1
      autosubst
      rw [A.sbOfEnv_irrel (E.eq_length ▸ Nat.le_refl _)]
    . convert ih lk using 1
      autosubst
      rw [A.wf_ctx.lookup_wf lk |>.sbOfEnv_irrel (E.eq_length ▸ Nat.le_refl _)]

theorem sbOfEnv_app {Δ Γ A E i l} (env : WfEnv Δ E Γ) (lk : Lookup Γ i A l) :
    sbOfEnv ‖Δ‖ E 0 i = (E[i]'(env.lookup_lt lk)).toExpr ‖Δ‖ := by
  simp [sbOfEnv, sbOfTms, List.getElem?_eq_some_iff.mpr ⟨env.lookup_lt lk, rfl⟩]

theorem mk : ∀ {Γ}, WfCtx Γ → ∀ {Δ} {E : List Val}, WfCtx Δ → (eq : ‖Γ‖ = ‖E‖) →
    (∀ {i A l}, (lk : Lookup Γ i A l) →
      WfValTm Δ l (E[i]'(eq ▸ lk.lt_length)) (A.subst (sbOfEnv ‖Δ‖ E))) →
    WfEnv Δ E Γ := by
  mutual_induction WfCtx
  all_goals intros; try exact True.intro
  case nil eq _ =>
    have := List.length_eq_zero_iff.mp eq.symm
    grind [WfEnv.nil]
  case snoc A ih _ _ E Δ eq h =>
    cases E
    . cases eq
    . replace eq := Nat.succ_inj'.mp eq
      apply WfEnv.snoc
      . refine ih Δ eq fun lk => ?_
        convert h (lk.succ ..) using 1; autosubst
        conv => rhs; rw [A.wf_ctx.lookup_wf lk |>.sbOfEnv_irrel <| eq ▸ Nat.le_refl _]
      . assumption
      . convert h (Lookup.zero ..) using 1; autosubst
        conv => rhs; rw [A.sbOfEnv_irrel <| eq ▸ Nat.le_refl _]

end WfEnv

/-! ## Values are well-typed as expressions -/

attribute [local grind] Val.toExpr Neut.toExpr Clos.toExpr in
theorem wf_toExpr {Γ : Ctx} :
    (∀ {l A}, WfValTp Γ l A → Γ ⊢[l] A.toExpr ‖Γ‖) ∧
    (∀ {l t A}, WfValTm Γ l t A → Γ ⊢[l] t.toExpr ‖Γ‖ : A) ∧
    (∀ {l t A}, WfNeutTm Γ l t A → Γ ⊢[l] t.toExpr ‖Γ‖ : A) ∧
    (∀ {l l' A B}, WfClosTp Γ l l' A B → (A, l) :: Γ ⊢[l'] B.toExpr ‖Γ‖) ∧
    (∀ {l l' A B b}, WfClosTm Γ l l' A B b → (A, l) :: Γ ⊢[l'] b.toExpr ‖Γ‖ : B) ∧
    (∀ {E Γ'}, WfEnv Γ E Γ' → ∀ (k), WfSb Γ (sbOfEnv ‖Γ‖ E k) Γ') := by
  mutual_induction WfValTp
  all_goals dsimp; intros
  case pi => grind [WfTp.pi]
  case sigma => grind [WfTp.sigma]
  case univ => grind [WfTp.univ]
  case el => grind [WfTp.el]
  case lam => grind [WfTm.lam]
  case pair => grind [WfTm.pair]
  case code => grind [WfTm.code]
  case neut_tm => grind
  case conv_nf => grind [WfTm.conv]
  case bvar Γ lk =>
    unfold Neut.toExpr
    convert WfTm.bvar Γ lk using 2
    have := lk.lt_length
    omega
  case app => grind [WfTm.app]
  case fst => grind [WfTm.fst]
  case snd => grind [WfTm.snd]
  case conv_neut => grind [WfTm.conv]
  case clos_tp Aenv _ B sb =>
    have := B.subst (sb 0 |>.up B.wf_ctx.inv_snoc)
    have := this.conv_binder Aenv
    convert this using 1
    rw [Clos.toExpr]
  case clos_tm Aenv Benv env b sb =>
    unfold Clos.toExpr
    have := b.subst (sb 0 |>.up b.wf_ctx.inv_snoc)
    have := this.conv_ctx (EqCtx.refl Aenv.wf_ctx |>.snoc Aenv)
    exact this.conv Benv
  case nil => apply WfSb.terminal; assumption
  case snoc E A _ _ _ _ =>
    rw [sbOfEnv_cons]
    apply WfSb.snoc
    . grind
    . grind
    . rw [A.sbOfEnv_irrel (E.eq_length ▸ Nat.le_refl _)]; grind

theorem WfValTp.wf_toExpr {Γ l A} (h : WfValTp Γ l A) : Γ ⊢[l] A.toExpr ‖Γ‖ :=
  _root_.wf_toExpr.1 h

theorem WfValTm.wf_toExpr {Γ l t A} (h : WfValTm Γ l t A) : Γ ⊢[l] t.toExpr ‖Γ‖ : A :=
  _root_.wf_toExpr.2.1 h

theorem WfNeutTm.wf_toExpr {Γ l t A} (h : WfNeutTm Γ l t A) : Γ ⊢[l] t.toExpr ‖Γ‖ : A :=
  _root_.wf_toExpr.2.2.1 h

theorem WfClosTp.wf_toExpr {Γ l l' A B} (h : WfClosTp Γ l l' A B) :
    (A, l) :: Γ ⊢[l'] B.toExpr ‖Γ‖ :=
  _root_.wf_toExpr.2.2.2.1 h

theorem WfClosTm.wf_toExpr {Γ A B b l l'} (h : WfClosTm Γ l l' A B b) :
    (A, l) :: Γ ⊢[l'] b.toExpr ‖Γ‖ : B :=
  _root_.wf_toExpr.2.2.2.2.1 h

theorem WfEnv.wf_sbOfEnv {Δ E Γ} (h : WfEnv Δ E Γ) : WfSb Δ (sbOfEnv ‖Δ‖ E) Γ :=
  _root_.wf_toExpr.2.2.2.2.2 h 0

/-! ## Values are closed under conversion -/

attribute [local grind] EqCtx.length_eq in
theorem conv_ctx {Γ : Ctx} :
    (∀ {l A}, WfValTp Γ l A → ∀ {Γ'}, EqCtx Γ Γ' → WfValTp Γ' l A) ∧
    (∀ {l t A}, WfValTm Γ l t A → ∀ {Γ'}, EqCtx Γ Γ' → WfValTm Γ' l t A) ∧
    (∀ {l t A}, WfNeutTm Γ l t A → ∀ {Γ'}, EqCtx Γ Γ' → WfNeutTm Γ' l t A) ∧
    (∀ {l l' A B}, WfClosTp Γ l l' A B → ∀ {Γ'}, EqCtx Γ Γ' → WfClosTp Γ' l l' A B) ∧
    (∀ {l l' A B b}, WfClosTm Γ l l' A B b → ∀ {Γ'}, EqCtx Γ Γ' → WfClosTm Γ' l l' A B b) ∧
    (∀ {E Δ}, WfEnv Γ E Δ → ∀ {Γ'}, EqCtx Γ Γ' → WfEnv Γ' E Δ) := by
  mutual_induction WfValTp
  all_goals intros; try exact True.intro
  case pi => grind [WfValTp.pi, EqTp.refl_tp]
  case sigma => grind [WfValTp.sigma, EqTp.refl_tp]
  case univ => grind [WfValTp.univ, EqCtx.wf_right]
  case el => grind [WfValTp.el]
  case lam eq =>
    rw [eq.length_eq]
    grind [WfValTm.lam, EqTp.refl_tp]
  case pair eq =>
    rw [eq.length_eq]
    grind [WfValTm.pair]
  case code => grind [WfValTm.code]
  case neut_tm => grind [WfValTm.neut_tm]
  case conv_nf => grind [EqTp.conv_ctx, WfValTm.conv_nf]
  case bvar lk _ eq =>
    have ⟨A', _, lk'⟩ := Lookup.of_lt_length <| eq.length_eq ▸ lk.lt_length
    obtain ⟨rfl, eqA⟩ := eq.lookup_eq lk lk'
    have := WfNeutTm.bvar eq.wf_right lk'
    rw [eq.length_eq]
    exact WfNeutTm.conv_neut this (eqA.symm_tp.conv_ctx eq)
  case app eq =>
    rw [eq.length_eq]
    grind [WfNeutTm.app]
  case fst B _ _ _ eq =>
    apply WfNeutTm.fst (B.conv_ctx <| eq.snoc <| EqTp.refl_tp B.wf_ctx.inv_snoc)
    grind
  case snd B _ _ _ eq =>
    rw [eq.length_eq]
    apply WfNeutTm.snd (B.conv_ctx <| eq.snoc <| EqTp.refl_tp B.wf_ctx.inv_snoc)
    grind
  case conv_neut => grind [EqTp.conv_ctx, WfNeutTm.conv_neut]
  case clos_tp Aeq env _ _ _ eq =>
    rw [eq.length_eq] at Aeq
    grind [WfClosTp.clos_tp, EqTp.conv_ctx]
  case clos_tm Aeq Beq _ _ _ _ eq =>
    rw [eq.length_eq] at Aeq Beq
    apply WfClosTm.clos_tm _ (Beq.conv_ctx _)
    all_goals grind [EqTp.conv_ctx, EqCtx.snoc, EqTp.refl_tp, EqTp.wf_right]
  case nil eq => exact .nil eq.wf_right
  case snoc => grind [WfEnv.snoc]

theorem WfValTp.conv_ctx {Γ Γ' l A} : WfValTp Γ l A → EqCtx Γ Γ' → WfValTp Γ' l A :=
  fun h eq => _root_.conv_ctx.1 h eq

theorem WfValTm.conv_ctx {Γ Γ' l t A} : WfValTm Γ l t A → EqCtx Γ Γ' → WfValTm Γ' l t A :=
  fun h eq => _root_.conv_ctx.2.1 h eq

theorem WfNeutTm.conv_ctx {Γ Γ' l t A} : WfNeutTm Γ l t A → EqCtx Γ Γ' → WfNeutTm Γ' l t A :=
  fun h eq => _root_.conv_ctx.2.2.1 h eq

theorem WfClosTp.conv_ctx {Γ Γ' l l' A B} : WfClosTp Γ l l' A B → EqCtx Γ Γ' →
    WfClosTp Γ' l l' A B :=
  fun h eq => _root_.conv_ctx.2.2.2.1 h eq

theorem WfClosTm.conv_ctx {Γ Γ' l l' A B b} :
    WfClosTm Γ l l' A B b → EqCtx Γ Γ' → WfClosTm Γ' l l' A B b :=
  fun h eq => _root_.conv_ctx.2.2.2.2.1 h eq

theorem WfEnv.conv_dom {Δ Δ' Γ E} : WfEnv Δ E Γ → EqCtx Δ Δ' → WfEnv Δ' E Γ :=
  fun h eq => _root_.conv_ctx.2.2.2.2.2 h eq

/-! ## Environments from contexts -/

/-- An identity evaluation environment (i.e., bvars remain themselves)
for contexts of the given length. -/
def envOfLen (n : Nat) : List Val :=
  /- Recall: we use de Bruijn levels in `Val`,
  so `‖Γ‖ - 1` is the innermost binder. -/
  List.ofFn (n := n) (.neut <| .bvar <| n - · - 1)

@[simp]
theorem length_envOfLen (n : Nat) : ‖envOfLen n‖ = n := by
  simp [envOfLen]

@[simp]
theorem envOfLen_succ (n : Nat) : envOfLen (n + 1) = (.neut <| .bvar n) :: envOfLen n := by
  rw [envOfLen, List.ofFn_succ]
  congr 2
  ext i
  congr 2
  dsimp
  omega

@[autosubst]
theorem sbOfEnv_envOfLen (n : Nat) : sbOfEnv n (envOfLen n) = Expr.bvar := by
  ext i
  simp [sbOfEnv, sbOfTms, envOfLen, Val.toExpr, Neut.toExpr]
  split_ifs <;> simp
  . omega

theorem envOfLen_wf {Γ} : WfCtx Γ → WfEnv Γ (envOfLen ‖Γ‖) Γ := by
  intro Γ
  refine WfEnv.mk Γ Γ (length_envOfLen _).symm fun lk => ?_
  conv => enter [3]; simp only [envOfLen, List.getElem_ofFn]
  apply WfValTm.neut_tm
  apply WfNeutTm.bvar Γ
  convert lk; autosubst

/-! ## Inversion for well-formed values -/

theorem WfValTm.inv_lam {Γ A C b l₀ l l'} : WfValTm Γ l₀ (.lam l l' A b) C →
    l₀ = max l l' ∧ (WfValTp Γ l A) ∧ ∃ B,
      (WfClosTm Γ l l' (A.toExpr ‖Γ‖) B b) ∧ (Γ ⊢[max l l'] C ≡ .pi l l' (A.toExpr ‖Γ‖) B) := by
  suffices
      ∀ {l₀ t C}, WfValTm Γ l₀ t C → ∀ {A b l l'}, t = .lam l l' A b →
        l₀ = max l l' ∧ (WfValTp Γ l A) ∧
          ∃ B, (WfClosTm Γ l l' (A.toExpr ‖Γ‖) B b) ∧
            (Γ ⊢[max l l'] C ≡ .pi l l' (A.toExpr ‖Γ‖) B) from
    fun h => this h rfl
  mutual_induction WfValTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case lam =>
    refine ⟨rfl, by assumption, _, by assumption, ?_⟩
    apply EqTp.cong_pi
    . grind [EqTp.refl_tp, WfValTp.wf_toExpr]
    . rename_i C _ _
      exact EqTp.refl_tp C.wf_toExpr.wf_tp
  case conv_nf =>
    grind [EqTp.symm_tp, EqTp.trans_tp]

theorem WfValTm.inv_pair {Γ B C t u l₀ l l'} : WfValTm Γ l₀ (.pair l l' B t u) C →
    l₀ = max l l' ∧ ∃ A,
      (WfClosTp Γ l l' A B) ∧ (WfValTm Γ l t A) ∧
      (WfValTm Γ l' u (B.toExpr ‖Γ‖ |>.subst (t.toExpr ‖Γ‖).toSb)) ∧
      (Γ ⊢[max l l'] C ≡ .sigma l l' A (B.toExpr ‖Γ‖)) := by
  suffices
      ∀ {l₀ t₀ C}, WfValTm Γ l₀ t₀ C → ∀ {B t u l l'}, t₀ = .pair l l' B t u →
        l₀ = max l l' ∧ ∃ A,
          (WfClosTp Γ l l' A B) ∧
          (WfValTm Γ l t A) ∧
          (WfValTm Γ l' u (B.toExpr ‖Γ‖ |>.subst (t.toExpr ‖Γ‖).toSb)) ∧
          (Γ ⊢[max l l'] C ≡ .sigma l l' A (B.toExpr ‖Γ‖)) from
    fun h => this h rfl
  mutual_induction WfValTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case pair =>
    refine ⟨rfl, _, by assumption, by assumption, by assumption, ?_⟩
    grind [EqTp.refl_tp, WfTp.sigma, WfClosTp.wf_toExpr]
  case conv_nf =>
    grind [EqTp.symm_tp, EqTp.trans_tp]

theorem WfValTm.inv_neut {Γ A t l} : WfValTm Γ l (.neut t) A → WfNeutTm Γ l t A := by
  suffices ∀ {l t A}, WfValTm Γ l t A → ∀ {n}, t = .neut n → (WfNeutTm Γ l n A) from
    fun h => this h rfl
  mutual_induction WfValTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case neut_tm => assumption
  case conv_nf eq _ _ ih => exact ih rfl |>.conv_neut eq
