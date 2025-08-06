import GroupoidModel.Syntax.GCongr
import GroupoidModel.Syntax.Injectivity
import GroupoidModel.Syntax.Synth

/-! # Values, neutral forms, closures, and evaluation environments

This module sets up definitions for normalization by evaluation (NbE).
We define values, neutral forms, closures, and evaluation environments,
as well as well-formedness judgments `WfVal/WfNeut/WfClos/WfEnv` for those.
We relate them to the core syntax with `Val.toExpr/Neut.toExpr/Clos.toExpr/sbOfEnv`.
-/

attribute [local grind]
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqTm.refl_tm EqTm.symm_tm EqTm.trans_tm

mutual
/-- Values are produced by the evaluator during NbE.

The value type is obtained by:
1. carving out normal (generally introduction) and neutral (generally elimination) forms
   as sublanguages of expressions; and
2. replacing the bodies of binders in those languages by unevaluated closures.

## Type annotations

Unlike expressions, values contain no type annotations
except when necessary to implement η laws (`Val.neut` and `Neut.app`)
and to implement `evalValTm` (`Val.lam`).
This is essential for performance:
- if we were to store type annotations as unevaluated `Expr`s,
  weakening would not be free for values; and
- if we were to store them as `Val`ues, we'd have to evaluate them.

Note that we don't need annotations to decide equality:
by uniqueness of typing, lemmas like the following can be proven
```lean4
  Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
  Γ ⊢[l] Expr.fst l l' A B p : A →
  Γ ⊢[l] Expr.fst l l' A' B' p' : A →
  Γ ⊢[l] Expr.fst l l' A B p ≡ Expr.fst l l' A' B' p' : A
```
and hence it suffices to compare the value parts (in this case `p`). -/
inductive Val where
  | pi (l l' : Nat) (A : Val) (B : Clos)
  | sigma (l l' : Nat) (A : Val) (B : Clos)
  | lam (l l' : Nat) (vA : Val) (b : Clos)
  | pair (l l' : Nat) (t u : Val)
  | univ (l : Nat)
  /-- Although `el` is an eliminator,
  as a neutral form it does not need to be annotated with a type
  (because it itself is a type).
  So we embed it in `Val` directly rather than through `Val.neut`. -/
  | el (a : Neut)
  | code (A : Val)
  /-- A neutral form at the given type. -/
  | neut (n : Neut) (A : Val)
  deriving Inhabited

/-- Neutral forms are elimination forms that are 'stuck',
i.e., contain no β-reducible subterm. -/
inductive Neut where
  /-- A de Bruijn *level*. -/
  | bvar (i : Nat)
  /-- Application at the specified argument type. -/
  | app (l l' : Nat) (A : Val) (f : Neut) (a : Val)
  | fst (l l' : Nat) (p : Neut)
  | snd (l l' : Nat) (p : Neut)
  deriving Inhabited

/-- Recall that given `Γ.A ⊢ b : B` and a substitution `Δ ⊢ env : Γ`,
we get `Δ.A[env] ⊢ b[(env∘↑).v₀] : B[(env∘↑).v₀]`.
A closure stores the term `b` or type `B` together with the substitution `env`.
We may view it as *almost* well-typed in `Δ`,
except that we are missing one more argument `Δ ⊢ a : A`
to fill in for `v₀` in `b`/`B`.

In NbE, closures are the runtime values of binder bodies.

In some NbE implementations, this would be a meta-level closure `Expr → Expr`;
the present variant is a defunctionalization due to Abel. -/
inductive Clos where
  | of_val (env : List Val) (v : Val)
  | of_expr (env : List Val) (t : Expr)
  deriving Inhabited
end

/-! ## Relation of values to terms -/

mutual
inductive ValEqTp : Ctx → Nat → Val → Expr → Prop
  | pi {Γ vA A vB B l l'} :
    ValEqTp Γ l vA A →
    ClosEqTp Γ l l' A vB B →
    ValEqTp Γ (max l l') (.pi l l' vA vB) (.pi l l' A B)
  | sigma {Γ vA A vB B l l'} :
    ValEqTp Γ l vA A →
    ClosEqTp Γ l l' A vB B →
    ValEqTp Γ (max l l') (.sigma l l' vA vB) (.sigma l l' A B)
  | univ {Γ l} :
    WfCtx Γ →
    l < univMax →
    ValEqTp Γ (l + 1) (.univ l) (.univ l)
  | el {Γ na a l} :
    NeutEqTm Γ (l + 1) na a (.univ l) →
    ValEqTp Γ l (.el na) (.el a)
  | conv_tp {Γ vA A A' l} :
    ValEqTp Γ l vA A →
    Γ ⊢[l] A ≡ A' →
    ValEqTp Γ l vA A'

-- Note: neutral types are embedded in `Val` directly and don't need a `NeutEqTp` relation.

inductive ValEqTm : Ctx → Nat → Val → Expr → Expr → Prop
  | lam {Γ A B vA vb b l l'} :
    ValEqTp Γ l vA A →
    ClosEqTm Γ l l' A B vb b →
    ValEqTm Γ (max l l') (.lam l l' vA vb) (.lam l l' A b) (.pi l l' A B)
  | pair {Γ A B vt t vu u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    ValEqTm Γ l vt t A →
    ValEqTm Γ l' vu u (B.subst t.toSb) →
    ValEqTm Γ (max l l') (.pair l l' vt vu) (.pair l l' B t u) (.sigma l l' A B)
  | code {Γ vA A l} :
    l < univMax →
    ValEqTp Γ l vA A →
    ValEqTm Γ (l + 1) (.code vA) (.code A) (.univ l)
  | neut_tm {Γ vA A vn n l} :
    ValEqTp Γ l vA A →
    NeutEqTm Γ l vn n A →
    ValEqTm Γ l (.neut vn vA) n A
  | conv_nf {Γ A A' vt t t' l} :
    ValEqTm Γ l vt t A →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] A ≡ A' →
    ValEqTm Γ l vt t' A'

inductive NeutEqTm : Ctx → Nat → Neut → Expr → Expr → Prop
  | bvar {Γ A i l} :
    WfCtx Γ →
    Lookup Γ i A l →
    NeutEqTm Γ l (.bvar (Γ.length - i - 1)) (.bvar i) A
  | app {Γ vA A B vf f va a l l'} :
    ValEqTp Γ l vA A →
    NeutEqTm Γ (max l l') vf f (.pi l l' A B) →
    ValEqTm Γ l va a A →
    NeutEqTm Γ l' (.app l l' vA vf va) (.app l l' B f a) (B.subst a.toSb)
  | fst {Γ A B vp p l l'} :
    NeutEqTm Γ (max l l') vp p (.sigma l l' A B) →
    NeutEqTm Γ l (.fst l l' vp) (.fst l l' A B p) A
  | snd {Γ A B vp p l l'} :
    NeutEqTm Γ (max l l') vp p (.sigma l l' A B) →
    NeutEqTm Γ l' (.snd l l' vp) (.snd l l' A B p) (B.subst (Expr.fst l l' A B p).toSb)
  | conv_neut {Γ A A' vn n n' l} :
    NeutEqTm Γ l vn n A →
    Γ ⊢[l] n ≡ n' : A →
    Γ ⊢[l] A ≡ A' →
    NeutEqTm Γ l vn n' A'

/-- `ClosEqTp Δ l l' A vB B` -/
inductive ClosEqTp : Ctx → Nat → Nat → Expr → Clos → Expr → Prop
  | clos_tp {Δ Γ A B Aenv env σ l l'} :
    EnvEqSb Δ env σ Γ →
    -- The equality argument builds in conversion.
    Δ ⊢[l] A.subst σ ≡ Aenv →
    (A, l) :: Γ ⊢[l'] B →
    ClosEqTp Δ l l' Aenv (.of_expr env B) (B.subst <| Expr.up σ)
  | clos_val_tp {Δ Γ A B Aenv vB env σ l l'} :
    EnvEqSb Δ env σ Γ →
    Δ ⊢[l] A.subst σ ≡ Aenv →
    ValEqTp ((A, l) :: Γ) l' vB B →
    ClosEqTp Δ l l' Aenv (.of_val env vB) (B.subst <| Expr.up σ)

/-- `ClosEqTm Δ l l' A B vb b` -/
inductive ClosEqTm : Ctx → Nat → Nat → Expr → Expr → Clos → Expr → Prop
  | clos_tm {Δ Γ A B Aenv Benv b env σ l l'} :
    EnvEqSb Δ env σ Γ →
    Δ ⊢[l] A.subst σ ≡ Aenv →
    (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up σ) ≡ Benv →
    (A, l) :: Γ ⊢[l'] b : B →
    ClosEqTm Δ l l' Aenv Benv (.of_expr env b) (b.subst <| Expr.up σ)
  | clos_val_tm {Δ Γ A B Aenv Benv b vb env σ l l'} :
    EnvEqSb Δ env σ Γ →
    Δ ⊢[l] A.subst σ ≡ Aenv →
    (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up σ) ≡ Benv →
    ValEqTm ((A, l) :: Γ) l' vb b B →
    ClosEqTm Δ l l' Aenv Benv (.of_val env vb) (b.subst <| Expr.up σ)

inductive EnvEqSb : Ctx → List Val → (Nat → Expr) → Ctx → Prop
  /- Possible optimization: allow `EnvEqSb Γ [] Expr.bvar Γ`
  and replace `envOfLen ‖Γ‖` by `[]`. -/
  | nil {Γ} (σ) : WfCtx Γ → EnvEqSb Γ [] σ []
  | snoc {Δ Γ A vt t E σ l} :
    EnvEqSb Δ E σ Γ →
    Γ ⊢[l] A →
    ValEqTm Δ l vt t (A.subst σ) →
    EnvEqSb Δ (vt :: E) (Expr.snoc σ t) ((A, l) :: Γ)
end

/-! ## Well-formed evaluation environments -/

namespace EnvEqSb

theorem wf_dom : ∀ {Δ E σ Γ}, EnvEqSb Δ E σ Γ → WfCtx Δ := by
  mutual_induction EnvEqSb
  all_goals grind

theorem wf_cod : ∀ {Δ E σ Γ}, EnvEqSb Δ E σ Γ → WfCtx Γ := by
  mutual_induction EnvEqSb
  all_goals grind [WfCtx.nil, WfCtx.snoc]

theorem eq_length : ∀ {Δ E σ Γ}, EnvEqSb Δ E σ Γ → E.length = Γ.length := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  all_goals simp; try grind

theorem lookup_lt {Δ Γ E σ i A l} : EnvEqSb Δ E σ Γ → Lookup Γ i A l → i < E.length :=
  fun env lk => env.eq_length ▸ lk.lt_length

theorem lookup_eq : ∀ {Δ E σ Γ}, (env : EnvEqSb Δ E σ Γ) →
    ∀ {A i l}, (lk : Lookup Γ i A l) →
    ValEqTm Δ l (E[i]'(env.lookup_lt lk)) (σ i) (A.subst σ) := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  case nil lk => cases lk
  case snoc E A v ih _ _ _ _ lk =>
    rcases lk with _ | ⟨_, _, lk⟩
    . convert v using 1; autosubst
    . convert ih lk using 1; autosubst

lemma Expr.eq_snoc_get_zero (σ : Nat → Expr) : σ = Expr.snoc (Expr.comp σ Expr.wk) (σ 0) := by
  ext i; cases i <;> rfl

theorem mk : ∀ {Γ}, WfCtx Γ → ∀ {Δ} {E : List Val} {σ}, WfCtx Δ → (eq : Γ.length = E.length) →
    (∀ {i A l}, (lk : Lookup Γ i A l) →
      ValEqTm Δ l (E[i]'(eq ▸ lk.lt_length)) (σ i) (A.subst σ)) →
    EnvEqSb Δ E σ Γ := by
  mutual_induction WfCtx
  all_goals intros; try exact True.intro
  case nil eq _ =>
    have := List.length_eq_zero_iff.mp eq.symm
    grind [EnvEqSb.nil]
  case snoc ih _ _ E σ Δ eq h =>
    cases E
    . cases eq
    . replace eq := Nat.succ_inj.mp eq
      rw [Expr.eq_snoc_get_zero σ]
      apply EnvEqSb.snoc
      . refine ih Δ eq fun lk => ?_
        convert h (lk.succ ..) using 1; autosubst
      . assumption
      . convert h (Lookup.zero ..) using 1; autosubst

end EnvEqSb

/-! ## Values are well-typed as expressions -/

theorem wf_expr :
    (∀ {Γ l vA A}, ValEqTp Γ l vA A → Γ ⊢[l] A) ∧
    (∀ {Γ l vt t A}, ValEqTm Γ l vt t A → Γ ⊢[l] t : A) ∧
    (∀ {Γ l vt t A}, NeutEqTm Γ l vt t A → Γ ⊢[l] t : A) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp Γ l l' A vB B → (A, l) :: Γ ⊢[l'] B) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm Γ l l' A B vb b → (A, l) :: Γ ⊢[l'] b : B) ∧
    (∀ {Γ E σ Γ'}, EnvEqSb Γ E σ Γ' → WfSb Γ σ Γ') := by
  mutual_induction ValEqTp
  all_goals dsimp; intros
  case pi => grind [WfTp.pi]
  case sigma => grind [WfTp.sigma]
  case univ => grind [WfTp.univ]
  case el => grind [WfTp.el]
  case conv_tp => grind [EqTp.wf_right]
  case lam => grind [WfTm.lam]
  case pair => grind [WfTm.pair]
  case code => grind [WfTm.code]
  case neut_tm => grind
  case conv_nf tt' AA' _ => exact tt'.wf_right.conv AA'
  case bvar Γ lk => exact WfTm.bvar Γ lk
  case app => grind [WfTm.app]
  case fst => grind [WfTm.fst]
  case snd => grind [WfTm.snd]
  case conv_neut nn' AA' _ => exact nn'.wf_right.conv AA'
  case clos_tp Aenv B σ =>
    have := B.subst (σ.up B.wf_binder)
    exact this.conv_binder Aenv
  case clos_val_tp Aenv _ σ B =>
    have := B.subst (σ.up B.wf_binder)
    exact this.conv_binder Aenv
  case clos_tm Aenv Benv b σ =>
    have := b.subst (σ.up b.wf_binder)
    have := this.conv_ctx (EqCtx.refl Aenv.wf_ctx |>.snoc Aenv)
    exact this.conv Benv
  case clos_val_tm Aenv Benv _ σ b =>
    have := b.subst (σ.up b.wf_binder)
    have := this.conv_ctx (EqCtx.refl Aenv.wf_ctx |>.snoc Aenv)
    exact this.conv Benv
  case nil => apply WfSb.terminal; assumption
  case snoc => grind [WfSb.snoc]

theorem ValEqTp.wf_tp {Γ l vA A} (h : ValEqTp Γ l vA A) : Γ ⊢[l] A :=
  _root_.wf_expr.1 h

theorem ValEqTm.wf_tm {Γ l vt t A} (h : ValEqTm Γ l vt t A) : Γ ⊢[l] t : A :=
  _root_.wf_expr.2.1 h

theorem NeutEqTm.wf_tm {Γ l vt t A} (h : NeutEqTm Γ l vt t A) : Γ ⊢[l] t : A :=
  _root_.wf_expr.2.2.1 h

theorem ClosEqTp.wf_tp {Γ l l' A vB B} (h : ClosEqTp Γ l l' A vB B) :
    (A, l) :: Γ ⊢[l'] B :=
  _root_.wf_expr.2.2.2.1 h

theorem ClosEqTm.wf_tm {Γ l l' A B vb b} (h : ClosEqTm Γ l l' A B vb b) :
    (A, l) :: Γ ⊢[l'] b : B :=
  _root_.wf_expr.2.2.2.2.1 h

theorem EnvEqSb.wf_sb {Δ E σ Γ} (h : EnvEqSb Δ E σ Γ) : WfSb Δ σ Γ :=
  _root_.wf_expr.2.2.2.2.2 h

theorem ValEqTm.conv_tm {Γ A vt t t' l} :
    ValEqTm Γ l vt t A → Γ ⊢[l] t ≡ t' : A → ValEqTm Γ l vt t' A :=
  fun h eq => h.conv_nf eq (EqTp.refl_tp eq.wf_tp)

theorem ValEqTm.conv_tp {Γ A A' vt t l} :
    ValEqTm Γ l vt t A → Γ ⊢[l] A ≡ A' → ValEqTm Γ l vt t A' :=
  fun h eq => h.conv_nf (EqTm.refl_tm h.wf_tm) eq

theorem NeutEqTm.conv_tm {Γ A vt t t' l} :
    NeutEqTm Γ l vt t A → Γ ⊢[l] t ≡ t' : A → NeutEqTm Γ l vt t' A :=
  fun h eq => h.conv_neut eq (EqTp.refl_tp eq.wf_tp)

theorem NeutEqTm.conv_tp {Γ A A' vt t l} :
    NeutEqTm Γ l vt t A → Γ ⊢[l] A ≡ A' → NeutEqTm Γ l vt t A' :=
  fun h eq => h.conv_neut (EqTm.refl_tm h.wf_tm) eq

/-! ## Values are closed under context conversion -/

attribute [local grind] EqCtx.length_eq in
theorem conv_ctx :
    (∀ {Γ l vA A}, ValEqTp Γ l vA A → ∀ {Γ'}, EqCtx Γ Γ' → ValEqTp Γ' l vA A) ∧
    (∀ {Γ l vt t A}, ValEqTm Γ l vt t A → ∀ {Γ'}, EqCtx Γ Γ' → ValEqTm Γ' l vt t A) ∧
    (∀ {Γ l vt t A}, NeutEqTm Γ l vt t A → ∀ {Γ'}, EqCtx Γ Γ' → NeutEqTm Γ' l vt t A) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp Γ l l' A vB B → ∀ {Γ'}, EqCtx Γ Γ' → ClosEqTp Γ' l l' A vB B) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm Γ l l' A B vb b → ∀ {Γ'}, EqCtx Γ Γ' →
      ClosEqTm Γ' l l' A B vb b) ∧
    (∀ {Γ E σ Δ}, EnvEqSb Γ E σ Δ → ∀ {Γ'}, EqCtx Γ Γ' → EnvEqSb Γ' E σ Δ) := by
  mutual_induction ValEqTp
  all_goals intros
  case pi => grind [ValEqTp.pi]
  case sigma => grind [ValEqTp.sigma]
  case univ => grind [ValEqTp.univ, EqCtx.wf_right]
  case el => grind [ValEqTp.el]
  case conv_tp => grind [ValEqTp.conv_tp, EqTp.conv_ctx]
  case lam eq => grind [ValEqTm.lam]
  case pair B _ _ _ _ _ eq =>
    apply ValEqTm.pair (B.conv_ctx (eq.snoc <| EqTp.refl_tp B.wf_binder)) <;>
      grind
  case code => grind [ValEqTm.code]
  case neut_tm => grind [ValEqTm.neut_tm]
  case conv_nf => grind [EqTm.conv_ctx, EqTp.conv_ctx, ValEqTm.conv_nf]
  case bvar lk _ eq =>
    have ⟨A', _, lk'⟩ := Lookup.of_lt_length <| eq.length_eq ▸ lk.lt_length
    obtain ⟨rfl, eqA⟩ := eq.lookup_eq lk lk'
    have := NeutEqTm.bvar eq.wf_right lk'
    rw [eq.length_eq]
    exact NeutEqTm.conv_neut this (EqTm.refl_tm this.wf_tm) (eqA.symm_tp.conv_ctx eq)
  case app eq => grind [NeutEqTm.app]
  case fst => grind [NeutEqTm.fst]
  case snd => grind [NeutEqTm.snd]
  case conv_neut => grind [EqTm.conv_ctx, EqTp.conv_ctx, NeutEqTm.conv_neut]
  case clos_tp => grind [ClosEqTp.clos_tp, EqTp.conv_ctx]
  case clos_val_tp => grind [ClosEqTp.clos_val_tp, EqTp.conv_ctx]
  case clos_tm Aeq Beq b env _ eq =>
    exact ClosEqTm.clos_tm (env eq) (Aeq.conv_ctx eq)
      (Beq.conv_ctx <| eq.snoc <| EqTp.refl_tp Aeq.wf_right)
      (b.conv_ctx b.wf_ctx.eq_self)
  case clos_val_tm Aeq Beq vb env _ _ eq =>
    exact ClosEqTm.clos_val_tm (env eq) (Aeq.conv_ctx eq)
      (Beq.conv_ctx <| eq.snoc <| EqTp.refl_tp Aeq.wf_right) vb
  case nil eq => exact .nil _ eq.wf_right
  case snoc => grind [EnvEqSb.snoc]

theorem ValEqTp.conv_ctx {Γ Γ' l vA A} : ValEqTp Γ l vA A → EqCtx Γ Γ' → ValEqTp Γ' l vA A :=
  fun h eq => _root_.conv_ctx.1 h eq

theorem ValEqTm.conv_ctx {Γ Γ' l vt t A} : ValEqTm Γ l vt t A → EqCtx Γ Γ' →
    ValEqTm Γ' l vt t A :=
  fun h eq => _root_.conv_ctx.2.1 h eq

theorem NeutEqTm.conv_ctx {Γ Γ' l vt t A} : NeutEqTm Γ l vt t A → EqCtx Γ Γ' →
    NeutEqTm Γ' l vt t A :=
  fun h eq => _root_.conv_ctx.2.2.1 h eq

theorem ClosEqTp.conv_ctx {Γ Γ' l l' A vB B} : ClosEqTp Γ l l' A vB B → EqCtx Γ Γ' →
    ClosEqTp Γ' l l' A vB B :=
  fun h eq => _root_.conv_ctx.2.2.2.1 h eq

theorem ClosEqTm.conv_ctx {Γ Γ' l l' A B vb b} :
    ClosEqTm Γ l l' A B vb b → EqCtx Γ Γ' → ClosEqTm Γ' l l' A B vb b :=
  fun h eq => _root_.conv_ctx.2.2.2.2.1 h eq

theorem EnvEqSb.conv_dom {Δ Δ' E σ Γ} : EnvEqSb Δ E σ Γ → EqCtx Δ Δ' → EnvEqSb Δ' E σ Γ :=
  fun h eq => _root_.conv_ctx.2.2.2.2.2 h eq

/-! ## Weakening is free -/

theorem wk_all :
    (∀ {Γ l vA A}, ValEqTp Γ l vA A → ∀ {C k}, Γ ⊢[k] C →
      ValEqTp ((C,k) :: Γ) l vA (A.subst Expr.wk)) ∧
    (∀ {Γ l vt t A}, ValEqTm Γ l vt t A → ∀ {C k}, Γ ⊢[k] C →
      ValEqTm ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {Γ l vt t A}, NeutEqTm Γ l vt t A → ∀ {C k}, Γ ⊢[k] C →
      NeutEqTm ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp Γ l l' A vB B → ∀ {C k}, Γ ⊢[k] C →
      ClosEqTp ((C,k) :: Γ) l l' (A.subst Expr.wk) vB (B.subst (Expr.up Expr.wk))) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm Γ l l' A B vb b → ∀ {C k}, Γ ⊢[k] C →
      ClosEqTm ((C,k) :: Γ) l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk))
        vb (b.subst (Expr.up Expr.wk))) ∧
    (∀ {Γ E σ Δ}, EnvEqSb Γ E σ Δ → ∀ {C k}, Γ ⊢[k] C →
      EnvEqSb ((C,k) :: Γ) E (Expr.comp Expr.wk σ) Δ) := by
  mutual_induction ValEqTp
  all_goals intros; try dsimp [Expr.subst] at *
  case pi => grind [ValEqTp.pi]
  case sigma => grind [ValEqTp.sigma]
  case univ => grind [ValEqTp.univ, WfCtx.snoc]
  case el => grind [ValEqTp.el]
  case conv_tp => grind [ValEqTp.conv_tp, EqTp.subst, WfSb.wk]
  case lam => grind [ValEqTm.lam]
  case pair B _ _ iht ihu _ _ C =>
    have := B.subst (WfSb.wk C |>.up B.wf_binder)
    apply ValEqTm.pair this (iht C) (by convert ihu C using 1; autosubst)
  case code => grind [ValEqTm.code]
  case neut_tm => grind [ValEqTm.neut_tm]
  case conv_nf => grind [ValEqTm.conv_nf, EqTp.subst, EqTm.subst, WfSb.wk]
  case bvar Γ lk _ _ C =>
    convert NeutEqTm.bvar (Γ.snoc C) (.succ _ _ lk) using 1; grind
  case app ihA ihf iha _ _ C =>
    convert NeutEqTm.app (ihA C) (ihf C) (iha C) using 1; autosubst
  case fst => grind [NeutEqTm.fst]
  case snd ih _ _ C =>
    convert NeutEqTm.snd (ih C) using 1; autosubst
  case conv_neut => grind [NeutEqTm.conv_neut, EqTp.subst, EqTm.subst, WfSb.wk]
  case clos_tp Aeq B ih _ _ C =>
    have := Aeq.subst (WfSb.wk C)
    convert ClosEqTp.clos_tp (ih C) (by convert this using 1; autosubst) B using 1
    autosubst
  case clos_val_tp Aeq vB ihE _ _ _ C =>
    convert ClosEqTp.clos_val_tp (ihE C)
      (by convert Aeq.subst (WfSb.wk C) using 1; autosubst) vB using 1
    autosubst
  case clos_tm Aeq Beq b ihE _ _ C =>
    have CAeq := Aeq.subst <| WfSb.wk C
    have CBeq := Beq.subst <| (WfSb.wk C).up Aeq.wf_right
    have := ClosEqTm.clos_tm (ihE C)
      (by convert CAeq using 1; autosubst)
      (by convert CBeq using 1; autosubst)
      b
    convert this using 1; autosubst
  case clos_val_tm Aeq Beq vb ihE _ _ _ C =>
    have CAeq := Aeq.subst <| WfSb.wk C
    have CBeq := Beq.subst <| (WfSb.wk C).up Aeq.wf_right
    have := ClosEqTm.clos_val_tm (ihE C)
      (by convert CAeq using 1; autosubst)
      (by convert CBeq using 1; autosubst)
      vb
    convert this using 1; autosubst
  case nil C => apply EnvEqSb.nil _ (C.wf_ctx.snoc C)
  case snoc =>
    simp only [autosubst] at *
    grind [EnvEqSb.snoc]

theorem ValEqTp.wk {Γ l vA A} (h : ValEqTp Γ l vA A) {C k} (hC : Γ ⊢[k] C) :
    ValEqTp ((C,k) :: Γ) l vA (A.subst Expr.wk) :=
  wk_all.1 h hC

theorem ValEqTm.wk {Γ l vt t A} (h : ValEqTm Γ l vt t A) {C k} (hC : Γ ⊢[k] C) :
    ValEqTm ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk) :=
  wk_all.2.1 h hC

theorem NeutEqTm.wk {Γ l vn n A} (h : NeutEqTm Γ l vn n A) {C k} (hC : Γ ⊢[k] C) :
    NeutEqTm ((C,k) :: Γ) l vn (n.subst Expr.wk) (A.subst Expr.wk) :=
  wk_all.2.2.1 h hC

theorem ClosEqTp.wk {Γ l l' A vB B} (h : ClosEqTp Γ l l' A vB B) {C k} (hC : Γ ⊢[k] C) :
    ClosEqTp ((C,k) :: Γ) l l' (A.subst Expr.wk) vB (B.subst (Expr.up Expr.wk)) :=
  wk_all.2.2.2.1 h hC

theorem ClosEqTm.wk {Γ l l' A B vb b} (h : ClosEqTm Γ l l' A B vb b) {C k} (hC : Γ ⊢[k] C) :
    ClosEqTm ((C,k) :: Γ) l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk))
      vb (b.subst (Expr.up Expr.wk)) :=
  wk_all.2.2.2.2.1 h hC

theorem EnvEqSb.wk {Δ E σ Γ} (h : EnvEqSb Δ E σ Γ) {C k} (hC : Δ ⊢[k] C) :
    EnvEqSb ((C,k) :: Δ) E (Expr.comp Expr.wk σ) Γ :=
  wk_all.2.2.2.2.2 h hC

/-! ## Type environments -/

/-- A type environment is a context where all types are in NF. -/
abbrev TpEnv := List (Val × Nat)

inductive TpEnvEqCtx : TpEnv → Ctx → Prop
  | nil : TpEnvEqCtx [] []
  | snoc {vΓ Γ l vA A} :
    TpEnvEqCtx vΓ Γ →
    ValEqTp Γ l vA A →
    TpEnvEqCtx ((vA, l) :: vΓ) ((A, l) :: Γ)

theorem TpEnvEqCtx.wf_ctx {vΓ Γ} : TpEnvEqCtx vΓ Γ → WfCtx Γ := by
  intro vΓ; induction vΓ <;> grind [WfCtx.nil, WfCtx.snoc, ValEqTp.wf_tp]

theorem TpEnvEqCtx.length_eq {vΓ Γ} : TpEnvEqCtx vΓ Γ → vΓ.length = Γ.length := by
  intro vΓ; induction vΓ <;> simp [*]

theorem TpEnvEqCtx.lt_length {vΓ Γ i A l} : TpEnvEqCtx vΓ Γ → Lookup Γ i A l → i < vΓ.length :=
  fun vΓ lk => vΓ.length_eq ▸ lk.lt_length

theorem TpEnvEqCtx.lvl_eq {vΓ Γ i A l} : (h : TpEnvEqCtx vΓ Γ) → (lk : Lookup Γ i A l) →
    (vΓ[i]'(h.lt_length lk)).2 = l := by
  intro h lk
  induction h generalizing i A <;> cases lk <;> grind

theorem TpEnvEqCtx.lookup_wf {vΓ Γ i A l} : (h : TpEnvEqCtx vΓ Γ) → (lk : Lookup Γ i A l) →
    ValEqTp Γ l (vΓ[i]'(h.lt_length lk)).1 A := by
  intro h lk
  induction h generalizing i A <;> cases lk
  case zero vA => exact vA.wk vA.wf_tp
  case snoc vA ih _ _ lk => exact (ih lk).wk vA.wf_tp

/-! ## Type environments from contexts -/

/-- An identity evaluation environment (i.e., bvars remain themselves)
for the given type environment. -/
def envOfTpEnv (vΓ : TpEnv) : List Val :=
  vΓ.mapIdx fun i (vA, _) => .neut (.bvar <| vΓ.length - i - 1) vA

@[simp]
theorem length_envOfTpEnv (vΓ : TpEnv) : (envOfTpEnv vΓ).length = vΓ.length := by
  simp [envOfTpEnv]

@[simp]
theorem envOfTpEnv_cons (vA : Val) (l : Nat) (vΓ : TpEnv) :
  envOfTpEnv ((vA, l) :: vΓ) = .neut (.bvar vΓ.length) vA :: envOfTpEnv vΓ := by
  simp [envOfTpEnv, List.mapIdx_cons]

theorem envOfTpEnv_wf {vΓ Γ} : TpEnvEqCtx vΓ Γ → EnvEqSb Γ (envOfTpEnv vΓ) Expr.bvar Γ := by
  intro vΓ
  have Γ := vΓ.wf_ctx
  refine EnvEqSb.mk Γ Γ ?_ fun lk => ?_
  . rw [length_envOfTpEnv, vΓ.length_eq]
  . simp only [envOfTpEnv, List.getElem_mapIdx]
    apply ValEqTm.neut_tm
    . convert vΓ.lookup_wf lk using 1; autosubst
    . rw [vΓ.length_eq]
      apply NeutEqTm.bvar Γ
      convert lk using 1; autosubst

/-! ## Inversion for value relations -/

theorem ValEqTp.inv_pi {Γ C vA vB l k k'} : ValEqTp Γ l (.pi k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
      (Γ ⊢[max k k'] C ≡ .pi k k' A B) := by
  suffices ∀ {Γ l vC C}, ValEqTp Γ l vC C →
      ∀ {vA vB k k'}, vC = .pi k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
        (Γ ⊢[max k k'] C ≡ .pi k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.pi, ClosEqTp.wf_tp]

theorem ValEqTp.inv_sigma {Γ C vA vB l k k'} : ValEqTp Γ l (.sigma k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
      (Γ ⊢[max k k'] C ≡ .sigma k k' A B) := by
  suffices ∀ {Γ l vC C}, ValEqTp Γ l vC C →
      ∀ {vA vB k k'}, vC = .sigma k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
        (Γ ⊢[max k k'] C ≡ .sigma k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.sigma, ClosEqTp.wf_tp]

theorem ValEqTp.inv_univ {Γ l k t} : ValEqTp Γ l (.univ k) t → l = k + 1 ∧
    (Γ ⊢[k + 1] t ≡ .univ k) := by
  suffices ∀ {Γ l vt t}, ValEqTp Γ l vt t → ∀ {k}, vt = .univ k → l = k + 1 ∧
      (Γ ⊢[k + 1] t ≡ .univ k) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.univ]

theorem ValEqTp.inv_el {Γ l na A} : ValEqTp Γ l (.el na) A →
    ∃ a, NeutEqTm Γ (l + 1) na a (.univ l) ∧
      (Γ ⊢[l] A ≡ .el a) := by
  suffices ∀ {Γ l vA A}, ValEqTp Γ l vA A → ∀ {na}, vA = .el na →
      ∃ a, NeutEqTm Γ (l + 1) na a (.univ l) ∧
        (Γ ⊢[l] A ≡ .el a) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.el, NeutEqTm.wf_tm]

theorem ValEqTm.inv_lam {Γ C vA vb t l₀ l l'} : ValEqTm Γ l₀ (.lam l l' vA vb) t C →
    l₀ = max l l' ∧ ∃ A B b,
      (ValEqTp Γ l vA A) ∧
      (ClosEqTm Γ l l' A B vb b) ∧
      (Γ ⊢[max l l'] t ≡ .lam l l' A b : C) ∧
      (Γ ⊢[max l l'] C ≡ .pi l l' A B) := by
  suffices
      ∀ {Γ l₀ vt t C}, ValEqTm Γ l₀ vt t C → ∀ {l l' vA vb}, vt = .lam l l' vA vb →
        l₀ = max l l' ∧ ∃ A B b, (ValEqTp Γ l vA A) ∧
          (ClosEqTm Γ l l' A B vb b) ∧
          (Γ ⊢[max l l'] t ≡ .lam l l' A b : C) ∧
          (Γ ⊢[max l l'] C ≡ .pi l l' A B) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case lam => grind [WfTm.lam, ClosEqTm.wf_tm, WfTm.wf_tp, WfTp.pi]

theorem ValEqTm.inv_pair {Γ C vt vu p l₀ l l'} : ValEqTm Γ l₀ (.pair l l' vt vu) p C →
    l₀ = max l l' ∧ ∃ A B t u, (ValEqTm Γ l vt t A) ∧ (ValEqTm Γ l' vu u (B.subst t.toSb)) ∧
      (Γ ⊢[max l l'] p ≡ .pair l l' B t u : C) ∧
      (Γ ⊢[max l l'] C ≡ .sigma l l' A B) := by
  suffices
      ∀ {Γ l₀ vp p C}, ValEqTm Γ l₀ vp p C → ∀ {vt vu l l'}, vp = .pair l l' vt vu →
        l₀ = max l l' ∧ ∃ A B t u,
          (ValEqTm Γ l vt t A) ∧
          (ValEqTm Γ l' vu u (B.subst t.toSb)) ∧
          (Γ ⊢[max l l'] p ≡ .pair l l' B t u : C) ∧
          (Γ ⊢[max l l'] C ≡ .sigma l l' A B) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case pair => grind [WfTm.pair, ValEqTm.wf_tm, WfTp.sigma]

theorem ValEqTm.inv_code {Γ C vA c l₀} : ValEqTm Γ l₀ (.code vA) c C →
    ∃ l A, l₀ = l + 1 ∧
      (ValEqTp Γ l vA A) ∧ (Γ ⊢[l₀] c ≡ .code A : C) ∧ (Γ ⊢[l₀] C ≡ .univ l) := by
  suffices
      ∀ {Γ l₀ vc c C}, ValEqTm Γ l₀ vc c C → ∀ {vA}, vc = .code vA →
        ∃ l A, l₀ = l + 1 ∧
          (ValEqTp Γ l vA A) ∧ (Γ ⊢[l₀] c ≡ .code A : C) ∧ (Γ ⊢[l₀] C ≡ .univ l) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case code => grind [WfTp.univ, WfTm.code, ValEqTp.wf_tp, WfTp.wf_ctx]

theorem ValEqTm.inv_neut {Γ vA A vt t l} : ValEqTm Γ l (.neut vt vA) t A →
    ValEqTp Γ l vA A ∧ NeutEqTm Γ l vt t A := by
  suffices ∀ {Γ l vt t A}, ValEqTm Γ l vt t A → ∀ {n vA}, vt = .neut n vA →
      ValEqTp Γ l vA A ∧ NeutEqTm Γ l n t A from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals grind [NeutEqTm.conv_neut, ValEqTp.conv_tp]

theorem NeutEqTm.inv_bvar {Γ A t i l} : NeutEqTm Γ l (.bvar i) t A →
    ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
      (Γ ⊢[l] t ≡ .bvar (Γ.length - i - 1) : A) ∧ (Γ ⊢[l] A ≡ A') := by
  suffices ∀ {Γ l vn n A}, NeutEqTm Γ l vn n A → ∀ {i}, vn = .bvar i →
      ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
        (Γ ⊢[l] n ≡ .bvar (Γ.length - i - 1) : A) ∧ (Γ ⊢[l] A ≡ A') from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case bvar Γ _ i _ Γwf lk =>
    have := lk.lt_length
    rw [show Γ.length - (Γ.length - i - 1) - 1 = i by omega]
    exact ⟨_, lk, EqTm.refl_tm (WfTm.bvar (by omega) lk), EqTp.refl_tp (Γwf.lookup_wf lk)⟩
  case conv_neut => grind [EqTm.conv_eq]

theorem NeutEqTm.inv_app {Γ vA C vf va t l₀ l l'} : NeutEqTm Γ l₀ (.app l l' vA vf va) t C →
    l₀ = l' ∧ ∃ A B f a,
      ValEqTp Γ l vA A ∧ NeutEqTm Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm Γ l va a A ∧
      (Γ ⊢[l'] t ≡ .app l l' B f a : C) ∧ (Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vA vf va l l'}, vn = .app l l' vA vf va →
      l₀ = l' ∧ ∃ A B f a,
        ValEqTp Γ l vA A ∧ NeutEqTm Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm Γ l va a A ∧
        (Γ ⊢[l'] n ≡ .app l l' B f a : C) ∧ (Γ ⊢[l'] C ≡ B.subst a.toSb) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case app =>
    grind [WfTm.app, ValEqTm.wf_tm, NeutEqTm.wf_tm, WfSb.toSb, WfTp.subst, WfTp.inv_pi, WfTm.wf_tp]

theorem NeutEqTm.inv_fst {Γ C vp f l₀ l l'} : NeutEqTm Γ l₀ (.fst l l' vp) f C →
    l₀ = l ∧ ∃ A B p, NeutEqTm Γ (max l l') vp p (.sigma l l' A B) ∧
      (Γ ⊢[l] f ≡ .fst l l' A B p : C) ∧ (Γ ⊢[l] C ≡ A) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vp l l'}, vn = .fst l l' vp →
      l₀ = l ∧ ∃ A B p, NeutEqTm Γ (max l l') vp p (.sigma l l' A B) ∧
      (Γ ⊢[l] n ≡ .fst l l' A B p : C) ∧ (Γ ⊢[l] C ≡ A) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case fst =>
    grind [WfTm.fst, NeutEqTm.wf_tm, WfTm.wf_tp, WfTp.inv_sigma, WfTp.wf_ctx, WfCtx.inv_snoc]

theorem NeutEqTm.inv_snd {Γ C vp s l₀ l l'} : NeutEqTm Γ l₀ (.snd l l' vp) s C →
    l₀ = l' ∧ ∃ A B p, NeutEqTm Γ (max l l') vp p (.sigma l l' A B) ∧
      (Γ ⊢[l'] s ≡ .snd l l' A B p : C) ∧ (Γ ⊢[l'] C ≡ B.subst (Expr.fst l l' A B p).toSb) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vp l l'}, vn = .snd l l' vp →
      l₀ = l' ∧ ∃ A B p, NeutEqTm Γ (max l l') vp p (.sigma l l' A B) ∧
      (Γ ⊢[l'] n ≡ .snd l l' A B p : C) ∧ (Γ ⊢[l'] C ≡ B.subst (Expr.fst l l' A B p).toSb) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case snd =>
    grind [WfTm.snd, NeutEqTm.wf_tm, WfTm.wf_tp, WfTp.inv_sigma, WfTp.wf_ctx, WfCtx.inv_snoc]
