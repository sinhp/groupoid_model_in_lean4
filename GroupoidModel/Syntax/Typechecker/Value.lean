import GroupoidModel.Syntax.GCongr
import GroupoidModel.Syntax.Injectivity

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
   as sublanguages of expressions
2. replacing the bodies of binders in those languages by unevaluated closures

## Type annotations

Unlike expressions, values contain no type annotations.
This is essential for performance:
- if we were to store type annotations as unevaluated `Expr`s,
  weakening would not be free for values; and
- if we we stored them as `Val`ues, we'd have to evaluate them.

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
  | lam (l l' : Nat) (b : Clos)
  | pair (l l' : Nat) (t u : Val)
  | univ (l : Nat)
  /- TODO: to make the theory usable,
  we'll need to treat `code` and `el` as eliminators,
  adding `el (code A) ≡ A` and `code (el a) ≡ a`.
  For now, we treat them as introductions. -/
  | el (a : Val)
  | code (A : Val)
  /-- A neutral form. -/
  | neut (n : Neut)
  deriving Inhabited

/-- Neutral forms are elimination forms that are 'stuck',
i.e., contain no β-reducible subterm. -/
inductive Neut where
  /-- A de Bruijn *level*. -/
  | bvar (i : Nat)
  | app (l l' : Nat) (f : Neut) (a : Val)
  | fst (l l' : Nat) (p : Neut)
  | snd (l l' : Nat) (p : Neut)
  deriving Inhabited

/-- Recall that given `Γ.A ⊢ b : B` and a substitution `Δ ⊢ env : Γ`,
`Δ.A ⊢ b[(env∘↑).v₀] : B[(env∘↑).v₀]`.
A term closure stores the term `b` together with the substitution `env`.
We may view it as a term which is *almost* well-typed in `Δ`,
except that we are missing one more argument `Δ ⊢ a : A`
to fill in for `v₀` in `b`.

In NbE, closures are the runtime values of binder bodies.

In some NbE implementations, this would be an actual closure `Expr → Expr`;
the present variant is a defunctionalization due to Abel. -/
inductive Clos where
  | mk_tp (Γ : Ctx) (A : Expr) (env : List Val) (B : Expr)
  | mk_tm (Γ : Ctx) (A : Expr) (env : List Val) (b : Expr)
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
  | el {Γ va a l} :
    ValEqTm Γ (l + 1) va a (.univ l) →
    ValEqTp Γ l (.el va) (.el a)
  | conv_tp {Γ vA A A' l} :
    ValEqTp Γ l vA A →
    Γ ⊢[l] A ≡ A' →
    ValEqTp Γ l vA A'

-- Note: no neutral types atm.

inductive ValEqTm : Ctx → Nat → Val → Expr → Expr → Prop
  | lam {Γ A B vb b l l'} :
    ClosEqTm Γ l l' A B vb b →
    ValEqTm Γ (max l l') (.lam l l' vb) (.lam l l' A b) (.pi l l' A B)
  | pair {Γ A B vt t vu u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    ValEqTm Γ l vt t A →
    ValEqTm Γ l' vu u (B.subst t.toSb) →
    ValEqTm Γ (max l l') (.pair l l' vt vu) (.pair l l' B t u) (.sigma l l' A B)
  | code {Γ vA A l} :
    l < univMax →
    ValEqTp Γ l vA A →
    ValEqTm Γ (l + 1) (.code vA) (.code A) (.univ l)
  | neut_tm {Γ A vn n l} :
    NeutEqTm Γ l vn n A →
    ValEqTm Γ l (.neut vn) n A
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
  | app {Γ A B vf f va a l l'} :
    NeutEqTm Γ (max l l') vf f (.pi l l' A B) →
    ValEqTm Γ l va a A →
    NeutEqTm Γ l' (.app l l' vf va) (.app l l' B f a) (B.subst a.toSb)
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
    ClosEqTp Δ l l' Aenv (.mk_tp Γ A env B) (B.subst <| Expr.up σ)

/-- `ClosEqTm Δ l l' A B vb b` -/
inductive ClosEqTm : Ctx → Nat → Nat → Expr → Expr → Clos → Expr → Prop
  | clos_tm {Δ Γ A B Aenv Benv b env σ l l'} :
    EnvEqSb Δ env σ Γ →
    Δ ⊢[l] A.subst σ ≡ Aenv →
    (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up σ) ≡ Benv →
    (A, l) :: Γ ⊢[l'] b : B →
    ClosEqTm Δ l l' Aenv Benv (.mk_tm Γ A env b) (b.subst <| Expr.up σ)

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

theorem wf_dom {Δ} : ∀ {E σ Γ}, EnvEqSb Δ E σ Γ → WfCtx Δ := by
  mutual_induction EnvEqSb
  all_goals grind

theorem wf_cod {Δ} : ∀ {E σ Γ}, EnvEqSb Δ E σ Γ → WfCtx Γ := by
  mutual_induction EnvEqSb
  all_goals grind [WfCtx.nil, WfCtx.snoc]

theorem eq_length {Δ} : ∀ {E σ Γ}, EnvEqSb Δ E σ Γ → E.length = Γ.length := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  all_goals simp; try grind

theorem lookup_lt {Δ Γ E σ i A l} : EnvEqSb Δ E σ Γ → Lookup Γ i A l → i < E.length :=
  fun env lk => env.eq_length ▸ lk.lt_length

theorem lookup_eq {Δ} : ∀ {E σ Γ}, (env : EnvEqSb Δ E σ Γ) →
    ∀ {A i l}, (lk : Lookup Γ i A l) →
    ValEqTm Δ l (E[i]'(env.lookup_lt lk)) (σ i) (A.subst σ) := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  case nil lk => cases lk
  case snoc E A v ih _ _ _ _ lk =>
    rcases lk with _ | ⟨_, _, lk⟩
    . convert v using 1; autosubst
    . convert ih lk using 1; autosubst

lemma Expr.eq_snoc_self (σ : Nat → Expr) : σ = Expr.snoc (Expr.comp σ Expr.wk) (σ 0) := by
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
      rw [Expr.eq_snoc_self σ]
      apply EnvEqSb.snoc
      . refine ih Δ eq fun lk => ?_
        convert h (lk.succ ..) using 1; autosubst
      . assumption
      . convert h (Lookup.zero ..) using 1; autosubst

end EnvEqSb

/-! ## Values are well-typed as expressions -/

theorem wf_expr {Γ} :
    (∀ {l vA A}, ValEqTp Γ l vA A → Γ ⊢[l] A) ∧
    (∀ {l vt t A}, ValEqTm Γ l vt t A → Γ ⊢[l] t : A) ∧
    (∀ {l vt t A}, NeutEqTm Γ l vt t A → Γ ⊢[l] t : A) ∧
    (∀ {l l' A vB B}, ClosEqTp Γ l l' A vB B → (A, l) :: Γ ⊢[l'] B) ∧
    (∀ {l l' A B vb b}, ClosEqTm Γ l l' A B vb b → (A, l) :: Γ ⊢[l'] b : B) ∧
    (∀ {E σ Γ'}, EnvEqSb Γ E σ Γ' → WfSb Γ σ Γ') := by
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
  case clos_tm Aenv Benv b σ =>
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

theorem ValEqTm.conv_tp {Γ A A' vt t l} :
    ValEqTm Γ l vt t A → Γ ⊢[l] A ≡ A' → ValEqTm Γ l vt t A' :=
  fun h eq => h.conv_nf (EqTm.refl_tm h.wf_tm) eq

theorem NeutEqTm.conv_tp {Γ A A' vt t l} :
    NeutEqTm Γ l vt t A → Γ ⊢[l] A ≡ A' → NeutEqTm Γ l vt t A' :=
  fun h eq => h.conv_neut (EqTm.refl_tm h.wf_tm) eq

/-! ## Values are closed under context conversion -/

attribute [local grind] EqCtx.length_eq in
theorem conv_ctx {Γ} :
    (∀ {l vA A}, ValEqTp Γ l vA A → ∀ {Γ'}, EqCtx Γ Γ' → ValEqTp Γ' l vA A) ∧
    (∀ {l vt t A}, ValEqTm Γ l vt t A → ∀ {Γ'}, EqCtx Γ Γ' → ValEqTm Γ' l vt t A) ∧
    (∀ {l vt t A}, NeutEqTm Γ l vt t A → ∀ {Γ'}, EqCtx Γ Γ' → NeutEqTm Γ' l vt t A) ∧
    (∀ {l l' A vB B}, ClosEqTp Γ l l' A vB B → ∀ {Γ'}, EqCtx Γ Γ' → ClosEqTp Γ' l l' A vB B) ∧
    (∀ {l l' A B vb b}, ClosEqTm Γ l l' A B vb b → ∀ {Γ'}, EqCtx Γ Γ' →
      ClosEqTm Γ' l l' A B vb b) ∧
    (∀ {E σ Δ}, EnvEqSb Γ E σ Δ → ∀ {Γ'}, EqCtx Γ Γ' → EnvEqSb Γ' E σ Δ) := by
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
    exact NeutEqTm.conv_neut this (EqTm.refl_tm (wf_expr.2.2.1 this)) (eqA.symm_tp.conv_ctx eq)
  case app eq => grind [NeutEqTm.app]
  case fst => grind [NeutEqTm.fst]
  case snd => grind [NeutEqTm.snd]
  case conv_neut => grind [EqTm.conv_ctx, EqTp.conv_ctx, NeutEqTm.conv_neut]
  case clos_tp => grind [ClosEqTp.clos_tp, EqTp.conv_ctx]
  case clos_tm Aeq Beq b env _ eq =>
    exact ClosEqTm.clos_tm (env eq) (Aeq.conv_ctx eq)
      (Beq.conv_ctx <| eq.snoc <| EqTp.refl_tp Aeq.wf_right)
      (b.conv_ctx b.wf_ctx.eq_self)
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

/-! ## Environments from contexts -/

/-- An identity evaluation environment (i.e., bvars remain themselves)
for contexts of the given length. -/
def envOfLen (n : Nat) : List Val :=
  /- Recall: we use de Bruijn levels in `Val`,
  so `‖Γ‖ - 1` is the innermost binder. -/
  List.ofFn (n := n) (.neut <| .bvar <| n - · - 1)

@[simp]
theorem length_envOfLen (n : Nat) : (envOfLen n).length = n := by
  simp [envOfLen]

@[simp]
theorem envOfLen_succ (n : Nat) : envOfLen (n + 1) = (.neut <| .bvar n) :: envOfLen n := by
  rw [envOfLen, List.ofFn_succ]
  congr 2
  ext i
  congr 2
  dsimp
  omega

theorem envOfLen_wf {Γ} : WfCtx Γ → EnvEqSb Γ (envOfLen Γ.length) Expr.bvar Γ := by
  intro Γ
  refine EnvEqSb.mk Γ Γ (length_envOfLen _).symm fun lk => ?_
  simp only [envOfLen, List.getElem_ofFn]
  apply ValEqTm.neut_tm
  apply NeutEqTm.bvar Γ
  convert lk using 1; autosubst

/-! ## Weakening is free -/

theorem wk_all {Γ} :
    (∀ {l vA A}, ValEqTp Γ l vA A → ∀ {C k}, Γ ⊢[k] C →
      ValEqTp ((C,k) :: Γ) l vA (A.subst Expr.wk)) ∧
    (∀ {l vt t A}, ValEqTm Γ l vt t A → ∀ {C k}, Γ ⊢[k] C →
      ValEqTm ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {l vt t A}, NeutEqTm Γ l vt t A → ∀ {C k}, Γ ⊢[k] C →
      NeutEqTm ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {l l' A vB B}, ClosEqTp Γ l l' A vB B → ∀ {C k}, Γ ⊢[k] C →
      ClosEqTp ((C,k) :: Γ) l l' (A.subst Expr.wk) vB (B.subst (Expr.up Expr.wk))) ∧
    (∀ {l l' A B vb b}, ClosEqTm Γ l l' A B vb b → ∀ {C k}, Γ ⊢[k] C →
      ClosEqTm ((C,k) :: Γ) l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk))
        vb (b.subst (Expr.up Expr.wk))) ∧
    (∀ {E σ Δ}, EnvEqSb Γ E σ Δ → ∀ {C k}, Γ ⊢[k] C →
      EnvEqSb ((C,k) :: Γ) E (Expr.comp Expr.wk σ) Δ) := by
  mutual_induction ValEqTp
  all_goals intros; try dsimp [Expr.subst] at *
  case pi => grind [ValEqTp.pi]
  case sigma => grind [ValEqTp.sigma]
  case univ => grind [ValEqTp.univ, WfCtx.snoc]
  case el => grind [ValEqTp.el]
  case conv_tp => grind [ValEqTp.conv_tp, EqTp.subst, WfSb.wk]
  case lam eq => grind [ValEqTm.lam]
  case pair B _ _ iht ihu _ _ C =>
    have := B.subst (WfSb.wk C |>.up B.wf_binder)
    apply ValEqTm.pair this (iht C) (by convert ihu C using 1; autosubst)
  case code => grind [ValEqTm.code]
  case neut_tm => grind [ValEqTm.neut_tm]
  case conv_nf => grind [ValEqTm.conv_nf, EqTp.subst, EqTm.subst, WfSb.wk]
  case bvar Γ lk _ _ C =>
    convert NeutEqTm.bvar (Γ.snoc C) (.succ _ _ lk) using 1; grind
  case app ihf iha _ _ C =>
    convert NeutEqTm.app (ihf C) (iha C) using 1; autosubst
  case fst => grind [NeutEqTm.fst]
  case snd ih _ _ C =>
    convert NeutEqTm.snd (ih C) using 1; autosubst
  case conv_neut => grind [NeutEqTm.conv_neut, EqTp.subst, EqTm.subst, WfSb.wk]
  case clos_tp Aeq B ih _ _ C =>
    have := Aeq.subst (WfSb.wk C)
    convert ClosEqTp.clos_tp (ih C) (by convert this using 1; autosubst) B using 1
    autosubst
  case clos_tm Aeq Beq b ih _ _ C =>
    have CAeq := Aeq.subst <| WfSb.wk C
    have CBeq := Beq.subst <| (WfSb.wk C).up Aeq.wf_right
    have := ClosEqTm.clos_tm (ih C)
      (by convert CAeq using 1; autosubst)
      (by convert CBeq using 1; autosubst)
      b
    convert this using 1; autosubst
  case nil C => apply EnvEqSb.nil _ (C.wf_ctx.snoc C)
  case snoc =>
    simp only [autosubst] at *
    grind [EnvEqSb.snoc]

/-! ## Inversion for value relations -/

theorem ValEqTp.inv_pi {Γ C vA vB l k k'} : ValEqTp Γ l (.pi k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
      (Γ ⊢[max k k'] C ≡ .pi k k' A B) := by
  suffices ∀ {l vC C}, ValEqTp Γ l vC C →
      ∀ {vA vB k k'}, vC = .pi k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
        (Γ ⊢[max k k'] C ≡ .pi k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.pi, ClosEqTp.wf_tp]

theorem ValEqTp.inv_sigma {Γ C vA vB l k k'} : ValEqTp Γ l (.sigma k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
      (Γ ⊢[max k k'] C ≡ .sigma k k' A B) := by
  suffices ∀ {l vC C}, ValEqTp Γ l vC C →
      ∀ {vA vB k k'}, vC = .sigma k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp Γ k vA A ∧ ClosEqTp Γ k k' A vB B ∧
        (Γ ⊢[max k k'] C ≡ .sigma k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.sigma, ClosEqTp.wf_tp]

theorem ValEqTp.inv_univ {Γ l k t} : ValEqTp Γ l (.univ k) t → l = k + 1 ∧
    (Γ ⊢[k + 1] t ≡ .univ k) := by
  suffices ∀ {l vt t}, ValEqTp Γ l vt t → ∀ {k}, vt = .univ k → l = k + 1 ∧
      (Γ ⊢[k + 1] t ≡ .univ k) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.univ]

theorem ValEqTp.inv_el {Γ l va A} : ValEqTp Γ l (.el va) A →
    ∃ a, ValEqTm Γ (l + 1) va a (.univ l) ∧ (Γ ⊢[l] A ≡ .el a) := by
  suffices ∀ {l vA A}, ValEqTp Γ l vA A → ∀ {va}, vA = .el va →
      ∃ a, ValEqTm Γ (l + 1) va a (.univ l) ∧ (Γ ⊢[l] A ≡ .el a) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.el, ValEqTm.wf_tm]

theorem ValEqTm.inv_lam {Γ C vb t l₀ l l'} : ValEqTm Γ l₀ (.lam l l' vb) t C →
    l₀ = max l l' ∧ ∃ A B b, (ClosEqTm Γ l l' A B vb b) ∧
      (Γ ⊢[max l l'] t ≡ .lam l l' A b : C) ∧
      (Γ ⊢[max l l'] C ≡ .pi l l' A B) := by
  suffices
      ∀ {l₀ vt t C}, ValEqTm Γ l₀ vt t C → ∀ {l l'}, vt = .lam l l' vb →
        l₀ = max l l' ∧ ∃ A B b, (ClosEqTm Γ l l' A B vb b) ∧
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
      ∀ {l₀ vp p C}, ValEqTm Γ l₀ vp p C → ∀ {vt vu l l'}, vp = .pair l l' vt vu →
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
    ∃ l A, l₀ = l + 1 ∧ (ValEqTp Γ l vA A) ∧ (Γ ⊢[l₀] c ≡ .code A : C) ∧ (Γ ⊢[l₀] C ≡ .univ l) := by
  suffices
      ∀ {l₀ vc c C}, ValEqTm Γ l₀ vc c C → ∀ {vA}, vc = .code vA →
        ∃ l A, l₀ = l + 1 ∧ (ValEqTp Γ l vA A) ∧ (Γ ⊢[l₀] c ≡ .code A : C) ∧ (Γ ⊢[l₀] C ≡ .univ l) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case code => grind [WfTp.univ, WfTm.code, ValEqTp.wf_tp, WfTp.wf_ctx]

theorem ValEqTm.inv_neut {Γ A vt t l} : ValEqTm Γ l (.neut vt) t A → NeutEqTm Γ l vt t A := by
  suffices ∀ {l vt t A}, ValEqTm Γ l vt t A → ∀ {n}, vt = .neut n → (NeutEqTm Γ l n t A) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals grind [NeutEqTm.conv_neut]

theorem NeutEqTm.inv_bvar {Γ A t i l} : NeutEqTm Γ l (.bvar i) t A →
    ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
      (Γ ⊢[l] t ≡ .bvar (Γ.length - i - 1) : A) ∧ (Γ ⊢[l] A ≡ A') := by
  suffices ∀ {l vn n A}, NeutEqTm Γ l vn n A → ∀ {i}, vn = .bvar i →
      ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
        (Γ ⊢[l] n ≡ .bvar (Γ.length - i - 1) : A) ∧ (Γ ⊢[l] A ≡ A') from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case bvar i _ Γwf lk =>
    have := lk.lt_length
    rw [show Γ.length - (Γ.length - i - 1) - 1 = i by omega]
    exact ⟨_, lk, EqTm.refl_tm (WfTm.bvar (by omega) lk), EqTp.refl_tp (Γwf.lookup_wf lk)⟩
  case conv_neut => grind [EqTm.conv_eq]

theorem NeutEqTm.inv_app {Γ C vf va t l₀ l l'} : NeutEqTm Γ l₀ (.app l l' vf va) t C →
    l₀ = l' ∧ ∃ A B f a, NeutEqTm Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm Γ l va a A ∧
      (Γ ⊢[l'] t ≡ .app l l' B f a : C) ∧ (Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices ∀ {l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vf va l l'}, vn = .app l l' vf va →
      l₀ = l' ∧ ∃ A B f a, NeutEqTm Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm Γ l va a A ∧
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
  suffices ∀ {l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vp l l'}, vn = .fst l l' vp →
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
  suffices ∀ {l₀ vn n C}, NeutEqTm Γ l₀ vn n C → ∀ {vp l l'}, vn = .snd l l' vp →
      l₀ = l' ∧ ∃ A B p, NeutEqTm Γ (max l l') vp p (.sigma l l' A B) ∧
      (Γ ⊢[l'] n ≡ .snd l l' A B p : C) ∧ (Γ ⊢[l'] C ≡ B.subst (Expr.fst l l' A B p).toSb) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case snd =>
    grind [WfTm.snd, NeutEqTm.wf_tm, WfTm.wf_tp, WfTp.inv_sigma, WfTp.wf_ctx, WfCtx.inv_snoc]

/-! ## Functionality of value relations -/

theorem uniq_all {Γ} :
    (∀ {l vA A}, ValEqTp Γ l vA A → ∀ {A'}, ValEqTp Γ l vA A' → Γ ⊢[l] A ≡ A') ∧
    (∀ {l vt t A}, ValEqTm Γ l vt t A → ∀ {t'}, ValEqTm Γ l vt t' A → Γ ⊢[l] t ≡ t' : A) ∧
    /- Technicality: `ValEqTm` does not need the generalization to `A'`
    because the only terms that 'forget' type information
    are elimination forms which must be neutral as values. -/
    (∀ {l vt t A}, NeutEqTm Γ l vt t A → ∀ {t' A'}, NeutEqTm Γ l vt t' A' →
      (Γ ⊢[l] A ≡ A') ∧ (Γ ⊢[l] t ≡ t' : A)) ∧
    (∀ {l l' A vB B}, ClosEqTp Γ l l' A vB B → ∀ {B'}, ClosEqTp Γ l l' A vB B' →
      (A, l) :: Γ ⊢[l'] B ≡ B') ∧
    (∀ {l l' A B vb b}, ClosEqTm Γ l l' A B vb b → ∀ {b'}, ClosEqTm Γ l l' A B vb b' →
      (A, l) :: Γ ⊢[l'] b ≡ b' : B) ∧
    (∀ {E σ Γ'}, EnvEqSb Γ E σ Γ' → ∀ {σ'}, EnvEqSb Γ E σ' Γ' →
      EqSb Γ σ σ' Γ') := by
  /- 2025-07-20: I think this could go by induction on `Val`,
  but my `mutual_induction` tactic doesn't support that. -/
  mutual_induction ValEqTp
  all_goals dsimp; intros; try exact True.intro
  case pi => grind [ValEqTp.inv_pi, cases ClosEqTp, ClosEqTp.clos_tp, EqTp.cong_pi]
  case sigma => grind [ValEqTp.inv_sigma, cases ClosEqTp, ClosEqTp.clos_tp, EqTp.cong_sigma]
  case univ h =>
    have := h.inv_univ
    grind
  case el => grind [ValEqTp.inv_el, EqTp.cong_el]
  case conv_tp => grind
  case lam ihb _ vl =>
    have ⟨_, _, _, _, vb, eqt, eq⟩ := vl.inv_lam
    apply EqTm.trans_tm _ eqt.symm_tm
    have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_pi
    gcongr
    rcases vb with ⟨env, Aeq', Beq', b⟩
    have Aeq'' := Aeq'.trans_tp Aeq.symm_tp
    have := Beq'.conv_binder Aeq.symm_tp |>.trans_tp Beq.symm_tp
    exact ihb ⟨env, Aeq'', this, b⟩
  case pair iht ihu _ vp =>
    have ⟨_, _, _, _, _, vt, vu, eqt, eq⟩ := vp.inv_pair
    apply EqTm.trans_tm _ eqt.symm_tm
    have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_sigma
    have := iht (vt.conv_tp Aeq.symm_tp)
    gcongr
    . apply ihu (vu.conv_tp _)
      exact Beq.symm_tp.subst_eq (EqSb.toSb this.symm_tm)
  case code => grind [ValEqTm.inv_code, EqTm.cong_code]
  case neut_tm vn =>
    have := vn.inv_neut
    grind
  case conv_nf Aeq ih _ vt =>
    have := ih (vt.conv_tp Aeq.symm_tp)
    grind [EqTm.conv_eq]
  case bvar lk _ _ _ =>
    have := lk.lt_length
    grind [EqTm.conv_eq, Lookup.tp_uniq, NeutEqTm.inv_bvar]
  case app ihf iha _ _ vn =>
    have ⟨_, _, _, _, _, vf, va, eqt, eq⟩ := vn.inv_app
    have ⟨peq, feq⟩ := ihf vf
    have ⟨_, _, _, Aeq, Beq⟩ := peq.inv_pi
    have aeq := iha <| va.conv_tp Aeq.symm_tp
    refine ⟨?teq, (fun teq => ?_) ?teq⟩
    . apply EqTp.trans_tp _ eq.symm_tp
      exact Beq.subst_eq (EqSb.toSb aeq)
    . apply EqTm.trans_tm _ <| eqt.symm_tm.conv_eq (by grind)
      gcongr
  case fst ih _ _ vn =>
    have ⟨_, _, _, _, vp, eqt, eq⟩ := vn.inv_fst
    have ⟨seq, peq⟩ := ih vp
    have ⟨_, _, _, Aeq, Beq⟩ := seq.inv_sigma
    constructor
    . grind
    . apply EqTm.trans_tm _ <| eqt.symm_tm.conv_eq (by grind)
      gcongr
  case snd ih _ _ vn =>
    have ⟨_, _, _, _, vp, eqt, eq⟩ := vn.inv_snd
    have ⟨seq, peq⟩ := ih vp
    have ⟨_, _, _, Aeq, Beq⟩ := seq.inv_sigma
    refine ⟨?teq2, (fun teq => ?_) ?teq2⟩
    . apply EqTp.trans_tp _ eq.symm_tp
      gcongr
      apply EqSb.toSb
      gcongr
    . apply EqTm.trans_tm _ <| eqt.symm_tm.conv_eq (by grind)
      gcongr
  case conv_neut => grind [EqTm.conv_eq]
  case clos_tp ih _ c =>
    rcases c with ⟨env, Aeq, B⟩
    have A := B.wf_binder
    have := B.subst_eq ((ih env).up A)
    exact this.conv_binder <| (A.subst_eq (ih env)).trans_tp Aeq
  case clos_tm ih _ c =>
    rcases c with ⟨env, Aeq, Beq, b⟩
    have A := b.wf_binder
    have := b.subst_eq ((ih env).symm.up A) |>.conv_binder Aeq
      |>.conv_eq Beq
    exact this.symm_tm
  case nil => grind [EqSb.terminal]
  case snoc => grind [cases EnvEqSb, EqSb.snoc, ValEqTm.conv_tp, WfTp.subst_eq]

theorem ValEqTp.tp_uniq {Γ l vA A A'} : ValEqTp Γ l vA A → ValEqTp Γ l vA A' → Γ ⊢[l] A ≡ A' :=
  fun h h' => uniq_all.1 h h'

theorem ValEqTm.tm_uniq {Γ l vt t t' A} : ValEqTm Γ l vt t A → ValEqTm Γ l vt t' A →
    Γ ⊢[l] t ≡ t' : A :=
  fun h h' => uniq_all.2.1 h h'

theorem NeutEqTm.tm_uniq {Γ l vn n A n' A'} : NeutEqTm Γ l vn n A → NeutEqTm Γ l vn n' A' →
    Γ ⊢[l] n ≡ n' : A :=
  fun h h' => uniq_all.2.2.1 h h' |>.2

theorem ClosEqTp.tp_uniq {Γ l l' A vB B B'} : ClosEqTp Γ l l' A vB B → ClosEqTp Γ l l' A vB B' →
    (A, l) :: Γ ⊢[l'] B ≡ B' :=
  fun h h' => uniq_all.2.2.2.1 h h'

theorem ClosEqTm.tm_uniq {Γ l l' A B vb b b'} : ClosEqTm Γ l l' A B vb b →
    ClosEqTm Γ l l' A B vb b' → (A, l) :: Γ ⊢[l'] b ≡ b' : B :=
  fun h h' => uniq_all.2.2.2.2.1 h h'

theorem EnvEqSb.sb_uniq {Δ E σ σ' Γ} : EnvEqSb Δ E σ Γ → EnvEqSb Δ E σ' Γ → EqSb Δ σ σ' Γ :=
  fun h h' => uniq_all.2.2.2.2.2 h h'
