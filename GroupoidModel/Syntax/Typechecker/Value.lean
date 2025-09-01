import GroupoidModel.Syntax.GCongr
import GroupoidModel.Syntax.Injectivity
import GroupoidModel.Syntax.Synth
import GroupoidModel.Syntax.Axioms

variable {χ : Type*} {E : Axioms χ}

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
variable (χ : Type*)

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
  | Id (l : Nat) (A t u : Val)
  | univ (l : Nat)
  /-- Although `el` is an eliminator,
  as a neutral form it does not need to be annotated with a type
  (because it itself is a type).
  So we embed it in `Val` directly rather than through `Val.neut`. -/
  | el (a : Neut)
  | lam (l l' : Nat) (vA : Val) (b : Clos)
  | pair (l l' : Nat) (t u : Val)
  | refl (l : Nat) (t : Val)
  | code (A : Val)
  /-- A neutral form at the given type. -/
  | neut (n : Neut) (A : Val)
  deriving Inhabited

/-- Neutral forms are elimination forms that are 'stuck',
i.e., contain no β-reducible subterm. -/
inductive Neut where
  | ax (c : χ) (A : Val)
  /-- A de Bruijn *level*. -/
  | bvar (i : Nat)
  /-- Application at the specified argument type. -/
  | app (l l' : Nat) (A : Val) (f : Neut) (a : Val)
  | fst (l l' : Nat) (p : Neut)
  | snd (l l' : Nat) (p : Neut)
  | idRec (l l' : Nat) (A a : Val) (M : Clos) (r : Val) (h : Neut)
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
  | of_expr (env : List Val) (t : Expr χ)
  deriving Inhabited
end

/-! ## Relation of values to terms -/

mutual
variable (E : Axioms χ)

inductive ValEqTp : Ctx χ → Nat → Val χ → Expr χ → Prop
  | pi {Γ vA A vB B l l'} :
    ValEqTp Γ l vA A →
    ClosEqTp Γ l l' A vB B →
    ValEqTp Γ (max l l') (.pi l l' vA vB) (.pi l l' A B)
  | sigma {Γ vA A vB B l l'} :
    ValEqTp Γ l vA A →
    ClosEqTp Γ l l' A vB B →
    ValEqTp Γ (max l l') (.sigma l l' vA vB) (.sigma l l' A B)
  | Id {Γ A vA vt t vu u l} :
    ValEqTp Γ l vA A →
    ValEqTm Γ l vt t A →
    ValEqTm Γ l vu u A →
    ValEqTp Γ l (.Id l vA vt vu) (.Id l A t u)
  | univ {Γ l} :
    WfCtx E Γ →
    l < univMax →
    ValEqTp Γ (l + 1) (.univ l) (.univ l)
  | el {Γ na a l} :
    NeutEqTm Γ (l + 1) na a (.univ l) →
    ValEqTp Γ l (.el na) (.el a)
  | conv_tp {Γ vA A A' l} :
    ValEqTp Γ l vA A →
    E ∣ Γ ⊢[l] A ≡ A' →
    ValEqTp Γ l vA A'

-- Note: neutral types are embedded in `Val` directly and don't need a `NeutEqTp` relation.

inductive ValEqTm : Ctx χ → Nat → Val χ → Expr χ → Expr χ → Prop
  | lam {Γ A B vA vb b l l'} :
    ValEqTp Γ l vA A →
    ClosEqTm Γ l l' A B vb b →
    ValEqTm Γ (max l l') (.lam l l' vA vb) (.lam l l' A b) (.pi l l' A B)
  | pair {Γ A B vt t vu u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    ValEqTm Γ l vt t A →
    ValEqTm Γ l' vu u (B.subst t.toSb) →
    ValEqTm Γ (max l l') (.pair l l' vt vu) (.pair l l' B t u) (.sigma l l' A B)
  | refl {Γ A vt t l} :
    ValEqTm Γ l vt t A →
    ValEqTm Γ l (.refl l vt) (.refl l t) (.Id l A t t)
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
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l] A ≡ A' →
    ValEqTm Γ l vt t' A'

inductive NeutEqTm : Ctx χ → Nat → Neut χ → Expr χ → Expr χ → Prop
  | ax {Γ c vA Al} :
    WfCtx E Γ →
    E c = some Al →
    ValEqTp Γ Al.val.2 vA Al.val.1 →
    NeutEqTm Γ Al.val.2 (.ax c vA) (.ax c Al.val.1) Al.val.1
  | bvar {Γ A i l} :
    WfCtx E Γ →
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
  | idRec {Γ vA A cM M va a vr r b nh h l l'} :
    ValEqTp Γ l vA A →
    ValEqTm Γ l va a A →
    Clos₂EqTp Γ A l (.Id l (A.subst Expr.wk) (a.subst Expr.wk) (.bvar 0)) l l' cM M →
    ValEqTm Γ l' vr r (M.subst (.snoc a.toSb <| .refl l a)) →
    NeutEqTm Γ l nh h (.Id l A a b) →
    NeutEqTm Γ l' (.idRec l l' vA va cM vr nh) (.idRec l l' a M r b h) (M.subst (.snoc b.toSb h))
  | conv_neut {Γ A A' vn n n' l} :
    NeutEqTm Γ l vn n A →
    E ∣ Γ ⊢[l] n ≡ n' : A →
    E ∣ Γ ⊢[l] A ≡ A' →
    NeutEqTm Γ l vn n' A'

/-- `ClosEqTp Δ l l' A vB B` -/
inductive ClosEqTp : Ctx χ → Nat → Nat → Expr χ → Clos χ → Expr χ → Prop
  | clos_tp {Δ Γ A B Aenv env σ l l'} :
    EnvEqSb Δ env σ Γ →
    -- The equality argument builds in conversion.
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    E ∣ (A, l) :: Γ ⊢[l'] B →
    ClosEqTp Δ l l' Aenv (.of_expr env B) (B.subst <| Expr.up σ)
  | clos_val_tp {Δ Γ A B Aenv vB env σ l l'} :
    EnvEqSb Δ env σ Γ →
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    ValEqTp ((A, l) :: Γ) l' vB B →
    ClosEqTp Δ l l' Aenv (.of_val env vB) (B.subst <| Expr.up σ)

/- Can `ClosEqTp` and `Clos₂EqTp` be subsumed by `ClosₙEqTp` that takes a context?
Would need defining substitution on contexts, and `Expr.upN`. -/
inductive Clos₂EqTp : Ctx χ → Expr χ → Nat → Expr χ → Nat → Nat → Clos χ → Expr χ → Prop
  | clos₂_tp {Δ Γ A B C Aenv Benv env σ l l' l''} :
    EnvEqSb Δ env σ Γ →
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    E ∣ (Aenv, l) :: Δ ⊢[l'] B.subst (Expr.up σ) ≡ Benv →
    E ∣ (B, l') :: (A, l) :: Γ ⊢[l''] C →
    Clos₂EqTp Δ Aenv l Benv l' l'' (.of_expr env C) (C.subst <| Expr.up <| Expr.up σ)
  | clos₂_val_tp {Δ Γ A B C vC Aenv Benv env σ l l' l''} :
    EnvEqSb Δ env σ Γ →
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    E ∣ (Aenv, l) :: Δ ⊢[l'] B.subst (Expr.up σ) ≡ Benv →
    ValEqTp ((B, l') :: (A, l) :: Γ) l'' vC C →
    Clos₂EqTp Δ Aenv l Benv l' l'' (.of_val env vC) (C.subst <| Expr.up <| Expr.up σ)

/-- `ClosEqTm Δ l l' A B vb b` -/
inductive ClosEqTm : Ctx χ → Nat → Nat → Expr χ → Expr χ → Clos χ → Expr χ → Prop
  | clos_tm {Δ Γ A B Aenv Benv b env σ l l'} :
    EnvEqSb Δ env σ Γ →
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    E ∣ (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up σ) ≡ Benv →
    E ∣ (A, l) :: Γ ⊢[l'] b : B →
    ClosEqTm Δ l l' Aenv Benv (.of_expr env b) (b.subst <| Expr.up σ)
  | clos_val_tm {Δ Γ A B Aenv Benv b vb env σ l l'} :
    EnvEqSb Δ env σ Γ →
    E ∣ Δ ⊢[l] A.subst σ ≡ Aenv →
    E ∣ (Aenv, l) :: Δ ⊢[l'] (B.subst <| Expr.up σ) ≡ Benv →
    ValEqTm ((A, l) :: Γ) l' vb b B →
    ClosEqTm Δ l l' Aenv Benv (.of_val env vb) (b.subst <| Expr.up σ)

inductive EnvEqSb : Ctx χ → List (Val χ) → (Nat → Expr χ) → Ctx χ → Prop
  /- Possible optimization: allow `EnvEqSb Γ [] Expr.bvar Γ`
  and replace `envOfLen ‖Γ‖` by `[]`. -/
  | nil {Γ} (σ) : WfCtx E Γ → EnvEqSb Γ [] σ []
  | snoc {Δ Γ A vt t Eᵥ σ l} :
    EnvEqSb Δ Eᵥ σ Γ →
    E ∣ Γ ⊢[l] A →
    ValEqTm Δ l vt t (A.subst σ) →
    EnvEqSb Δ (vt :: Eᵥ) (Expr.snoc σ t) ((A, l) :: Γ)
end

/-! ## Well-formed evaluation environments -/

namespace EnvEqSb

theorem wf_dom : ∀ {Δ Eᵥ σ Γ}, EnvEqSb E Δ Eᵥ σ Γ → WfCtx E Δ := by
  mutual_induction EnvEqSb
  all_goals grind

theorem wf_cod : ∀ {Δ Eᵥ σ Γ}, EnvEqSb E Δ Eᵥ σ Γ → WfCtx E Γ := by
  mutual_induction EnvEqSb
  all_goals grind [WfCtx.nil, WfCtx.snoc]

theorem eq_length : ∀ {Δ Eᵥ σ Γ}, EnvEqSb E Δ Eᵥ σ Γ → Eᵥ.length = Γ.length := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  all_goals simp; try grind

theorem lookup_lt {Δ Γ Eᵥ σ i A l} : EnvEqSb E Δ Eᵥ σ Γ → Lookup Γ i A l → i < Eᵥ.length :=
  fun env lk => env.eq_length ▸ lk.lt_length

theorem lookup_eq : ∀ {Δ Eᵥ σ Γ}, (env : EnvEqSb E Δ Eᵥ σ Γ) →
    ∀ {A i l}, (lk : Lookup Γ i A l) →
    ValEqTm E Δ l (Eᵥ[i]'(env.lookup_lt lk)) (σ i) (A.subst σ) := by
  mutual_induction EnvEqSb
  all_goals intros; try exact True.intro
  case nil lk => cases lk
  case snoc E A v ih _ _ _ _ lk =>
    rcases lk with _ | ⟨_, _, lk⟩
    . exact autosubst% v
    . exact autosubst% ih lk

private lemma Expr.eq_snoc_get_zero (σ : Nat → Expr χ) :
    σ = Expr.snoc (Expr.comp σ Expr.wk) (σ 0) := by
  ext i; cases i <;> rfl

theorem mk : ∀ {Γ}, WfCtx E Γ → ∀ {Δ} {Eᵥ : List (Val χ)} {σ},
    WfCtx E Δ → (eq : Γ.length = Eᵥ.length) →
    (∀ {i A l}, (lk : Lookup Γ i A l) →
      ValEqTm E Δ l (Eᵥ[i]'(eq ▸ lk.lt_length)) (σ i) (A.subst σ)) →
    EnvEqSb E Δ Eᵥ σ Γ := by
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
        exact autosubst% h (lk.succ ..)
      . assumption
      . exact autosubst% h (Lookup.zero ..)

end EnvEqSb

/-! ## Values are well-typed as expressions -/

private theorem wf_expr :
    (∀ {Γ l vA A}, ValEqTp E Γ l vA A → E ∣ Γ ⊢[l] A) ∧
    (∀ {Γ l vt t A}, ValEqTm E Γ l vt t A → E ∣ Γ ⊢[l] t : A) ∧
    (∀ {Γ l vt t A}, NeutEqTm E Γ l vt t A → E ∣ Γ ⊢[l] t : A) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp E Γ l l' A vB B → E ∣ (A, l) :: Γ ⊢[l'] B) ∧
    (∀ {Γ A l B l' l'' cC C}, Clos₂EqTp E Γ A l B l' l'' cC C → E ∣ (B, l') :: (A, l) :: Γ ⊢[l''] C) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm E Γ l l' A B vb b → E ∣ (A, l) :: Γ ⊢[l'] b : B) ∧
    (∀ {Γ Eᵥ σ Γ'}, EnvEqSb E Γ Eᵥ σ Γ' → WfSb E Γ σ Γ') := by
  mutual_induction ValEqTp
  all_goals dsimp; intros
  case ax => apply WfTm.ax <;> assumption
  case conv_tp => grind [EqTp.wf_right]
  case conv_nf tt' AA' _ => exact tt'.wf_right.conv AA'
  case conv_neut nn' AA' _ => exact nn'.wf_right.conv AA'
  case clos₂_tp Aenv Benv C σ =>
    have B := C.wf_binder
    have A := B.wf_binder
    apply C.subst (σ.up A |>.up B) |>.conv_ctx
    apply EqCtx.refl Aenv.wf_ctx
      |>.snoc Aenv
      |>.snoc (Benv.conv_binder Aenv.symm_tp)
  case clos₂_val_tp Aenv Benv _ σ C =>
    have B := C.wf_binder
    have A := B.wf_binder
    apply C.subst (σ.up A |>.up B) |>.conv_ctx
    apply EqCtx.refl Aenv.wf_ctx
      |>.snoc Aenv
      |>.snoc (Benv.conv_binder Aenv.symm_tp)
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
  grind_cases

theorem ValEqTp.wf_tp {Γ l vA A} (h : ValEqTp E Γ l vA A) : E ∣ Γ ⊢[l] A :=
  _root_.wf_expr.1 h

theorem ValEqTm.wf_tm {Γ l vt t A} (h : ValEqTm E Γ l vt t A) : E ∣ Γ ⊢[l] t : A :=
  _root_.wf_expr.2.1 h

theorem NeutEqTm.wf_tm {Γ l vt t A} (h : NeutEqTm E Γ l vt t A) : E ∣ Γ ⊢[l] t : A :=
  _root_.wf_expr.2.2.1 h

theorem ClosEqTp.wf_tp {Γ l l' A vB B} (h : ClosEqTp E Γ l l' A vB B) :
    E ∣ (A, l) :: Γ ⊢[l'] B :=
  _root_.wf_expr.2.2.2.1 h

theorem Clos₂EqTp.wf_tp {Γ A B C vC l l' l''} (h : Clos₂EqTp E Γ A l B l' l'' vC C) :
    E ∣ (B, l') :: (A, l) :: Γ ⊢[l''] C :=
  _root_.wf_expr.2.2.2.2.1 h

theorem ClosEqTm.wf_tm {Γ l l' A B vb b} (h : ClosEqTm E Γ l l' A B vb b) :
    E ∣ (A, l) :: Γ ⊢[l'] b : B :=
  _root_.wf_expr.2.2.2.2.2.1 h

theorem EnvEqSb.wf_sb {Δ Eᵥ σ Γ} (h : EnvEqSb E Δ Eᵥ σ Γ) : WfSb E Δ σ Γ :=
  _root_.wf_expr.2.2.2.2.2.2 h

theorem ValEqTm.conv_tm {Γ A vt t t' l} :
    ValEqTm E Γ l vt t A → E ∣ Γ ⊢[l] t ≡ t' : A → ValEqTm E Γ l vt t' A :=
  fun h eq => h.conv_nf eq (EqTp.refl_tp eq.wf_tp)

theorem ValEqTm.conv_tp {Γ A A' vt t l} :
    ValEqTm E Γ l vt t A → E ∣ Γ ⊢[l] A ≡ A' → ValEqTm E Γ l vt t A' :=
  fun h eq => h.conv_nf (EqTm.refl_tm h.wf_tm) eq

theorem NeutEqTm.conv_tm {Γ A vt t t' l} :
    NeutEqTm E Γ l vt t A → E ∣ Γ ⊢[l] t ≡ t' : A → NeutEqTm E Γ l vt t' A :=
  fun h eq => h.conv_neut eq (EqTp.refl_tp eq.wf_tp)

theorem NeutEqTm.conv_tp {Γ A A' vt t l} :
    NeutEqTm E Γ l vt t A → E ∣ Γ ⊢[l] A ≡ A' → NeutEqTm E Γ l vt t A' :=
  fun h eq => h.conv_neut (EqTm.refl_tm h.wf_tm) eq

/-! ## Values are closed under context conversion -/

attribute [local grind →] EqCtx.length_eq WfTp.conv_ctx EqTp.conv_ctx WfTm.conv_ctx EqTm.conv_ctx in
private theorem conv_ctx :
    (∀ {Γ l vA A}, ValEqTp E Γ l vA A → ∀ {Γ'},
      EqCtx E Γ Γ' → ValEqTp E Γ' l vA A) ∧
    (∀ {Γ l vt t A}, ValEqTm E Γ l vt t A → ∀ {Γ'},
      EqCtx E Γ Γ' → ValEqTm E Γ' l vt t A) ∧
    (∀ {Γ l vt t A}, NeutEqTm E Γ l vt t A → ∀ {Γ'},
      EqCtx E Γ Γ' → NeutEqTm E Γ' l vt t A) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp E Γ l l' A vB B → ∀ {Γ'},
      EqCtx E Γ Γ' → ClosEqTp E Γ' l l' A vB B) ∧
    (∀ {Γ A l B l' l'' vC C}, Clos₂EqTp E Γ A l B l' l'' vC C →
      ∀ {Γ'}, EqCtx E Γ Γ' → Clos₂EqTp E Γ' A l B l' l'' vC C) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm E Γ l l' A B vb b → ∀ {Γ'}, EqCtx E Γ Γ' →
      ClosEqTm E Γ' l l' A B vb b) ∧
    (∀ {Γ Eᵥ σ Δ}, EnvEqSb E Γ Eᵥ σ Δ → ∀ {Γ'}, EqCtx E Γ Γ' → EnvEqSb E Γ' Eᵥ σ Δ) := by
  mutual_induction ValEqTp
  all_goals intros
  case ax => apply NeutEqTm.ax <;> grind [EqCtx.wf_right]
  case univ => grind [ValEqTp.univ, EqCtx.wf_right]
  case pair B _ _ _ _ _ eq =>
    apply ValEqTm.pair (B.conv_ctx (eq.snoc <| EqTp.refl_tp B.wf_binder)) <;> grind
  case bvar lk _ eq =>
    have ⟨A', _, lk'⟩ := Lookup.of_lt_length <| eq.length_eq ▸ lk.lt_length
    obtain ⟨rfl, eqA⟩ := eq.lookup_eq lk lk'
    have := NeutEqTm.bvar eq.wf_right lk'
    rw [eq.length_eq]
    exact NeutEqTm.conv_neut this (EqTm.refl_tm this.wf_tm) (eqA.symm_tp.conv_ctx eq)
  case clos₂_tp Aeq Beq C ihE _ eq =>
    apply Clos₂EqTp.clos₂_tp (ihE eq) (Aeq.conv_ctx eq) (Beq.conv_ctx _) C
    grind [Clos₂EqTp.clos₂_tp, EqTp.conv_ctx, EqCtx.snoc, EqTp.trans_tp, EqTp.symm_tp]
  case clos₂_val_tp Aeq Beq C ihE _ _ eq =>
    apply Clos₂EqTp.clos₂_val_tp (ihE eq) (Aeq.conv_ctx eq) (Beq.conv_ctx _) C
    grind [Clos₂EqTp.clos₂_tp, EqTp.conv_ctx, EqCtx.snoc, EqTp.trans_tp, EqTp.symm_tp]
  case clos_tm Aeq Beq b env _ eq =>
    exact ClosEqTm.clos_tm (env eq) (Aeq.conv_ctx eq)
      (Beq.conv_ctx <| eq.snoc <| EqTp.refl_tp Aeq.wf_right)
      (b.conv_ctx b.wf_ctx.eq_self)
  case clos_val_tm Aeq Beq vb env _ _ eq =>
    exact ClosEqTm.clos_val_tm (env eq) (Aeq.conv_ctx eq)
      (Beq.conv_ctx <| eq.snoc <| EqTp.refl_tp Aeq.wf_right) vb
  case nil eq => exact .nil _ eq.wf_right
  grind_cases

theorem ValEqTp.conv_ctx {Γ Γ' l vA A} : ValEqTp E Γ l vA A → EqCtx E Γ Γ' → ValEqTp E Γ' l vA A :=
  fun h eq => _root_.conv_ctx.1 h eq

theorem ValEqTm.conv_ctx {Γ Γ' l vt t A} : ValEqTm E Γ l vt t A → EqCtx E Γ Γ' →
    ValEqTm E Γ' l vt t A :=
  fun h eq => _root_.conv_ctx.2.1 h eq

theorem NeutEqTm.conv_ctx {Γ Γ' l vt t A} : NeutEqTm E Γ l vt t A → EqCtx E Γ Γ' →
    NeutEqTm E Γ' l vt t A :=
  fun h eq => _root_.conv_ctx.2.2.1 h eq

theorem ClosEqTp.conv_ctx {Γ Γ' l l' A vB B} : ClosEqTp E Γ l l' A vB B → EqCtx E Γ Γ' →
    ClosEqTp E Γ' l l' A vB B :=
  fun h eq => _root_.conv_ctx.2.2.2.1 h eq

theorem Clos₂EqTp.conv_ctx {Γ Γ' A B C vC l l' l''} :
    Clos₂EqTp E Γ A l B l' l'' vC C →
    EqCtx E Γ Γ' →
    Clos₂EqTp E Γ' A l B l' l'' vC C :=
  fun h eq => _root_.conv_ctx.2.2.2.2.1 h eq

theorem ClosEqTm.conv_ctx {Γ Γ' l l' A B vb b} :
    ClosEqTm E Γ l l' A B vb b → EqCtx E Γ Γ' → ClosEqTm E Γ' l l' A B vb b :=
  fun h eq => _root_.conv_ctx.2.2.2.2.2.1 h eq

theorem EnvEqSb.conv_dom {Δ Δ' Eᵥ σ Γ} : EnvEqSb E Δ Eᵥ σ Γ → EqCtx E Δ Δ' → EnvEqSb E Δ' Eᵥ σ Γ :=
  fun h eq => _root_.conv_ctx.2.2.2.2.2.2 h eq

/-! ## Weakening is free -/

private theorem wk_all :
    (∀ {Γ l vA A}, ValEqTp E Γ l vA A → ∀ {C k}, E ∣ Γ ⊢[k] C →
      ValEqTp E ((C,k) :: Γ) l vA (A.subst Expr.wk)) ∧
    (∀ {Γ l vt t A}, ValEqTm E Γ l vt t A → ∀ {C k}, E ∣ Γ ⊢[k] C →
      ValEqTm E ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {Γ l vt t A}, NeutEqTm E Γ l vt t A → ∀ {C k}, E ∣ Γ ⊢[k] C →
      NeutEqTm E ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk)) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp E Γ l l' A vB B → ∀ {C k}, E ∣ Γ ⊢[k] C →
      ClosEqTp E ((C,k) :: Γ) l l' (A.subst Expr.wk) vB (B.subst (Expr.up Expr.wk))) ∧
    (∀ {Γ A l B l' l'' vC C}, Clos₂EqTp E Γ A l B l' l'' vC C → ∀ {D k}, E ∣ Γ ⊢[k] D →
      Clos₂EqTp E ((D,k) :: Γ) (A.subst Expr.wk) l (B.subst (Expr.up Expr.wk)) l' l''
        vC (C.subst (Expr.up <| Expr.up Expr.wk))) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm E Γ l l' A B vb b → ∀ {C k}, E ∣ Γ ⊢[k] C →
      ClosEqTm E ((C,k) :: Γ) l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk))
        vb (b.subst (Expr.up Expr.wk))) ∧
    (∀ {Γ Eᵥ σ Δ}, EnvEqSb E Γ Eᵥ σ Δ → ∀ {C k}, E ∣ Γ ⊢[k] C →
      EnvEqSb E ((C,k) :: Γ) Eᵥ (Expr.comp Expr.wk σ) Δ) := by
  mutual_induction ValEqTp
  all_goals intros; try dsimp [Expr.subst] at *
  case ax Al _ _ _ ihA _ _ C =>
    have := ihA C
    rw [Expr.subst_of_isClosed _ Al.2.1] at this ⊢
    apply NeutEqTm.ax <;> grind [WfCtx.snoc]
  case univ => grind [ValEqTp.univ, WfCtx.snoc]
  case conv_tp => grind [ValEqTp.conv_tp, EqTp.subst, WfSb.wk]
  case pair B _ _ iht ihu _ _ C =>
    have := B.subst (WfSb.wk C |>.up B.wf_binder)
    apply ValEqTm.pair this (iht C) (autosubst% ihu C)
  case conv_nf => grind [ValEqTm.conv_nf, EqTp.subst, EqTm.subst, WfSb.wk]
  case bvar Γ lk _ _ C =>
    convert NeutEqTm.bvar (Γ.snoc C) (.succ _ _ lk) using 1; grind
  case app ihA ihf iha _ _ C =>
    exact autosubst% NeutEqTm.app (ihA C) (ihf C) (iha C)
  case snd ih _ _ C =>
    exact autosubst% NeutEqTm.snd (ih C)
  case idRec b _ ihA iha ihM ihr ihh _ _ C =>
    exact autosubst% NeutEqTm.idRec
      (ihA C)
      (iha C)
      (autosubst% ihM C)
      (autosubst% ihr C)
      (ihh C)
  case conv_neut => grind [NeutEqTm.conv_neut, EqTp.subst, EqTm.subst, WfSb.wk]
  case clos_tp Aeq B ihE _ _ C =>
    have := Aeq.subst (WfSb.wk C)
    exact autosubst% ClosEqTp.clos_tp (ihE C) (autosubst% this) B
  case clos_val_tp Aeq B ihE _ _ _ C =>
    have := Aeq.subst (WfSb.wk C)
    exact autosubst% ClosEqTp.clos_val_tp (ihE C) (autosubst% this) B
  case clos₂_tp Aeq Beq C ihE _ _ D =>
    have Aeq' := Aeq.subst (WfSb.wk D)
    have Beq' := Beq.subst (WfSb.up (WfSb.wk D) Aeq.wf_right)
    exact autosubst% Clos₂EqTp.clos₂_tp (ihE D) (autosubst% Aeq') (autosubst% Beq') C
  case clos₂_val_tp Aeq Beq C ihE _ _ _ D =>
    have Aeq' := Aeq.subst (WfSb.wk D)
    have Beq' := Beq.subst (WfSb.up (WfSb.wk D) Aeq.wf_right)
    exact autosubst% Clos₂EqTp.clos₂_val_tp (ihE D) (autosubst% Aeq') (autosubst% Beq') C
  case clos_tm Aeq Beq b ihE _ _ C =>
    have CAeq := Aeq.subst <| WfSb.wk C
    have CBeq := Beq.subst <| (WfSb.wk C).up Aeq.wf_right
    exact autosubst% ClosEqTm.clos_tm (ihE C) (autosubst% CAeq) (autosubst% CBeq) b
  case clos_val_tm Aeq Beq vb ihE _ _ _ C =>
    have CAeq := Aeq.subst <| WfSb.wk C
    have CBeq := Beq.subst <| (WfSb.wk C).up Aeq.wf_right
    exact autosubst% ClosEqTm.clos_val_tm (ihE C) (autosubst% CAeq) (autosubst% CBeq) vb
  case nil C => apply EnvEqSb.nil _ (C.wf_ctx.snoc C)
  case snoc =>
    simp only [autosubst] at *
    grind [EnvEqSb.snoc]
  grind_cases

theorem ValEqTp.wk {Γ l vA A} (h : ValEqTp E Γ l vA A) {C k} (hC : E ∣ Γ ⊢[k] C) :
    ValEqTp E ((C,k) :: Γ) l vA (A.subst Expr.wk) :=
  wk_all.1 h hC

theorem ValEqTm.wk {Γ l vt t A} (h : ValEqTm E Γ l vt t A) {C k} (hC : E ∣ Γ ⊢[k] C) :
    ValEqTm E ((C,k) :: Γ) l vt (t.subst Expr.wk) (A.subst Expr.wk) :=
  wk_all.2.1 h hC

theorem NeutEqTm.wk {Γ l vn n A} (h : NeutEqTm E Γ l vn n A) {C k} (hC : E ∣ Γ ⊢[k] C) :
    NeutEqTm E ((C,k) :: Γ) l vn (n.subst Expr.wk) (A.subst Expr.wk) :=
  wk_all.2.2.1 h hC

theorem ClosEqTp.wk {Γ l l' A vB B} (h : ClosEqTp E Γ l l' A vB B) {C k} (hC : E ∣ Γ ⊢[k] C) :
    ClosEqTp E ((C,k) :: Γ) l l' (A.subst Expr.wk) vB (B.subst (Expr.up Expr.wk)) :=
  wk_all.2.2.2.1 h hC

theorem Clos₂EqTp.wk {Γ A l B l' l'' vC C} (h : Clos₂EqTp E Γ A l B l' l'' vC C)
    {D k} (hD : E ∣ Γ ⊢[k] D) :
    Clos₂EqTp E ((D,k) :: Γ) (A.subst Expr.wk) l (B.subst (Expr.up Expr.wk)) l' l''
      vC (C.subst (Expr.up (Expr.up Expr.wk))) :=
  wk_all.2.2.2.2.1 h hD

theorem ClosEqTm.wk {Γ l l' A B vb b} (h : ClosEqTm E Γ l l' A B vb b) {C k} (hC : E ∣ Γ ⊢[k] C) :
    ClosEqTm E ((C,k) :: Γ) l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk))
      vb (b.subst (Expr.up Expr.wk)) :=
  wk_all.2.2.2.2.2.1 h hC

theorem EnvEqSb.wk {Δ Eᵥ σ Γ} (h : EnvEqSb E Δ Eᵥ σ Γ) {C k} (hC : E ∣ Δ ⊢[k] C) :
    EnvEqSb E ((C,k) :: Δ) Eᵥ (Expr.comp Expr.wk σ) Γ :=
  wk_all.2.2.2.2.2.2 h hC

/-! ## Type environments -/

/-- A type environment is a context where all types are in NF. -/
abbrev TpEnv (χ) := List (Val χ × Nat)

variable (E : Axioms χ) in
inductive TpEnvEqCtx : TpEnv χ → Ctx χ → Prop
  | nil : TpEnvEqCtx [] []
  | snoc {vΓ Γ l vA A} :
    TpEnvEqCtx vΓ Γ →
    ValEqTp E Γ l vA A →
    TpEnvEqCtx ((vA, l) :: vΓ) ((A, l) :: Γ)

namespace TpEnvEqCtx

theorem wf_ctx {vΓ Γ} : TpEnvEqCtx E vΓ Γ → WfCtx E Γ := by
  intro vΓ; induction vΓ <;> grind [WfCtx.nil, WfCtx.snoc, ValEqTp.wf_tp]

theorem length_eq {vΓ Γ} : TpEnvEqCtx E vΓ Γ → vΓ.length = Γ.length := by
  intro vΓ; induction vΓ <;> simp [*]

theorem lt_length {vΓ Γ i A l} : TpEnvEqCtx E vΓ Γ → Lookup Γ i A l → i < vΓ.length :=
  fun vΓ lk => vΓ.length_eq ▸ lk.lt_length

theorem lvl_eq {vΓ Γ i A l} : (h : TpEnvEqCtx E vΓ Γ) → (lk : Lookup Γ i A l) →
    (vΓ[i]'(h.lt_length lk)).2 = l := by
  intro h lk
  induction h generalizing i A <;> cases lk <;> grind
theorem lookup_wf {vΓ Γ i A l} : (h : TpEnvEqCtx E vΓ Γ) → (lk : Lookup Γ i A l) →
    ValEqTp E Γ l (vΓ[i]'(h.lt_length lk)).1 A := by
  intro h lk
  induction h generalizing i A <;> cases lk
  case zero vA => exact vA.wk vA.wf_tp
  case snoc vA ih _ _ lk => exact (ih lk).wk vA.wf_tp

end TpEnvEqCtx

/-! ## Type environments from contexts -/

namespace TpEnv

/-- An identity evaluation environment (i.e., bvars remain themselves)
for the given type environment. -/
def toEnv (vΓ : TpEnv χ) : List (Val χ) :=
  vΓ.mapIdx fun i (vA, _) => .neut (.bvar <| vΓ.length - i - 1) vA

@[simp]
theorem length_toEnv (vΓ : TpEnv χ) : vΓ.toEnv.length = vΓ.length := by
  simp [toEnv]

@[simp]
theorem toEnv_cons (vA : Val χ) (l : Nat) (vΓ : TpEnv χ) :
    toEnv ((vA, l) :: vΓ) = .neut (.bvar vΓ.length) vA :: vΓ.toEnv := by
  simp [toEnv, List.mapIdx_cons]

end TpEnv

theorem TpEnvEqCtx.toEnv_wf {vΓ Γ} : TpEnvEqCtx E vΓ Γ → EnvEqSb E Γ vΓ.toEnv Expr.bvar Γ := by
  intro vΓ
  have Γ := vΓ.wf_ctx
  refine EnvEqSb.mk Γ Γ ?_ fun lk => ?_
  . rw [TpEnv.length_toEnv, vΓ.length_eq]
  . simp only [TpEnv.toEnv, List.getElem_mapIdx]
    apply ValEqTm.neut_tm
    . exact autosubst% vΓ.lookup_wf lk
    . rw [vΓ.length_eq]
      apply NeutEqTm.bvar Γ
      exact autosubst% lk

/-! ## Monotonicity w.r.t. axioms -/

attribute [local grind] WfCtx.of_axioms_le WfTp.of_axioms_le WfTm.of_axioms_le EqTp.of_axioms_le
  EqTm.of_axioms_le in
private theorem of_axioms_le {E E' : Axioms χ} (le : E ≤ E') :
    (∀ {Γ l vA A}, ValEqTp E Γ l vA A → ValEqTp E' Γ l vA A) ∧
    (∀ {Γ l vt t A}, ValEqTm E Γ l vt t A → ValEqTm E' Γ l vt t A) ∧
    (∀ {Γ l vt t A}, NeutEqTm E Γ l vt t A → NeutEqTm E' Γ l vt t A) ∧
    (∀ {Γ l l' A vB B}, ClosEqTp E Γ l l' A vB B → ClosEqTp E' Γ l l' A vB B) ∧
    (∀ {Γ A l B l' l'' vC C}, Clos₂EqTp E Γ A l B l' l'' vC C → Clos₂EqTp E' Γ A l B l' l'' vC C) ∧
    (∀ {Γ l l' A B vb b}, ClosEqTm E Γ l l' A B vb b → ClosEqTm E' Γ l l' A B vb b) ∧
    (∀ {Γ Eᵥ σ Δ}, EnvEqSb E Γ Eᵥ σ Δ → EnvEqSb E' Γ Eᵥ σ Δ) := by
  mutual_induction ValEqTp
  case ax => introv _ Ec _ ihA; apply NeutEqTm.ax _ (le Ec) ihA; grind
  grind_cases

theorem ValEqTp.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ l vA A} :
    ValEqTp E Γ l vA A → ValEqTp E' Γ l vA A :=
  fun h => _root_.of_axioms_le le |>.1 h

theorem ValEqTm.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ l vt t A} :
    ValEqTm E Γ l vt t A → ValEqTm E' Γ l vt t A :=
  fun h => _root_.of_axioms_le le |>.2.1 h

theorem NeutEqTm.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ l vn n A} :
    NeutEqTm E Γ l vn n A → NeutEqTm E' Γ l vn n A :=
  fun h => _root_.of_axioms_le le |>.2.2.1 h

theorem ClosEqTp.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ l l' A vB B} :
    ClosEqTp E Γ l l' A vB B → ClosEqTp E' Γ l l' A vB B :=
  fun h => _root_.of_axioms_le le |>.2.2.2.1 h

theorem Clos₂EqTp.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ A l B l' l'' vC C} :
    Clos₂EqTp E Γ A l B l' l'' vC C → Clos₂EqTp E' Γ A l B l' l'' vC C :=
  fun h => _root_.of_axioms_le le |>.2.2.2.2.1 h

theorem ClosEqTm.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Γ l l' A B vb b} :
    ClosEqTm E Γ l l' A B vb b → ClosEqTm E' Γ l l' A B vb b :=
  fun h => _root_.of_axioms_le le |>.2.2.2.2.2.1 h

theorem EnvEqSb.of_axioms_le {E E' : Axioms χ} (le : E ≤ E') {Δ Eᵥ σ Γ} :
    EnvEqSb E Δ Eᵥ σ Γ → EnvEqSb E' Δ Eᵥ σ Γ :=
  fun h => _root_.of_axioms_le le |>.2.2.2.2.2.2 h

/-! ## Misc lemmas -/

theorem ValEqTp.Id_bvar {Γ vA A va a l} : ValEqTp E Γ l vA A → ValEqTm E Γ l va a A →
    ValEqTp E ((A, l) :: Γ) l
      (.Id l vA va (.neut (.bvar Γ.length) vA))
      (.Id l (A.subst Expr.wk) (a.subst Expr.wk) (.bvar 0)) := by
  intro vA va
  have A := vA.wf_tp
  apply ValEqTp.Id (vA.wk A) (va.wk A)
  apply ValEqTm.neut_tm (vA.wk A)
  exact NeutEqTm.bvar (A.wf_ctx.snoc A) (.zero ..)
