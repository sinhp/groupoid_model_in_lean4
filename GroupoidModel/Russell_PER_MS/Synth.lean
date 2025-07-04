import GroupoidModel.Russell_PER_MS.Inversion

/-! ## Level and type synthesis -/

/-- Synthesize the universe level of a type or term. -/
/- NOTE(2025-07-02): levels can be synthesized
without using any of the level annotations.
Furthermore, the correctness proof `eq_synthLvl` needs zero metatheory.
Does this imply we could omit level annotations from the syntax?
In the interpretation function, we'd invoke `synthLvl.go` on `ExtSeq`.  -/
/- noncomputable -/ def synthLvl (Γ : Ctx) (e : Expr) : Nat :=
  go (Γ.map (·.2)) e
where
  go (Γ : List Nat) : Expr → Nat
  | .bvar i => Γ[i]? |>.getD default
  | .pi _ _ A B | .sigma _ _ A B =>
    let l := go Γ A
    max l (go (l :: Γ) B)
  | .lam _ _ A b =>
    let l := go Γ A
    max l (go (l :: Γ) b)
  | .app _ _ B _ a =>
    let l := go Γ a
    go (l :: Γ) B
  | .pair _ _ _ t u => max (go Γ t) (go Γ u)
  | .fst _ _ A _ _ => go Γ A
  | .snd _ _ A B _ =>
    let l := go Γ A
    go (l :: Γ) B
  | .univ l => l + 1
  | .el a => go Γ a - 1
  | .code A => go Γ A + 1

theorem eq_synthLvl :
    (∀ {Γ l A}, Γ ⊢[l] A → l = synthLvl Γ A) ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A → l = synthLvl Γ t) := by
  mutual_induction WfTp
  all_goals intros; try exact True.intro
  case bvar lk _  => simp [synthLvl, synthLvl.go, lk.lt_length, lk.lvl_eq]
  all_goals grind [synthLvl, synthLvl.go]

theorem WfTp.lvl_eq_synthLvl {Γ A l} : Γ ⊢[l] A → l = synthLvl Γ A :=
  fun A => _root_.eq_synthLvl.1 A

theorem WfTm.lvl_eq_synthLvl {Γ A t l} : Γ ⊢[l] t : A → l = synthLvl Γ t :=
  fun t => _root_.eq_synthLvl.2 t

/-- Synthesize the type of a term.

This function is marked `noncomputable`
because it is not supposed to be executed;
it is only defined for mathematical modelling,
in particular to prove unique typing. -/
-- FIXME: not actually marked `noncomputable`; we compute it in the evaluator.
/- noncomputable -/ def synthTp (Γ : Ctx) : Expr → Expr
  | .bvar 0 => Γ[0]? |>.getD default |>.1.subst Expr.wk
  | .bvar (i+1) => synthTp (Γ.drop 1) (.bvar i) |>.subst Expr.wk
  | .lam l l' A b => .pi l l' A (synthTp ((A, l) :: Γ) b)
  | .app _ _ B _ a => B.subst a.toSb
  | .pair l l' B t _ => .sigma l l' (synthTp Γ t) B
  | .fst _ _ A _ _ => A
  | .snd l l' A B p => B.subst (Expr.fst l l' A B p).toSb
  | .code A => .univ (synthLvl Γ A)
  | _ => default

attribute [local grind] synthTp EqTp.symm_tp EqTp.trans_tp EqTp.refl_tp in
theorem WfTm.tp_eq_synthTp : ∀ {Γ l A t}, Γ ⊢[l] t : A → Γ ⊢[l] A ≡ synthTp Γ t := by
  mutual_induction WfTm
  all_goals intros; try exact True.intro
  case bvar Γ lk _ =>
    induction lk
    . simp only [synthTp, List.getElem?_cons_zero, Option.getD_some]
      apply EqTp.refl_tp
      exact Γ.inv_snoc.subst (WfSb.wk Γ.inv_snoc)
    . rename_i ih
      simp only [synthTp, List.drop_succ_cons, List.drop_zero]
      exact ih Γ.inv_snoc.wf_ctx |>.subst (WfSb.wk Γ.inv_snoc)
  case lam' => grind [EqTp.cong_pi]
  case app' => grind [WfTp.subst, WfSb.toSb]
  case pair' => grind [EqTp.cong_sigma]
  case fst' => grind
  case snd' => grind [WfTp.subst, WfSb.toSb, WfTm.fst]
  case code => grind [WfTp.lvl_eq_synthLvl, WfTp.univ, WfTp.wf_ctx]
  case conv => grind

theorem WfTm.with_synthTp {Γ l A t} : Γ ⊢[l] t : A → Γ ⊢[l] t : synthTp Γ t :=
  fun t => t.conv t.tp_eq_synthTp

/-! ## Unique typing -/

/-- A term's type is unique up to conversion. -/
theorem WfTm.uniq_tp {Γ A B t l} : Γ ⊢[l] t : A → Γ ⊢[l] t : B → Γ ⊢[l] A ≡ B :=
  fun tA tB => tA.tp_eq_synthTp.trans_tp tB.tp_eq_synthTp.symm_tp
