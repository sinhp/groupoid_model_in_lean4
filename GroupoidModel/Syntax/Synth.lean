import GroupoidModel.Syntax.Inversion
import GroupoidModel.Syntax.GCongr

variable {χ : Type*} {E : Axioms χ} {Γ : Ctx χ}
  {A A' t : Expr χ} {i l l' : Nat}

/-! ## Lookup well-formedness -/

namespace Lookup

theorem lt_length : Lookup Γ i A l → i < Γ.length := by
  intro lk; induction lk <;> (dsimp; omega)

theorem lvl_eq (lk : Lookup Γ i A l) : l = (Γ[i]'lk.lt_length).2 := by
  induction lk <;> grind

theorem tp_uniq (lk : Lookup Γ i A l) (lk' : Lookup Γ i A' l) : A = A' := by
  induction lk generalizing A' <;> grind [cases Lookup]

theorem of_lt_length : i < Γ.length → ∃ A l, Lookup Γ i A l := by
  intro lt
  induction Γ generalizing i
  · cases lt
  · cases i
    · exact ⟨_, _, Lookup.zero ..⟩
    · rename_i ih _
      have ⟨A, l, h⟩ := ih <| Nat.succ_lt_succ_iff.mp lt
      exact ⟨A.subst Expr.wk, l, Lookup.succ _ _ h⟩

end Lookup

/-! ## Level synthesis and uniqueness -/

/-- Synthesize the universe level of a type or term. -/
/- NOTE(2025-07-02): levels can be synthesized
without using any of the level annotations.
Furthermore, the correctness proof `eq_synthLvl` needs zero metatheory.
Does this imply we could omit level annotations from the syntax?
In the interpretation function, we'd invoke `synthLvl.go` on `ExtSeq`.  -/
noncomputable def synthLvl (Γ : Ctx χ) (e : Expr χ) : Nat :=
  go (Γ.map (·.2)) e
where
  go (Γ : List Nat) : Expr χ → Nat
  | .ax _ A => go Γ A
  | .bvar i => Γ[i]? |>.getD default
  | .pi _ _ A B | .sigma _ _ A B =>
    let l := go Γ A
    max l (go (l :: Γ) B)
  | .Id _ A _ _ => go Γ A
  | .lam _ _ A b =>
    let l := go Γ A
    max l (go (l :: Γ) b)
  | .app _ _ B _ a =>
    let l := go Γ a
    go (l :: Γ) B
  | .pair _ _ _ t u => max (go Γ t) (go Γ u)
  | .fst _ _ A .. => go Γ A
  | .snd _ _ A B _ =>
    let l := go Γ A
    go (l :: Γ) B
  | .refl _ t => go Γ t
  | .idRec _ _ _ _ r .. => go Γ r
  | .univ l => l + 1
  | .el a => go Γ a - 1
  | .code A => go Γ A + 1

theorem eq_synthLvl :
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A → l = synthLvl Γ A) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → l = synthLvl Γ t) := by
  mutual_induction WfTp
  all_goals intros; try exact True.intro
  case bvar lk _ => simp [synthLvl, synthLvl.go, lk.lt_length, lk.lvl_eq]
  all_goals grind [synthLvl, synthLvl.go]

theorem WfTp.lvl_eq_synthLvl : E ∣ Γ ⊢[l] A → l = synthLvl Γ A :=
  fun A => _root_.eq_synthLvl.1 A

theorem WfTm.lvl_eq_synthLvl : E ∣ Γ ⊢[l] t : A → l = synthLvl Γ t :=
  fun t => _root_.eq_synthLvl.2 t

/-- A type's universe level is unique. -/
theorem WfTp.uniq_lvl : E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l'] A → l = l' :=
  fun h h' => h.lvl_eq_synthLvl.trans h'.lvl_eq_synthLvl.symm

/-- A term's universe level is unique. -/
theorem WfTm.uniq_lvl : E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l'] t : A' → l = l' :=
  fun h h' => h.lvl_eq_synthLvl.trans h'.lvl_eq_synthLvl.symm

/-! ## Type synthesis and uniqueness -/

/-- Synthesize the type of a term.

This function is marked `noncomputable`
because it is not supposed to be executed;
it is only defined for mathematical modelling,
in particular to prove unique typing.
For executable type synthesis, see `Typechecker.Synth`. -/
noncomputable def synthTp (Γ : Ctx χ) : Expr χ → Expr χ
  | .ax _ A => A
  | .bvar 0 => Γ[0]? |>.getD default |>.1.subst Expr.wk
  | .bvar (i+1) => synthTp (Γ.drop 1) (.bvar i) |>.subst Expr.wk
  | .lam l l' A b => .pi l l' A (synthTp ((A, l) :: Γ) b)
  | .app _ _ B _ a => B.subst a.toSb
  | .pair l l' B t _ => .sigma l l' (synthTp Γ t) B
  | .fst _ _ A _ _ => A
  | .snd l l' A B p => B.subst (Expr.fst l l' A B p).toSb
  | .refl l t => .Id l (synthTp Γ t) t t
  | .idRec _ _ _ M _ u h => M.subst (.snoc u.toSb h)
  | .code A => .univ (synthLvl Γ A)
  | _ => default

attribute [local grind] synthTp EqTp.symm_tp EqTp.trans_tp EqTp.refl_tp in
theorem WfTm.tp_eq_synthTp : ∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l] A ≡ synthTp Γ t := by
  mutual_induction WfTm
  all_goals intros; try exact True.intro
  case ax A _ _ =>
    simp only [synthTp]
    apply EqTp.refl_tp A
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
  case refl' =>
    simp only [synthTp]
    gcongr <;> grind
  case idRec' C _ _ _ _ _ _ _ _ _ =>
    unfold synthTp
    apply EqTp.refl_tp <| C.subst <| WfSb.snoc (WfSb.toSb ..) ..
    all_goals (try autosubst); grind [WfTp.Id_bvar, WfTp.wf_ctx]
  case code => grind [WfTp.lvl_eq_synthLvl, WfTp.univ, WfTp.wf_ctx]
  case conv => grind

theorem WfTm.with_synthTp : E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l] t : synthTp Γ t :=
  fun t => t.conv t.tp_eq_synthTp

/-- A term's type is unique up to conversion. -/
theorem WfTm.uniq_tp : E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l'] t : A' → E ∣ Γ ⊢[l] A ≡ A' :=
  fun tA tB => tA.tp_eq_synthTp.trans_tp (tA.uniq_lvl tB ▸ tB).tp_eq_synthTp.symm_tp
