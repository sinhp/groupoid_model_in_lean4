import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Category.Cat.Limit

import GroupoidModel.RepMap.Lift
import GroupoidModel.Grothendieck.Groupoidal.IsPullback
import GroupoidModel.CwRGroupoids.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory Limits Functor.Groupoidal RepMap Universe

namespace GroupoidModel

open U

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that `Ty` and `Tm` are representables,
  but since representables are `Ctx`-large,
  its representable fibers can be larger (in terms of universe levels) than itself.
-/
@[simps] def U : Universe repMap where
  Ty := Ty.{v}
  Tm := Tm.{v}
  tp := tp
  ext A := ext A
  disp A := disp A
  var A := var A
  disp_pullback A := (GroupoidModel.IsPullback.disp_pullback A).flip
  tp_representable := sorry

namespace U

open MonoidalCategory

def asSmallClosedType : (tensorUnit _ : Ctx) ⟶ Ty.{v+1, max u (v+2)} :=
  toCoreAsSmallEquiv.symm ((Functor.const _).obj
    (Grpd.of (Core (AsSmall.{v+1} Grpd.{v,v}))))

def isoExtAsSmallClosedTypeHom :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ ∫(toCoreAsSmallEquiv (asSmallClosedType.{v, max u (v + 2)})) where
  obj X := objMk ⟨⟨⟩⟩ ⟨AsSmall.up.obj.{_,_,v+1} (AsSmall.down.obj X.of)⟩
  map {X Y} F := homMk (𝟙 _) ⟨{
    hom := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map F.iso.hom)
    inv := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map (F.iso.inv))
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl }⟩

def isoExtAsSmallClosedTypeInv :
    ∫(toCoreAsSmallEquiv (asSmallClosedType.{v, max u (v + 2)})) ⥤
    Core (AsSmall.{max u (v+2)} Grpd.{v,v}) where
  obj X := ⟨AsSmall.up.obj (AsSmall.down.obj.{_,_,v+1} X.fiber.of)⟩
  map {X Y} F := ⟨{
    hom := AsSmall.up.map.{_,_,max u (v+2)}
      (AsSmall.down.map F.fiber.iso.hom)
    inv := AsSmall.up.map.{_,_,max u (v+2)}
      (AsSmall.down.map F.fiber.iso.inv)
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl }⟩

def isoExtAsSmallClosedType :
    Ty.{v,max u (v+2)}
    ≅ U.{v+1,max u (v+2)}.ext U.asSmallClosedType.{v, max u (v+2)} where
  hom := (Grpd.homOf isoExtAsSmallClosedTypeHom.{v,u})
  inv := (Grpd.homOf isoExtAsSmallClosedTypeInv.{v,u})
  hom_inv_id := rfl
  inv_hom_id := rfl

end U

def uHomSeqObjs (i : Nat) (h : i < 4) : Universe repMap.{4} :=
  match i with
  | 0 => U.{0,4}
  | 1 => U.{1,4}
  | 2 => U.{2,4}
  | 3 => U.{3,4}
  | (n+4) => by omega

def lift : Lift U.{v, max u (v+2)} U.{v+1, max u (v+2)} :=
    @Lift.ofTyIsoExt _ _ _ _ _ _ _
    { mapTy := U.liftTy.{v,max u (v+2)}
      mapTm := U.liftTm
      pb := IsPullback.liftTm_isPullback }
    asSmallClosedType
    isoExtAsSmallClosedType.{v,u}

def liftSeqHomSucc' (i : Nat) (h : i < 3) :
    Lift (uHomSeqObjs i (by omega)) (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => lift.{0,4}
  | 1 => lift.{1,4}
  | 2 => lift.{2,4}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def liftSeq : LiftSeq repMap.{4} where
  length := 3
  objs := uHomSeqObjs
  homSucc' := liftSeqHomSucc'

open CategoryTheory Opposite

section

variable {Γ : Ctx} {C : Type (v+1)} [Category.{v} C] {Δ : Ctx} (σ : Δ ⟶ Γ)

namespace U

theorem substWk_eq (A : Γ ⟶ U.{v}.Ty) (σA eq) : U.substWk A σ σA eq =
    map (eqToHom (by subst eq; rfl)) ⋙ pre (toCoreAsSmallEquiv A) σ := by
  apply (U.disp_pullback A).hom_ext
  · rw [substWk_disp]
    simp [Grpd.comp_eq_comp, Functor.assoc]
    erw [pre_comp_forget, ← Functor.assoc, map_comp_forget]
  · rw [substWk_var]
    simp [var, Grpd.comp_eq_comp]
    rw [← toCoreAsSmallEquiv_symm_apply_comp_left, Functor.assoc, pre_toPGrpd,
      map_eqToHom_toPGrpd]

@[simp] theorem sec_eq {Γ : Ctx} (α : Γ ⟶ U.{v}.Tm) :
    U.sec _ α rfl = sec _ (toCoreAsSmallEquiv α) rfl := by
  apply (U.disp_pullback _).hom_ext
  . rw [sec_disp]
    rfl
  . erw [Universe.sec_var, U_var, var, Grpd.comp_eq_comp,
      ← toCoreAsSmallEquiv_symm_apply_comp_left, Equiv.eq_symm_apply, sec_toPGrpd]
    rfl

namespace PtpEquiv

variable (AB : Γ ⟶ U.{v}.Ptp.obj (Ctx.coreAsSmall C))

/--
A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.fst` is the `A` in this pair.
-/
def fst : Γ ⥤ Grpd.{v,v} :=
  toCoreAsSmallEquiv (RepMap.Universe.PtpEquiv.fst U AB)

/--
A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd : ∫(fst AB) ⥤ C :=
  toCoreAsSmallEquiv (RepMap.Universe.PtpEquiv.snd U AB)

nonrec theorem fst_comp_left : fst (σ ≫ AB) = σ ⋙ fst AB := by
  dsimp only [fst]
  rw [PtpEquiv.fst_comp_left, ← toCoreAsSmallEquiv_apply_comp_left, Grpd.comp_eq_comp]

theorem fst_comp_right {D : Type (v + 1)} [Category.{v, v + 1} D] (F : C ⥤ D) :
    fst (AB ≫ U.Ptp.map (Ctx.coreAsSmallFunctor F)) = fst AB := by
  dsimp only [fst]
  rw [RepMap.Universe.PtpEquiv.fst_comp_right]

nonrec theorem snd_comp_left : snd (σ ≫ AB) =
    map (eqToHom (fst_comp_left σ AB)) ⋙ pre _ σ ⋙ snd AB := by
  dsimp only [snd]
  simp only [eqToHom_refl, map_id_eq, Cat.of_α, Functor.simpIdComp]
  erw [PtpEquiv.snd_comp_left U (snd._proof_1 AB), toCoreAsSmallEquiv_apply_comp_left]
  · rw [substWk_eq]
    · congr 1
      simp [fst, map_id_eq]
    · rfl

/--
A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
    Γ ⟶ U.{v}.Ptp.obj (Ctx.coreAsSmall C) :=
  Universe.PtpEquiv.mk U (toCoreAsSmallEquiv.symm A) (toCoreAsSmallEquiv.symm B)

theorem hext (AB1 AB2 : Γ ⟶ U.{v}.Ptp.obj Ty.{v}) (hfst : fst AB1 = fst AB2)
    (hsnd : HEq (snd AB1) (snd AB2)) : AB1 = AB2 := by
  have hfst' : Universe.PtpEquiv.fst U AB1 = Universe.PtpEquiv.fst U AB2 := by
    dsimp [fst] at hfst
    aesop
  apply Universe.PtpEquiv.ext U (Universe.PtpEquiv.fst U AB1) ?_ hfst' ?_
  · simp
  · dsimp only [snd] at hsnd
    apply toCoreAsSmallEquiv.injective
    rw! [hsnd]
    conv => right; rw! (castMode := .all) [hfst']
    simp [← heq_eq_eq]
    rfl

lemma fst_mk (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
    fst (mk A B) = A := by
  simp [fst, mk, Universe.PtpEquiv.fst_mk]

lemma Grpd.eqToHom_comp_heq {A B : Grpd} {C : Type*} [Category C]
    (h : A = B) (F : B ⥤ C) : eqToHom h ⋙ F ≍ F := by
  subst h
  simp [Grpd.id_eq_id, Functor.id_comp]

lemma snd_mk (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
    snd (mk A B) = map (eqToHom (fst_mk A B)) ⋙ B := by
  dsimp only [snd, mk]
  rw! (castMode := .all) [Universe.PtpEquiv.fst_mk, Universe.PtpEquiv.snd_mk]
  simp only [U_ext, U_Ty, Equiv.apply_eq_iff_eq_symm_apply, toCoreAsSmallEquiv_symm_apply_comp_left]
  simp only [← heq_eq_eq, eqRec_heq_iff_heq, ← eqToHom_eq_homOf_map (fst_mk A B)]
  symm
  apply Grpd.eqToHom_comp_heq

lemma snd_mk_heq (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
    snd (mk A B) ≍ B := by
  simp [snd_mk, map_eqToHom_comp_heq]

end PtpEquiv

def compDom := U.{v}.uvPolyTp.compDom U.{v}.uvPolyTp

def comp : compDom.{v} ⟶ U.{v}.Ptp.obj Ty.{v} :=
  (U.{v}.uvPolyTp.comp U.{v}.uvPolyTp).p

namespace compDom

variable (ab : (Γ) ⟶ compDom.{v})

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : (Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `fst : Γ ⥤ PGrpd`
is `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst : Γ ⥤ PGrpd.{v,v} :=
  toCoreAsSmallEquiv (Universe.compDomEquiv.fst ab)

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : (Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `dependent : Γ ⥤ Grpd`
is `B : A → Type` in `(a : A) × (b : B a)`.
-/
def dependent : ∫(fst ab ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v} :=
  toCoreAsSmallEquiv (Universe.compDomEquiv.dependent ab)

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : (Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `snd : Γ ⥤ PGrpd`
is `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd : Γ ⥤ PGrpd.{v,v} :=
  toCoreAsSmallEquiv (Universe.compDomEquiv.snd ab)

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : (Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`.
The equation `snd_forgetToGrpd` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_forgetToGrpd : snd ab ⋙ PGrpd.forgetToGrpd = sec _ (fst ab) rfl ⋙ (dependent ab) := by
  erw [← toCoreAsSmallEquiv_apply_comp_right, ← Grpd.comp_eq_comp,
    Universe.compDomEquiv.snd_tp ab, sec_eq]
  rfl

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Γ ⥤ PGrpd.{v,v}) (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v})
    (β : Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : (Γ) ⟶ compDom.{v} :=
  RepMap.Universe.compDomEquiv.mk (toCoreAsSmallEquiv.symm α) rfl
    (toCoreAsSmallEquiv.symm B) (toCoreAsSmallEquiv.symm β) (by
      simp only [U_Ty, U_Tm, U_tp, tp, Grpd.comp_eq_comp, U_ext]
      erw [← toCoreAsSmallEquiv_symm_apply_comp_right, h,
        ← toCoreAsSmallEquiv_symm_apply_comp_left, sec_eq]
      rfl
      )

theorem fst_forgetToGrpd : fst ab ⋙ PGrpd.forgetToGrpd =
    U.PtpEquiv.fst (ab ≫ comp.{v}) := by
  erw [U.PtpEquiv.fst, ← compDomEquiv.fst_tp ab, ← toCoreAsSmallEquiv_apply_comp_right]
  rfl

theorem dependent_eq : dependent ab =
    map (eqToHom (fst_forgetToGrpd ab)) ⋙ U.PtpEquiv.snd (ab ≫ comp.{v}) := by
  -- conv => rhs; rw! (castMode := .all) [← fst_forgetToGrpd]
  -- erw [eqToHom_refl, map_id_eq, Functor.id_comp]
  simp [dependent, compDomEquiv.dependent]

  -- simp only [← heq_eq_eq, heq_eqRec_iff_heq, dependent, compDomEquiv.dependent, PtpEquiv.snd, comp]
  -- rw! (castMode := .all) [compDomEquiv.fst_tp]
  -- simp

  sorry

theorem dependent_heq : HEq (dependent ab) (U.PtpEquiv.snd (ab ≫ comp.{v})) := by
  rw [dependent_eq]
  apply Functor.precomp_heq_of_heq_id
  · rw [fst_forgetToGrpd]
  · rw [fst_forgetToGrpd]
  · apply map_eqToHom_heq_id_cod

theorem fst_naturality : fst ((σ) ≫ ab) = σ ⋙ fst ab := by
  dsimp only [fst]
  rw [← RepMap.Universe.compDomEquiv.comp_fst, Grpd.comp_eq_comp,
    toCoreAsSmallEquiv_apply_comp_left]

theorem dependent_naturality : dependent ((σ) ≫ ab) =
    map (eqToHom (by rw [fst_naturality, Functor.assoc]))
    ⋙ pre _ σ ⋙ dependent ab := by
  rw [dependent, dependent,
    ← RepMap.Universe.compDomEquiv.comp_dependent (eq1 := rfl)
      (eq2 := by simp [← compDomEquiv.comp_fst]),
    substWk_eq]
  rw! [Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
  rfl

theorem snd_naturality : snd (σ ≫ ab) = σ ⋙ snd ab := by
  dsimp only [snd]
  rw [← RepMap.Universe.compDomEquiv.comp_snd, Grpd.comp_eq_comp,
    toCoreAsSmallEquiv_apply_comp_left]

/-- First component of the computation rule for `mk`. -/
theorem fst_mk (α : Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : fst (mk α B β h) = α := by
  simp [fst, mk, RepMap.Universe.compDomEquiv.fst_mk]

/-- Second component of the computation rule for `mk`. -/
theorem dependent_mk (α : Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : dependent (mk α B β h) = map (eqToHom (by rw [fst_mk])) ⋙ B := by
  sorry

/-- Second component of the computation rule for `mk`. -/
theorem snd_mk (α : Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : snd (mk α B β h) = β := by
  dsimp [snd, mk]
  rw [RepMap.Universe.compDomEquiv.snd_mk]
  simp

theorem U.compDom.hext (ab1 ab2 : (Γ) ⟶ U.compDom.{v}) (hfst : fst ab1 = fst ab2)
    (hdependent : HEq (dependent ab1) (dependent ab2)) (hsnd : snd ab1 = snd ab2) : ab1 = ab2 := by
  sorry

end compDom

end U
end

end GroupoidModel

end
