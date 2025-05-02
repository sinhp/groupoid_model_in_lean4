import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal
import GroupoidModel.Groupoids.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory
  Limits NaturalModelBase CategoryTheory.Functor
  GroupoidModel.IsPullback.SmallBase
  GroupoidModel.IsPullback.SmallUHom
  Grothendieck.Groupoidal


namespace GroupoidModel

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that `Ty` and `Tm` are representables,
  but since representables are `max u (v+1)`-large,
  its representable fibers can be larger (in terms of universe levels) than itself.
-/
@[simps] def smallU : NaturalModelBase Ctx.{max u (v+1)} where
  Ty := y(U.{v})
  Tm := y(E)
  tp := ym(π)
  ext A := Ctx.ofGrpd.obj (Grpd.of ∫(yonedaCategoryEquiv A))
  disp A := Ctx.ofGrpd.map forget
  var A := yonedaCategoryEquiv.symm (toPGrpd _)
  disp_pullback A := by
    convert isPullback_yonedaDisp_yonedaπ (Yoneda.fullyFaithful.homEquiv.symm A)
    simp

namespace U

open MonoidalCategory

def asSmallClosedType' : tensorUnit
    ⟶ U.{v+1, max u (v+2)} :=
  toCoreAsSmallEquiv.symm ((Functor.const _).obj
    (Grpd.of (Core (AsSmall.{v+1} Grpd.{v,v}))))

def asSmallClosedType : y(tensorUnit)
    ⟶ smallU.{v+1, max u (v+2)}.Ty :=
  ym(U.asSmallClosedType')

def isoGrpd : Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ Grpd.{v,v} := Core.inclusion _ ⋙ AsSmall.down

def isoExtAsSmallClosedTypeHom :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ ∫(classifier (asSmallClosedType'.{v, max u (v + 2)})) where
  obj X := ⟨ ⟨⟨⟩⟩ , AsSmall.up.obj.{_,_,v+1} (AsSmall.down.obj X) ⟩
  map {X Y} F := ⟨ (CategoryStruct.id _) , {
    hom := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map F.hom)
    inv := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map (F.inv))
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl } ⟩

def isoExtAsSmallClosedTypeInv :
    ∫(classifier (asSmallClosedType'.{v, max u (v + 2)})) ⥤
    Core (AsSmall.{max u (v+2)} Grpd.{v,v}) where
  obj X := AsSmall.up.obj (AsSmall.down.obj.{_,_,v+1} X.fiber)
  map {X Y} F := {
    hom := AsSmall.up.map.{_,_,max u (v+2)}
      (AsSmall.down.map F.fiber.hom)
    inv := AsSmall.up.map.{_,_,max u (v+2)}
      (AsSmall.down.map F.fiber.inv)
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl }

def isoExtAsSmallClosedType :
    U.{v,max u (v+2)}
    ≅ smallU.{v+1,max u (v+2)}.ext U.asSmallClosedType.{v, max u (v+2)} where
  hom := Ctx.ofGrpd.map (Grpd.homOf isoExtAsSmallClosedTypeHom.{v,u})
  inv := Ctx.ofGrpd.map (Grpd.homOf isoExtAsSmallClosedTypeInv.{v,u})
  hom_inv_id := rfl
  inv_hom_id := rfl

end U

def uHomSeqObjs (i : Nat) (h : i < 4) : NaturalModelBase Ctx.{4} :=
  match i with
  | 0 => smallU.{0,4}
  | 1 => smallU.{1,4}
  | 2 => smallU.{2,4}
  | 3 => smallU.{3,4}
  | (n+4) => by omega

def smallUHom : UHom smallU.{v, max u (v+2)} smallU.{v+1, max u (v+2)} :=
    @UHom.ofTyIsoExt _ _ _ _ _
    { mapTy := ym(U.toU.{v,max u (v+2)})
      mapTm := ym(U.toE)
      pb := isPullback_yπ_yπ }
    U.asSmallClosedType
    (Functor.mapIso yoneda U.isoExtAsSmallClosedType.{v,u})

def uHomSeqHomSucc' (i : Nat) (h : i < 3) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => smallUHom.{0,4}
  | 1 => smallUHom.{1,4}
  | 2 => smallUHom.{2,4}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def uHomSeq : NaturalModelBase.UHomSeq Ctx.{4} where
  length := 3
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

open CategoryTheory NaturalModelBase Opposite

section

variable {Γ : Ctx} {C : Type (v+1)} [Category.{v} C] {Δ : Ctx} (σ : Δ ⟶ Γ)

-- TODO rename
def smallUPTpEquiv :
    (y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v}) × (∫(A) ⥤ C) :=
  smallU.Ptp_equiv.trans (
  Equiv.sigmaCongr
    yonedaCategoryEquiv
    (fun _ => yonedaCategoryEquiv))

theorem smallUPTpEquiv_naturality_left
    (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C)) : smallUPTpEquiv (ym(σ) ≫ AB) =
    ⟨ Ctx.toGrpd.map σ ⋙ (smallUPTpEquiv AB).fst,
    pre _ (Ctx.toGrpd.map σ) ⋙ (smallUPTpEquiv AB).snd ⟩ := by
  dsimp [smallUPTpEquiv]
  erw [Ptp_equiv_naturality_left]
  simp [Equiv.sigmaCongr]
  constructor
  · erw [← yonedaCategoryEquiv_naturality_left]
    rfl
  · dsimp
    sorry

end

@[simp] theorem smallU_sec {Γ : Ctx.{max u (v+1)}} (α : y(Γ) ⟶ smallU.{v}.Tm) :
    smallU.sec _ α rfl = Ctx.ofGrpd.map (sec _ (yonedaCategoryEquiv α) rfl) := by
  apply Yoneda.fullyFaithful.map_injective
  apply (smallU.disp_pullback _).hom_ext
  . rw [NaturalModelBase.sec_var, smallU_var]
    convert_to α = ym(Ctx.ofGrpd.map $ Grpd.homOf (sec (yonedaCategoryEquiv (α ≫ ym(Ctx.homOfFunctor PGrpd.forgetToGrpd))) (yonedaCategoryEquiv α) _)) ≫ yonedaCategoryEquiv.symm (_)
    dsimp [toCoreAsSmallEquiv, Ctx.homGrpdEquivFunctor, functorToAsSmallEquiv,
      Core.functorToCoreEquiv]
    rw [← Functor.map_comp, ← Functor.map_comp, Grpd.comp_eq_comp, ← Core.functorToCore_naturality_left, ← Functor.assoc, sec_toPGrpd]
    simp [yonedaCategoryEquiv, toCoreAsSmallEquiv, functorToAsSmallEquiv,
      Core.functorToCoreEquiv, Core.forgetFunctorToCore, Ctx.homGrpdEquivFunctor,
      -AsSmall.down_map, Functor.assoc, Functor.comp_id,
      Core.functorToCore_naturality_left, Core.functorToCore_inclusion_apply]
  . rw [← Functor.map_comp, sec_disp]
    rfl

-- TODO shorten name
/-- A specialization of the universal property of `UvPoly.compDom`
  to the natural model `smallU`.
  This consists of a pair of dependent types
  `A = α ⋙ forgetToGrpd` and `B`,
  `a : A` captured by `α`,
  and `b : B[a / x] = β ⋙ forgetToGrpd` caputred by `β`.
  -/
def smallUUvPolyTpCompDomEquiv {Γ : Ctx.{max u (v+1)}} :
    (y(Γ) ⟶ smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp)
    ≃ (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    × (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B :=
  (smallU.uvPolyTpCompDomEquiv smallU Γ).trans
  (Equiv.sigmaCongr
    yonedaCategoryEquiv $
    fun α => Equiv.sigmaCongr
      yonedaCategoryEquiv $
      fun B => Equiv.psigmaCongrProp
        yonedaCategoryEquiv $
        fun β => by
    convert (yonedaCategoryEquiv.apply_eq_iff_eq).symm
    rw [yonedaCategoryEquiv_naturality_left, smallU_sec]
    rfl)

theorem smallUUvPolyTpCompDomEquiv_apply_fst {Γ : Ctx.{max u (v+1)}}
    (ab : y(Γ) ⟶ smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp) :
    (smallUUvPolyTpCompDomEquiv ab).fst ⋙ PGrpd.forgetToGrpd
    = (smallUPTpEquiv (ab ≫ (
      smallU.{v}.uvPolyTp.comp smallU.{v}.uvPolyTp).p)).fst := by
  dsimp only [smallUPTpEquiv, Equiv.trans_apply, Equiv.sigmaCongrLeft]
  rw [Equiv.sigmaCongr_apply_fst]
  convert congr_arg yonedaCategoryEquiv.toFun
    (@uvPolyTpCompDomEquiv_apply_fst Ctx.{max u (v+1)} _ smallU.{v} smallU.{v} Γ ab)

end GroupoidModel

end
