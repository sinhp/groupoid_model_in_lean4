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
open CategoryTheory Grothendieck
  Limits NaturalModelBase CategoryTheory.Functor
  GroupoidModel.IsPullback.Base
  GroupoidModel.IsPullback.LargeUHom
  GroupoidModel.IsPullback.SmallBase
  GroupoidModel.IsPullback.SmallUHom


namespace GroupoidModel

-- TODO link to this in blueprint
/-- The natural model that acts as the ambient
  model in which the other universes live.
  Note that unlike the other universes this is *not* representable,
  but enjoys having representable fibers that land in itself.
-/
@[simps] def base : NaturalModelBase Ctx.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext := ext
  disp := disp
  var := var
  disp_pullback := isPullback_yonedaDisp_tp

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v+1)`-large,
  its representable fibers can be larger than itself.
-/
def smallU : NaturalModelBase Ctx.{max u (v+1)} where
  Ty := y(U.{v})
  Tm := y(E)
  tp := ym(π)
  ext A := U.ext (yoneda.preimage A)
  disp A := U.disp (yoneda.preimage A)
  var A := ym(U.var (yoneda.preimage A))
  disp_pullback A := by
    convert isPullback_yonedaDisp_yonedaπ (yoneda.preimage A)
    rw [Functor.map_preimage]

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
    ⥤ Groupoidal (classifier (asSmallClosedType'.{v, max u (v + 2)})) where
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
    Groupoidal
      (classifier (asSmallClosedType'.{v, max u (v + 2)})) ⥤
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
    ≫ eqToHom (by simp only [smallU, asSmallClosedType, preimage_map])
  inv := eqToHom (by simp only [smallU, asSmallClosedType, preimage_map])
    ≫ Ctx.ofGrpd.map (Grpd.homOf isoExtAsSmallClosedTypeInv.{v,u})
  hom_inv_id := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl]
    rfl
  inv_hom_id := by
    simp only [Category.assoc, eqToHom_comp_iff, Category.comp_id]
    simp only [← Category.assoc, comp_eqToHom_iff, eqToHom_trans]
    rfl

def asClosedType :
    y(tensorUnit) ⟶ base.Ty :=
  yonedaCatEquiv.invFun ((CategoryTheory.Functor.const _).obj
    (Grpd.of U'.{v,u}))

def isoExtAsClosedTypeFun : Core (AsSmall Grpd)
    ⥤ Groupoidal (yonedaCatEquiv U.asClosedType.{v,u}) where
  obj X := ⟨ ⟨⟨⟩⟩ , X ⟩
  map {X Y} F := ⟨ id _ , F ⟩

def isoExtAsClosedTypeInv : Groupoidal (yonedaCatEquiv U.asClosedType.{v,u})
    ⥤ Core (AsSmall Grpd) where
  obj X := X.fiber
  map {X Y} F := F.fiber

def isoExtAsClosedType :
    U.{v,u} ≅ base.ext asClosedType.{v,u} where
  hom := Ctx.ofGrpd.map isoExtAsClosedTypeFun
  inv := Ctx.ofGrpd.map isoExtAsClosedTypeInv

end U

def largeUHom : UHom smallU.{v,u} base :=
  UHom.ofTyIsoExt
    { mapTy := toTy
      mapTm := toTm
      pb := isPullback_yπ_tp }
    (Functor.mapIso yoneda U.isoExtAsClosedType)

def uHomSeqObjs (i : Nat) (h : i < 4) : NaturalModelBase Ctx.{3} :=
  match i with
  | 0 => smallU.{0,3}
  | 1 => smallU.{1,3}
  | 2 => smallU.{2,3}
  | 3 => base.{3}
  | (n+4) => by omega

def smallUHom : UHom smallU.{v, max u (v+2)} smallU.{v+1, max u (v+2)} :=
    @UHom.ofTyIsoExt _ _ _ _ _
    { mapTy := ym(toU.{v,max u (v+2)})
      mapTm := ym(toE)
      pb := isPullback_yπ_yπ }
    U.asSmallClosedType
    (Functor.mapIso yoneda U.isoExtAsSmallClosedType.{v,u})

def uHomSeqHomSucc' (i : Nat) (h : i < 3) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => smallUHom.{0,3}
  | 1 => smallUHom.{1,3}
  | 2 => largeUHom.{2,3}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def uHomSeq : NaturalModelBase.UHomSeq Ctx.{3} where
  length := 3
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

open CategoryTheory NaturalModelBase Opposite Grothendieck

/-- A specialization of the polynomial universal property to the natural model `base`
  The polynomial functor on `tp` taken at `yonedaCat.obj C`
  `P_tp(yonedaCat C)` takes a groupoid `Γ`
  to a pair of functors `A` and `B`

      B
   C ⇇ Groupoidal A   ⥤   PGrpd
            ⇊               ⇊
            Γ          ⥤   Grpd
                       A
As a special case, if `C` is taken to be `Grpd`,
then this is how `P_tp(Ty)` classifies dependent pairs.
-/
def baseUvPolyTpEquiv {Γ : Ctx.{u}} {C : Cat.{u,u+1}} :
    (base.Ptp.obj (yonedaCat.obj C)).obj (op Γ)
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}) × (Groupoidal A ⥤ C) :=
  yonedaEquiv.symm.trans (
  base.uvPolyTpEquiv.trans (
  Equiv.sigmaCongr
    yonedaCatEquiv
    (fun _ => yonedaCatEquiv)))

@[simp] theorem base_sec {Γ : Ctx.{u}} (α : y(Γ) ⟶ base.Tm) :
    base.sec α = ym(Ctx.ofGrpd.map (Groupoidal.sec (yonedaCatEquiv α))) :=
  (base.disp_pullback (α ≫ base.tp)).hom_ext
  (by
    rw [NaturalModelBase.sec_var]
    dsimp only [base_var, var]
    convert_to α =
    yonedaCatEquiv.symm
      (Groupoidal.sec (yonedaCatEquiv α) ⋙ Groupoidal.toPGrpd (yonedaCatEquiv α ⋙ Cat.homOf PGrpd.forgetToGrpd))
    rw [Groupoidal.sec_toPGrpd _, yonedaCatEquiv.eq_symm_apply])
  (by rw [NaturalModelBase.sec_disp]; rfl)

/-- A specialization of the universal property of `UvPoly.compDom`
  to the natural model `base`.
  This consists of a pair of dependent types
  `A = α ⋙ forgetToGrpd` and `B`,
  `a : A` captured by `α`,
  and `b : B[a / x] = β ⋙ forgetToGrpd` caputred by `β`.
  -/
def baseUvPolyTpCompDomEquiv {Γ : Ctx.{u}} :
    (base.uvPolyTp.compDom base.uvPolyTp).obj (op Γ)
    ≃ (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' β ⋙ PGrpd.forgetToGrpd = Groupoidal.sec α ⋙ B :=
  yonedaEquiv.symm.trans (
  (base.uvPolyTpCompDomEquiv Γ).trans
  (Equiv.sigmaCongr
    yonedaCatEquiv $
    fun α => Equiv.sigmaCongr
      yonedaCatEquiv $
      fun B => Equiv.psigmaCongrProp
        yonedaCatEquiv $
        fun β => by
  convert_to _ ↔ yonedaCatEquiv (β ≫ yonedaCat.map PGrpd.forgetToGrpd)
    = Ctx.toGrpd.map (Ctx.ofGrpd.map
      (Groupoidal.sec (yonedaCatEquiv α))) ⋙ yonedaCatEquiv B
  convert_to _ ↔ β ≫ yonedaCat.map PGrpd.forgetToGrpd =
    yoneda.map (Ctx.ofGrpd.map (Groupoidal.sec (yonedaCatEquiv α))) ≫ B
  · simp only [yonedaCatEquiv_naturality_left, ← yonedaCatEquiv.apply_eq_iff_eq]
  simp [yonedaCatEquiv.apply_eq_iff_eq]))

def baseUvPolyTpCompDomEquiv' {Γ : Ctx.{u}} :
    (base.uvPolyTp.compDom base.uvPolyTp).obj (op Γ)
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u})
    × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : Groupoidal A ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = Groupoidal.sec α ⋙ Groupoidal.map (eqToHom h) ⋙ B :=
  baseUvPolyTpCompDomEquiv.trans $ {
    toFun := fun ⟨α,B,β,h⟩ => ⟨α ⋙ PGrpd.forgetToGrpd, α, B, β, rfl, by
      rw [h, eqToHom_refl, Groupoidal.map_id_eq]
      rfl⟩
    invFun := fun ⟨A,α,B,β,hA,hB⟩ => ⟨α, Groupoidal.map (eqToHom hA) ⋙ B, β, by rw [hB] ⟩
    left_inv := by
      intro ⟨α,B,β,h⟩
      dsimp
      congr!
      simp [Groupoidal.map_id_eq, Functor.id_comp]
    right_inv := by
      intro ⟨A,α,B,β,h1,h2⟩
      subst h1
      congr!
      · simp [eqToHom_refl, Groupoidal.map_id_eq, Functor.id_comp]
    }

def baseTmEquiv {Γ : Ctx} :
    (A : y(Γ) ⟶ base.Ty) × (α : y(Γ) ⟶ base.Tm) ×' (α ≫ base.tp = A) ≃
    (A : Ctx.toGrpd.obj Γ ⥤ Grpd) × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd)
      ×' (α ⋙ PGrpd.forgetToGrpd = A) :=
  Equiv.sigmaCongr yonedaCatEquiv $ fun A =>
    Equiv.psigmaCongrProp yonedaCatEquiv $ fun α => (by
      simp only [base_tp, tp]
      convert_to _ ↔ yonedaCatEquiv
        (α ≫ yonedaCat.map (Cat.homOf PGrpd.forgetToGrpd)) = _
      simp)

end GroupoidModel

end
