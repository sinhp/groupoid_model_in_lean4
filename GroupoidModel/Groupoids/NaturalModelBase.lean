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
  GroupoidModel.IsPullback.Base
  GroupoidModel.IsPullback.LargeUHom
  GroupoidModel.IsPullback.SmallBase
  GroupoidModel.IsPullback.SmallUHom
  Grothendieck.Groupoidal


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

def asClosedType :
    y(tensorUnit) ⟶ base.Ty :=
  yonedaCatEquiv.invFun ((CategoryTheory.Functor.const _).obj
    (Grpd.of (Core (AsSmall Grpd.{v,v}))))

def isoExtAsClosedTypeFun : Core (AsSmall Grpd)
    ⥤ ∫(yonedaCatEquiv U.asClosedType.{v,u}) where
  obj X := ⟨ ⟨⟨⟩⟩ , X ⟩
  map {X Y} F := ⟨ id _ , F ⟩

def isoExtAsClosedTypeInv : ∫(yonedaCatEquiv U.asClosedType.{v,u})
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

def smallUUvPolyTpEquiv :
    (y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v}) × (∫(A) ⥤ C) :=
  smallU.uvPolyTpEquiv.trans (
  Equiv.sigmaCongr
    yonedaCategoryEquiv
    (fun _ => yonedaCategoryEquiv))

theorem smallUUvPolyTpEquiv_naturality_left
    (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C)) : smallUUvPolyTpEquiv (ym(σ) ≫ AB) =
    ⟨ Ctx.toGrpd.map σ ⋙ (smallUUvPolyTpEquiv AB).fst,
    pre _ (Ctx.toGrpd.map σ) ⋙ (smallUUvPolyTpEquiv AB).snd ⟩ := by
  dsimp [smallUUvPolyTpEquiv]
  erw [uvPolyTpEquiv_naturality_left]
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


-- NOTE the rest of this file will be removed

def baseUvPolyTpEquiv' {Γ : Ctx.{u}} {C : Cat.{u,u+1}} :
    (y(Γ) ⟶ base.Ptp.obj (yonedaCat.obj C))
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}) × (∫(A) ⥤ C) :=
  base.uvPolyTpEquiv.trans (
  Equiv.sigmaCongr
    yonedaCatEquiv
    (fun _ => yonedaCatEquiv))

/-- A specialization of the polynomial universal property to the natural model `base`
  The polynomial functor on `tp` taken at `yonedaCat.obj C`
  `P_tp(yonedaCat C)` takes a groupoid `Γ`
  to a pair of functors `A` and `B`

      B
   C ⇇ ∫(A)   ⥤   PGrpd
            ⇊               ⇊
            Γ          ⥤   Grpd
                       A
As a special case, if `C` is taken to be `Grpd`,
then this is how `P_tp(Ty)` classifies dependent pairs.
-/
def baseUvPolyTpEquiv {Γ : Ctx.{u}} {C : Cat.{u,u+1}} :
    (base.Ptp.obj (yonedaCat.obj C)).obj (op Γ)
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}) × (∫(A) ⥤ C) :=
  yonedaEquiv.symm.trans baseUvPolyTpEquiv'

@[simp] theorem base_sec {Γ : Ctx.{u}} (α : y(Γ) ⟶ base.Tm) :
    base.sec _ α rfl = Ctx.ofGrpd.map (sec _ (yonedaCatEquiv α) rfl) := by
  apply Yoneda.fullyFaithful.map_injective
  apply (base.disp_pullback _).hom_ext
  . rw [NaturalModelBase.sec_var]
    dsimp only [base_var, var]
    convert_to α =
    yonedaCatEquiv.symm
      (sec _ (yonedaCatEquiv α) rfl ⋙
        toPGrpd (yonedaCatEquiv α ⋙ Cat.homOf PGrpd.forgetToGrpd))
    rw [sec_toPGrpd _, yonedaCatEquiv.eq_symm_apply]
  . rw [NaturalModelBase.sec_disp_functor_map]; rfl

/-- A specialization of the universal property of `UvPoly.compDom`
  to the natural model `base`.
  This consists of a pair of dependent types
  `A = α ⋙ forgetToGrpd` and `B`,
  `a : A` captured by `α`,
  and `b : B[a / x] = β ⋙ forgetToGrpd` caputred by `β`.
  -/
def baseUvPolyTpCompDomEquiv {Γ : Ctx.{u}} :
    (y(Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp)
    ≃ (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B :=
  (base.uvPolyTpCompDomEquiv base Γ).trans <|
  Equiv.sigmaCongr
    yonedaCatEquiv $
    fun α => Equiv.sigmaCongr
      yonedaCatEquiv $
      fun B => Equiv.psigmaCongrProp
        yonedaCatEquiv $
        fun β => by
          convert_to _ ↔ yonedaCatEquiv (β ≫ yonedaCat.map PGrpd.forgetToGrpd)
            = Ctx.toGrpd.map (Ctx.ofGrpd.map
              (sec _ (yonedaCatEquiv α) rfl)) ⋙ yonedaCatEquiv B
          convert_to _ ↔ β ≫ yonedaCat.map PGrpd.forgetToGrpd =
            yoneda.map (Ctx.ofGrpd.map (sec _ (yonedaCatEquiv α) rfl)) ≫ B
          · simp only [yonedaCatEquiv_naturality_left, ← yonedaCatEquiv.apply_eq_iff_eq]
          rw [base_sec]
          simp [yonedaCatEquiv.apply_eq_iff_eq]

def baseUvPolyTpCompDomEquiv' {Γ : Ctx.{u}} :
    (y(Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp)
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u})
    × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : ∫(A) ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ map (eqToHom h) ⋙ B :=
  baseUvPolyTpCompDomEquiv.trans $ {
    toFun := fun ⟨α,B,β,h⟩ => ⟨α ⋙ PGrpd.forgetToGrpd, α, B, β, rfl, by
      rw [h, eqToHom_refl, map_id_eq]
      rfl⟩
    invFun := fun ⟨A,α,B,β,hA,hB⟩ => ⟨α, map (eqToHom hA) ⋙ B, β, by rw [hB] ⟩
    left_inv := by
      intro ⟨α,B,β,h⟩
      dsimp
      congr!
      simp [map_id_eq, Functor.id_comp]
    right_inv := by
      intro ⟨A,α,B,β,h1,h2⟩
      subst h1
      congr!
      · simp [eqToHom_refl, map_id_eq, Functor.id_comp]
    }

def baseTmEquiv {Γ : Ctx} :
    (A : y(Γ) ⟶ base.Ty) × (α : y(Γ) ⟶ base.Tm)
    ×' (α ≫ base.tp = A) ≃
    (A : Ctx.toGrpd.obj Γ ⥤ Grpd) × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd)
    ×' (α ⋙ PGrpd.forgetToGrpd = A) :=
  Equiv.sigmaCongr yonedaCatEquiv $ fun A =>
    Equiv.psigmaCongrProp yonedaCatEquiv $ fun α => (by
      simp only [base_tp, tp]
      convert_to _ ↔ yonedaCatEquiv
        (α ≫ yonedaCat.map (Cat.homOf PGrpd.forgetToGrpd)) = _
      simp)

theorem baseTmEquiv_fst {Γ : Ctx} {A : y(Γ) ⟶ base.Ty} {α : y(Γ) ⟶ base.Tm}
    (h : α ≫ base.tp = A) : (baseTmEquiv ⟨A,α,h⟩).1 = yonedaCatEquiv A := by
  simp [baseTmEquiv, Equiv.sigmaCongr]

theorem baseTmEquiv_snd {Γ : Ctx} {A : y(Γ) ⟶ base.Ty} {α : y(Γ) ⟶ base.Tm}
    (h : α ≫ base.tp = A) : (baseTmEquiv ⟨A,α,h⟩).2.1 = yonedaCatEquiv α := by
  simp [baseTmEquiv, Equiv.sigmaCongr, Equiv.psigmaCongrProp]

end GroupoidModel

end
