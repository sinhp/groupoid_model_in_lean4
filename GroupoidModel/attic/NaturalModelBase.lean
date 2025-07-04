import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Category.Cat.Limit

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.Groupoidal.IsPullback
import GroupoidModel.Groupoids.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory
  Limits NaturalModelBase
  GroupoidModel.IsPullback.SmallU
  GroupoidModel.IsPullback.SmallUHom
  Grothendieck.Groupoidal

namespace GroupoidModel

section
variable {Γ : Ctx} (A : y(Γ) ⟶ y(U.{v}))

def smallU.ext : Ctx :=
  Ctx.ofGrpd.obj (Grpd.of ∫(yonedaCategoryEquiv A))

def smallU.disp : smallU.ext.{v} A ⟶ Γ :=
  Ctx.ofGrpd.map forget

def smallU.var : y(smallU.ext.{v} A) ⟶ y(E.{v}) :=
  yonedaCategoryEquiv.symm (toPGrpd (yonedaCategoryEquiv A))

end

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that `Ty` and `Tm` are representables,
  but since representables are `Ctx`-large,
  its representable fibers can be larger (in terms of universe levels) than itself.
-/
@[simps] def smallU : NaturalModelBase Ctx where
  Ty := y(U.{v})
  Tm := y(E)
  tp := ym(π)
  ext A := smallU.ext A
  disp A := smallU.disp A
  var A := smallU.var A
  disp_pullback A := by
    convert isPullback_yonedaDisp_yonedaπ (Yoneda.fullyFaithful.homEquiv.symm A)
    simp

namespace U

open MonoidalCategory

def asSmallClosedType' : tensorUnit _
    ⟶ U.{v+1, max u (v+2)} :=
  toCoreAsSmallEquiv.symm ((Functor.const _).obj
    (Grpd.of (Core (AsSmall.{v+1} Grpd.{v,v}))))

def asSmallClosedType : y(tensorUnit _)
    ⟶ smallU.{v+1, max u (v+2)}.Ty :=
  ym(U.asSmallClosedType')

def isoGrpd : Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ Grpd.{v,v} := Core.inclusion _ ⋙ AsSmall.down

def isoExtAsSmallClosedTypeHom :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ ∫(classifier (asSmallClosedType'.{v, max u (v + 2)})) where
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
    ∫(classifier (asSmallClosedType'.{v, max u (v + 2)})) ⥤
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

theorem smallU_lift {Γ Δ : Ctx} (A : y(Γ) ⟶ smallU.{v}.Ty)
    (fst : y(Δ) ⟶ smallU.{v}.Tm) (snd : Δ ⟶ Γ)
    (w : fst ≫ smallU.{v}.tp = ym(snd) ≫ A) :
    (smallU.{v}.disp_pullback A).lift fst ym(snd) w =
    ym(Ctx.ofGrpd.map ((Grothendieck.Groupoidal.isPullback _).lift
      (yonedaCategoryEquiv fst)
      (Ctx.toGrpd.map snd)
      (by erw [← yonedaCategoryEquiv_naturality_right, w,
        yonedaCategoryEquiv_naturality_left]))) := by
  apply (smallU.{v}.disp_pullback A).hom_ext
  · dsimp only [smallU_var]
    erw [← yonedaCategoryEquiv_symm_naturality_left,
      (Grothendieck.Groupoidal.isPullback (yonedaCategoryEquiv A)).fac_left,
      Equiv.apply_symm_apply]
    simp
  · simp only [smallU_ext, smallU_Tm, smallU_Ty, smallU_var, Grpd.coe_of,
      Equiv.symm_trans_apply, Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, smallU_disp,
      smallU_tp, IsPullback.lift_snd, ← Functor.map_comp, Grpd.comp_eq_comp,
      smallU.disp]
    erw [(isPullback (yonedaCategoryEquiv A)).fac_right, AsSmall.down_map_up_map]

def yonedaCategoryEquivPre (A : y(Γ) ⟶ smallU.{v}.Ty) :
    ∫(yonedaCategoryEquiv (ym(σ) ≫ A)) ⥤ ∫(yonedaCategoryEquiv A) :=
  map (eqToHom (by rw [yonedaCategoryEquiv_naturality_left]))
  ⋙ pre (yonedaCategoryEquiv A) (Ctx.toGrpd.map σ)

namespace Ctx

@[simp] lemma toGrpd_obj_ofGrpd_obj (x) : toGrpd.obj (ofGrpd.obj x) = x := rfl

@[simp] lemma ofGrpd_obj_toGrpd_obj (x) : ofGrpd.obj (toGrpd.obj x) = x := rfl

@[simp] lemma toGrpd_map_ofGrpd_map {x y} (f : x ⟶ y) : toGrpd.map (ofGrpd.map f) = f := rfl

@[simp] lemma ofGrpd_map_toGrpd_map {x y} (f : x ⟶ y) : ofGrpd.map (toGrpd.map f) = f := rfl

end Ctx

namespace Grothendieck.Groupoidal

theorem map_eqToHom_toPGrpd {Γ : Type*} [Category Γ] (A A' : Γ ⥤ Grpd) (h : A = A'):
    map (eqToHom h) ⋙ toPGrpd A' = toPGrpd A := by
  subst h
  simp [map_id_eq, Functor.id_comp]

end Grothendieck.Groupoidal

theorem smallU_substWk (A : y(Γ) ⟶ smallU.{v}.Ty) : smallU.substWk σ A =
    (Ctx.ofGrpd.map $ Grpd.homOf $ yonedaCategoryEquivPre σ A) := by
  apply Yoneda.fullyFaithful.map_injective
  apply (smallU.disp_pullback A).hom_ext
  · conv => right; erw [← yonedaCategoryEquiv_symm_naturality_left]
    rw [substWk_var, smallU_var, yonedaCategoryEquivPre, Ctx.toGrpd_map_ofGrpd_map,
      Functor.assoc, pre_toPGrpd, Grothendieck.Groupoidal.map_eqToHom_toPGrpd]
    dsimp only [smallU_Ty, smallU_ext, smallU.var]
  · conv => left; rw [← Functor.map_comp, substWk_disp]
    simp only [smallU_disp, ← Functor.map_comp, Grpd.homOf, yonedaCategoryEquivPre,
      Grpd.comp_eq_comp, Functor.assoc, smallU.disp]
    rw [pre_forget, ← Functor.assoc, map_forget]
    rfl

@[simp] theorem smallU_sec {Γ : Ctx} (α : y(Γ) ⟶ smallU.{v}.Tm) :
    smallU.sec _ α rfl = Ctx.ofGrpd.map (sec _ (yonedaCategoryEquiv α) rfl) := by
  apply Yoneda.fullyFaithful.map_injective
  apply (smallU.disp_pullback _).hom_ext
  . erw [NaturalModelBase.sec_var, smallU_var, ← yonedaCategoryEquiv_symm_naturality_left,
      Equiv.eq_symm_apply, Ctx.toGrpd_map_ofGrpd_map, sec_toPGrpd]
    rfl
  . rw [← Functor.map_comp, sec_disp]
    simp only [CategoryTheory.Functor.map_id, smallU_Tm, smallU_Ty, smallU_tp, smallU_ext,
      smallU_disp, ← Functor.map_comp, Grpd.comp_eq_comp, Grpd.coe_of, sec_forget, ← Grpd.id_eq_id]
    rfl

namespace smallU
namespace PtpEquiv

variable (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))

/--
A map `(AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.fst` is the `A` in this pair.
-/
def fst : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v} :=
  yonedaCategoryEquiv (NaturalModelBase.PtpEquiv.fst smallU AB)

/--
A map `(AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd : ∫(fst AB) ⥤ C :=
  yonedaCategoryEquiv (NaturalModelBase.PtpEquiv.snd smallU AB)

theorem fst_naturality : fst (ym(σ) ≫ AB) = Ctx.toGrpd.map σ ⋙ fst AB := by
  dsimp only [fst]
  rw [PtpEquiv.fst_naturality_left, ← yonedaCategoryEquiv_naturality_left]

theorem snd_naturality : snd (ym(σ) ≫ AB) =
    map (eqToHom (fst_naturality σ AB)) ⋙ pre _ (Ctx.toGrpd.map σ) ⋙ snd AB := by
  rw [snd, PtpEquiv.snd_naturality_left, yonedaCategoryEquiv_naturality_left, ← Functor.assoc,
    smallU_substWk, Ctx.toGrpd_map_ofGrpd_map, yonedaCategoryEquivPre, Grpd.homOf]
  rfl

/--
A map `(AB : y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C))`
is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
    y(Γ) ⟶ smallU.{v}.Ptp.obj y(Ctx.ofCategory C) :=
  NaturalModelBase.PtpEquiv.mk smallU (yonedaCategoryEquiv.symm A) (yonedaCategoryEquiv.symm B)

theorem hext (AB1 AB2 : y(Γ) ⟶ smallU.{v}.Ptp.obj y(U.{v})) (hfst : fst AB1 = fst AB2)
    (hsnd : HEq (snd AB1) (snd AB2)) : AB1 = AB2 := by
  -- apply NaturalModelBase.PtpEquiv.ext
  sorry

end PtpEquiv

def compDom := smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp

def comp : compDom.{v} ⟶ smallU.{v}.Ptp.obj y(U.{v}) :=
  (smallU.{v}.uvPolyTp.comp smallU.{v}.uvPolyTp).p

namespace compDom

variable (ab : y(Γ) ⟶ compDom.{v})

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : y(Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `fst : Γ ⥤ PGrpd`
is `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v} :=
  yonedaCategoryEquiv (NaturalModelBase.compDomEquiv.fst smallU ab)

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : y(Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `dependent : Γ ⥤ Grpd`
is `B : A → Type` in `(a : A) × (b : B a)`.
-/
def dependent : ∫(fst ab ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v} :=
  yonedaCategoryEquiv (NaturalModelBase.compDomEquiv.dependent smallU ab)

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : y(Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `snd : Γ ⥤ PGrpd`
is `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v} :=
  yonedaCategoryEquiv (NaturalModelBase.compDomEquiv.snd smallU ab)

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : y(Γ) ⟶ compDom` is equivalently three functors
`fst, dependent, snd` such that `snd_forgetToGrpd`.
The equation `snd_forgetToGrpd` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_forgetToGrpd : snd ab ⋙ PGrpd.forgetToGrpd = sec _ (fst ab) rfl ⋙ (dependent ab) := by
  erw [← yonedaCategoryEquiv_naturality_right, NaturalModelBase.compDomEquiv.snd_tp smallU ab,
    smallU_sec, yonedaCategoryEquiv_naturality_left]
  rfl

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v}) (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v})
    (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : y(Γ) ⟶ compDom.{v} :=
  NaturalModelBase.compDomEquiv.mk smallU (yonedaCategoryEquiv.symm α)
    (yonedaCategoryEquiv.symm B) (yonedaCategoryEquiv.symm β) (by
      erw [← yonedaCategoryEquiv_symm_naturality_right, h,
        ← yonedaCategoryEquiv_symm_naturality_left, smallU_sec]
      rfl)

theorem fst_forgetToGrpd : fst ab ⋙ PGrpd.forgetToGrpd =
    smallU.PtpEquiv.fst (ab ≫ comp.{v}) := by
  erw [smallU.PtpEquiv.fst, ← compDomEquiv.fst_tp smallU ab, ← yonedaCategoryEquiv_naturality_right]
  rfl

theorem dependent_eq : dependent ab =
    map (eqToHom (fst_forgetToGrpd ab)) ⋙ smallU.PtpEquiv.snd (ab ≫ comp.{v}) := by
  dsimp only [dependent, smallU.PtpEquiv.snd]
  rw [NaturalModelBase.compDomEquiv.dependent_eq smallU ab, yonedaCategoryEquiv_naturality_left,
    eqToHom_map, eqToHom_eq_homOf_map]
  rfl

theorem dependent_heq : HEq (dependent ab) (smallU.PtpEquiv.snd (ab ≫ comp.{v})) := by
  rw [dependent_eq]
  apply Functor.precomp_heq_of_heq_id
  · rw [fst_forgetToGrpd]
  · rw [fst_forgetToGrpd]
  · apply map_eqToHom_heq_id_cod

theorem fst_naturality : fst (ym(σ) ≫ ab) = Ctx.toGrpd.map σ ⋙ fst ab := by
  dsimp only [fst]
  rw [NaturalModelBase.compDomEquiv.fst_naturality, yonedaCategoryEquiv_naturality_left]

theorem dependent_naturality : dependent (ym(σ) ≫ ab) = map (eqToHom (by rw [fst_naturality, Functor.assoc]))
    ⋙ pre _ (Ctx.toGrpd.map σ) ⋙ dependent ab := by
  rw [dependent, dependent, NaturalModelBase.compDomEquiv.dependent_naturality, smallU_substWk,
    yonedaCategoryEquiv_naturality_left, Functor.map_comp, eqToHom_map, Ctx.toGrpd_map_ofGrpd_map,
    yonedaCategoryEquivPre, Grpd.homOf_comp, ← eqToHom_eq_homOf_map, ← Category.assoc,
    eqToHom_trans, Grpd.comp_eq_comp, Grpd.homOf, eqToHom_eq_homOf_map]
  rfl

theorem snd_naturality : snd (ym(σ) ≫ ab) = Ctx.toGrpd.map σ ⋙ snd ab := by
  dsimp only [snd]
  rw [NaturalModelBase.compDomEquiv.snd_naturality, yonedaCategoryEquiv_naturality_left]

/-- First component of the computation rule for `mk`. -/
theorem fst_mk (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : fst (mk α B β h) = α := by
  dsimp [fst, mk]
  -- TODO
  -- apply NaturalModelBase.compDomEquiv.fst_mk
  sorry

/-- Second component of the computation rule for `mk`. -/
theorem dependent_mk (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : dependent (mk α B β h) = map (eqToHom (by rw [fst_mk])) ⋙ B := by
  dsimp [snd, mk]
  -- TODO
  -- apply NaturalModelBase.compDomEquiv.snd_mk
  sorry

/-- Second component of the computation rule for `mk`. -/
theorem snd_mk (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v}) (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (h : β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B)
    : snd (mk α B β h) = β := by
  dsimp [snd, mk]
  -- TODO
  -- apply NaturalModelBase.compDomEquiv.snd_mk
  sorry

theorem smallU.compDom.hext (ab1 ab2 : y(Γ) ⟶ smallU.compDom.{v}) (hfst : fst ab1 = fst ab2)
    (hdependent : HEq (dependent ab1) (dependent ab2)) (hsnd : snd ab1 = snd ab2) : ab1 = ab2 := by
  sorry

end compDom

namespace IsPullback

variable {E B} (intr : E ⟶ smallU.{v}.Tm) (typ : E ⟶ B) (form : B ⟶ smallU.{v}.Ty)

variable (intr_tp : intr ≫ smallU.tp = typ ≫ form)
    (liftExt : Π {Γ : Ctx} (b : y(Γ) ⟶ B),
      (f : y(smallU.ext (b ≫ form)) ⟶ E)
      ×' f ≫ intr = smallU.var (b ≫ form)
      ∧ f ≫ typ = ym(smallU.disp (b ≫ form)) ≫ b)

def lift (s : RepPullbackCone smallU.tp form) : y(s.pt) ⟶ E :=
  NaturalModelBase.IsPullback.lift smallU intr typ form liftExt s

theorem fac_left (s : RepPullbackCone smallU.tp form) :
    lift intr typ form liftExt s ≫ intr = s.fst :=
  NaturalModelBase.IsPullback.fac_left smallU intr typ form liftExt s

theorem fac_right (s : RepPullbackCone smallU.tp form) :
    lift intr typ form liftExt s ≫ typ = s.snd :=
  NaturalModelBase.IsPullback.fac_right smallU intr typ form liftExt s

include intr_tp liftExt in
/-- To show that the square

  E ----------> smallU.Tm
  |               |
  |               |
  |               |
  |               |
  V               V
  B ----------> smallU.Ty

  is a pullback, it suffices to construct a unique lift from
  every context extension.
 y(ext) --------> E ----------> smallU.Tm
  |               |              |
  |               |              |
  |               |              |
  |               |              |
  V               V              V
 y(Γ) ----------> B ----------> smallU.Ty
-/
theorem of_existsUnique_liftExt_hom_ext
  (hom_ext : Π {Γ : Ctx} (f1 f2 : y(Γ) ⟶ E),
    f1 ≫ intr = f2 ≫ intr ∧ f1 ≫ typ = f2 ≫ typ → f1 = f2) :
    IsPullback intr typ smallU.{v}.tp form :=
  NaturalModelBase.IsPullback.of_existsUnique_liftExt_hom_ext _ _ _ _ intr_tp liftExt hom_ext

end IsPullback

end smallU
end

end GroupoidModel

end
