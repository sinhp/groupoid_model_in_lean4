import HoTTLean.Model.Unstructured.UnstructuredUniverse
import Mathlib.CategoryTheory.NatIso

universe v u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Opposite

namespace Model

namespace UnstructuredUniverse

open MonoidalCategory

open Functor in
/-- A cylinder (functor) is an endofunctor `I` with two "endpoint" natural transformations
`δ0, δ1` from the identity endofunctor, a "projection" natural transformation `π`
to the identity endofunctor, and a symmetry isomorphism `symm : I ⋙ I → I ⋙ I`.

These satisfy some minimal equations to allow for abstract cubical-style reasoning. -/
structure Cylinder (Ctx : Type u) [Category.{v} Ctx] where
  (I : Ctx ⥤ Ctx)
  (δ0 δ1 : 𝟭 Ctx ⟶ I)
  (π : I ⟶ 𝟭 Ctx)
  (δ0_π : δ0 ≫ π = 𝟙 _)
  (δ1_π : δ1 ≫ π = 𝟙 _)
  (symm : I ⋙ I ⟶ I ⋙ I)
  (symm_symm : symm ≫ symm = 𝟙 _)
  (whiskerLeft_I_δ0_symm : whiskerLeft I δ0 ≫ symm = whiskerRight δ0 I)
  (whiskerLeft_I_δ1_symm : whiskerLeft I δ1 ≫ symm = whiskerRight δ1 I)
  (symm_π_π : symm ≫ whiskerLeft I π ≫ π = whiskerLeft I π ≫ π)

variable {Ctx : Type u} [Category Ctx] (cyl : Cylinder Ctx)

namespace Cylinder

@[reassoc (attr := simp)]
lemma δ0_π' : cyl.δ0 ≫ cyl.π = 𝟙 _ := δ0_π _

@[reassoc (attr := simp)]
lemma δ1_π' : cyl.δ1 ≫ cyl.π = 𝟙 _ := δ1_π _

@[reassoc (attr := simp)]
lemma δ0_π'_app (X) : cyl.δ0.app X ≫ cyl.π.app _ = 𝟙 _ := by
  simp [← NatTrans.comp_app]

@[reassoc (attr := simp)]
lemma δ1_π'_app (X) : cyl.δ1.app X ≫ cyl.π.app _ = 𝟙 _ := by
  simp [← NatTrans.comp_app]

@[reassoc]
lemma δ0_naturality {Γ Δ} (σ : Δ ⟶ Γ) : cyl.δ0.app Δ ≫ cyl.I.map σ = σ ≫ cyl.δ0.app Γ := by
  simp [← NatTrans.naturality]

@[reassoc]
lemma δ1_naturality {Γ Δ} (σ : Δ ⟶ Γ) : cyl.δ1.app Δ ≫ cyl.I.map σ = σ ≫ cyl.δ1.app Γ := by
  simp [← NatTrans.naturality]

@[reassoc (attr := simp)]
lemma symm_symm' : cyl.symm ≫ cyl.symm = 𝟙 _ := symm_symm ..

open Functor in
lemma whiskerRight_δ0_I_symm : whiskerRight cyl.δ0 cyl.I ≫ cyl.symm =
    whiskerLeft cyl.I cyl.δ0 := by
  simp [← whiskerLeft_I_δ0_symm]

open Functor in
lemma whiskerRight_δ1_I_symm : whiskerRight cyl.δ1 cyl.I ≫ cyl.symm =
    whiskerLeft cyl.I cyl.δ1 := by
  simp [← whiskerLeft_I_δ1_symm]

@[reassoc (attr := simp)]
lemma δ0_app_I_obj_comp_symm_app (X) : cyl.δ0.app (cyl.I.obj X) ≫ cyl.symm.app X =
    cyl.I.map (cyl.δ0.app X) :=
  NatTrans.congr_app (cyl.whiskerLeft_I_δ0_symm) X

@[reassoc (attr := simp)]
lemma δ1_app_I_obj_comp_symm_app (X) : cyl.δ1.app (cyl.I.obj X) ≫ cyl.symm.app X = cyl.I.map (cyl.δ1.app X) :=
  NatTrans.congr_app (cyl.whiskerLeft_I_δ1_symm) X

@[reassoc (attr := simp)]
lemma I_map_δ0_app_comp_symm_app (X) : cyl.I.map (cyl.δ0.app X) ≫ cyl.symm.app X = cyl.δ0.app _ :=
  NatTrans.congr_app (cyl.whiskerRight_δ0_I_symm) X

@[reassoc (attr := simp)]
lemma I_map_δ1_app_comp_symm_app (X) : cyl.I.map (cyl.δ1.app X) ≫ cyl.symm.app X = cyl.δ1.app _ :=
  NatTrans.congr_app (cyl.whiskerRight_δ1_I_symm) X

@[reassoc]
lemma symm_π_π'_app (X) : cyl.symm.app X ≫ cyl.π.app (cyl.I.obj X) ≫ cyl.π.app X =
    cyl.π.app (cyl.I.obj X) ≫ cyl.π.app X :=
  NatTrans.congr_app (cyl.symm_π_π) X

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory in
def ofCartesianMonoidalCategoryLeft [CartesianMonoidalCategory Ctx] (Interval : Ctx)
    (δ0 δ1 : 𝟙_ Ctx ⟶ Interval) : Cylinder Ctx where
  I := tensorLeft Interval
  δ0 := (leftUnitorNatIso _).inv ≫ (tensoringLeft _).map δ0
  δ1 := (leftUnitorNatIso _).inv ≫ (tensoringLeft _).map δ1
  π := (tensoringLeft _).map (toUnit _) ≫ (leftUnitorNatIso _).hom
  δ0_π := by simp [← Functor.map_comp_assoc]
  δ1_π := by simp [← Functor.map_comp_assoc]
  symm := (tensorLeftTensor _ _).inv ≫ (tensoringLeft _).map (β_ _ _).hom ≫
    (tensorLeftTensor _ _).hom
  symm_symm := by simp [← Functor.map_comp_assoc]
  whiskerLeft_I_δ0_symm := by
    ext
    simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, Functor.whiskerLeft_comp,
      Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app, leftUnitorNatIso_inv_app,
      leftUnitor_tensor_inv, curriedTensor_map_app, whiskerRight_tensor, tensorLeftTensor_inv_app,
      tensorLeftTensor_hom_app, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left, leftUnitor_inv_braiding_assoc ]
    simp
  whiskerLeft_I_δ1_symm := by
    ext
    simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, Functor.whiskerLeft_comp,
      Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app, leftUnitorNatIso_inv_app,
      leftUnitor_tensor_inv, curriedTensor_map_app, whiskerRight_tensor, tensorLeftTensor_inv_app,
      tensorLeftTensor_hom_app, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left, leftUnitor_inv_braiding_assoc, ]
    simp
  symm_π_π := by
    ext
    simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, Functor.whiskerLeft_comp,
      Category.assoc, NatTrans.comp_app, tensorLeftTensor_inv_app, curriedTensor_map_app,
      tensorLeftTensor_hom_app, Functor.whiskerLeft_app, whiskerRight_tensor,
      leftUnitorNatIso_hom_app, Iso.hom_inv_id_assoc, Iso.cancel_iso_inv_left]
    have h0 (x) : 𝟙_ Ctx ◁ toUnit Interval ▷ x = 𝟙 _ ⊗ₘ toUnit Interval ⊗ₘ 𝟙 x := by simp
    have h1 (x) : (𝟙_ Ctx ◁ toUnit Interval) ▷ x = (𝟙 _ ⊗ₘ toUnit Interval) ⊗ₘ 𝟙 x := by simp
    have h2 : λ_ (𝟙_ Ctx) = ρ_ (𝟙_ Ctx) := by aesop_cat
    rw [← leftUnitor_naturality_assoc, h0, ← associator_naturality_assoc, ← h1]
    simp [← comp_whiskerRight_assoc, h2]

/-- A Hurewicz cleavage (just called `Hurewicz`) of `f` consists of a diagonal filler
`lift` for every commutative square of the form
```
    y
Γ -----> Y
|        |
|δ0      |f
|        |
V        V
I;Γ ---> X
```
-/
structure Hurewicz {X Y : Ctx} (f : Y ⟶ X) where
  (lift : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X), y ≫ f = cyl.δ0.app Γ ≫ p →
    (cyl.I.obj Γ ⟶ Y))
  (lift_comp_self : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), lift y p comm_sq ≫ f = p)
  (δ0_comp_lift : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), cyl.δ0.app Γ ≫ lift y p comm_sq = y)

variable {cyl} {X Y : Ctx} {f : Y ⟶ X} (hrwcz : cyl.Hurewicz f)

@[reassoc (attr := simp)]
lemma Hurewicz.lift_comp_self' {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : hrwcz.lift y p comm_sq ≫ f = p :=
  lift_comp_self ..

@[reassoc (attr := simp)]
lemma Hurewicz.δ0_comp_lift' {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : cyl.δ0.app Γ ≫ hrwcz.lift y p comm_sq = y :=
  δ0_comp_lift ..

/-- A Hurewicz cleavage is uniform when it is stable under precomposition. -/
class Hurewicz.IsUniform : Prop where
  (lift_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), hrwcz.lift (σ ≫ y) (cyl.I.map σ ≫ p)
    (by simp [comm_sq, δ0_naturality_assoc]) = cyl.I.map σ ≫ hrwcz.lift y p comm_sq)

@[reassoc]
lemma Hurewicz.lift_comp [IsUniform hrwcz] {Γ Δ} (σ : Δ ⟶ Γ) (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : hrwcz.lift (σ ≫ y) (cyl.I.map σ ≫ p)
    (by simp [comm_sq, δ0_naturality_assoc]) = cyl.I.map σ ≫ hrwcz.lift y p comm_sq :=
  IsUniform.lift_comp ..

/-- A Hurewicz cleavage is normal when lifts of constant paths are constant.
This means that the lift of the following square is just `π ≫ y`
```
    y
Γ --------------> Y
|             ↗  |
|δ0         y⧸    |
|           ⧸     |
V          ⧸      V
I;Γ ---> Γ -----> X
     π       x
```
-/
class Hurewicz.IsNormal : Prop where
  (isNormal : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X) (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p)
    (x : Γ ⟶ X), p = cyl.π.app Γ ≫ x → hrwcz.lift y p comm_sq = cyl.π.app Γ ≫ y)

@[reassoc]
lemma Hurewicz.isNormal [IsNormal hrwcz] {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) (x : Γ ⟶ X) (hp : p = cyl.π.app Γ ≫ x) :
    hrwcz.lift y p comm_sq = cyl.π.app Γ ≫ y :=
  IsNormal.isNormal y p comm_sq x hp

end Cylinder

open Cylinder

/-- An elementary formulation of Steve Awodey's natural model formulation of identity types,
in the presence of an interval.
Unlike the original, this formulation does not require an object `I`, exponentials,
or the presence of any limits (other than a terminal object and chosen pullbacks of the classifier)
on the category of contexts.

`Path` constructs the identity type,
`unPath` and `path` form a natural (as in stable under precomposition)
bijection between terms of `Γ ⊢ e : Path_A (a,b)`
```
     e
Γ ------> Tm
‖          |
‖          |tp
‖          |
‖          V
Γ ------> Ty
  Path_A(a,b)
```
and "cubical paths" `(i:I);Γ ⊢ p i : A` such that `p 0 = a` and `p 1 = b`
```
     p
I;Γ -----> Tm
|          |
|          |tp
|          |
V          V
Γ ------> Ty
     A
```
-/
structure PathType (U : UnstructuredUniverse Ctx) where
  (Path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm), (a0 ≫ U.tp = A) → a1 ≫ U.tp = A →
    (Γ ⟶ U.Ty))
  (Path_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A),
    Path (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) =
    σ ≫ Path a0 a1 a0_tp a1_tp)
  (path : ∀ {Γ} {A : Γ ⟶ U.Ty} (p : cyl.I.obj Γ ⟶ U.Tm),
    p ≫ U.tp = cyl.π.app Γ ≫ A → (Γ ⟶ U.Tm))
  (path_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty}
    (p : cyl.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A),
    path (A := σ ≫ A) ((cyl.I.map σ) ≫ p) (by simp [p_tp]) =
    σ ≫ path p p_tp)
  (path_tp : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (p : cyl.I.obj Γ ⟶ U.Tm)
    (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1), path p p_tp ≫ U.tp =
    Path (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp]))
  (unpath : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm), p ≫ U.tp =
    Path a0 a1 a0_tp a1_tp → (cyl.I.obj Γ ⟶ U.Tm))
  (unpath_tp : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Path a0 a1 a0_tp a1_tp),
    unpath a0 a1 a0_tp a1_tp p p_tp ≫ U.tp = cyl.π.app _ ≫ A)
  (δ0_unpath : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Path a0 a1 a0_tp a1_tp),
    cyl.δ0.app _ ≫ unpath a0 a1 a0_tp a1_tp p p_tp = a0)
  (δ1_unpath : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Path a0 a1 a0_tp a1_tp),
    cyl.δ1.app _ ≫ unpath a0 a1 a0_tp a1_tp p p_tp = a1)
  (unpath_path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (p : cyl.I.obj Γ ⟶ U.Tm)
    (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1),
    unpath (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp])
    (path p p_tp) (path_tp a0 a1 p p_tp δ0_p δ1_p) = p)
  (path_unpath : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Path a0 a1 a0_tp a1_tp),
    path (A := A) (unpath a0 a1 a0_tp a1_tp p p_tp)
    (unpath_tp ..) = p)

namespace PathType

variable {cyl} {U0 : UnstructuredUniverse Ctx} (P0 : PathType cyl U0)

@[reassoc (attr := simp)]
lemma path_tp' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (p : cyl.I.obj Γ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1) : P0.path p p_tp ≫ U0.tp =
    P0.Path (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp]) :=
  P0.path_tp a0 a1 p p_tp δ0_p δ1_p

@[reassoc (attr := simp)]
lemma unpath_tp' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Path a0 a1 a0_tp a1_tp) :
    P0.unpath a0 a1 a0_tp a1_tp p p_tp ≫ U0.tp = cyl.π.app _ ≫ A :=
  unpath_tp ..

@[reassoc (attr := simp)]
lemma unpath_path' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (p : cyl.I.obj Γ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1) :
    P0.unpath (A := A) a0 (a1) (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp])
    (P0.path p p_tp) (P0.path_tp a0 a1 p p_tp δ0_p δ1_p) = p :=
  P0.unpath_path a0 a1 p p_tp δ0_p δ1_p

@[reassoc (attr := simp)]
lemma path_unpath' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Path a0 a1 a0_tp a1_tp) :
    P0.path (A := A) (P0.unpath a0 a1 a0_tp a1_tp p p_tp) (P0.unpath_tp ..) = p :=
  path_unpath ..

@[reassoc (attr := simp)]
lemma δ0_unpath' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Path a0 a1 a0_tp a1_tp) :
    cyl.δ0.app _ ≫ P0.unpath a0 a1 a0_tp a1_tp p p_tp = a0 :=
  δ0_unpath ..

@[reassoc (attr := simp)]
lemma δ1_unpath' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Path a0 a1 a0_tp a1_tp) :
    cyl.δ1.app _ ≫ P0.unpath a0 a1 a0_tp a1_tp p p_tp = a1 :=
  δ1_unpath ..

lemma unpath_ext {Γ} (A : Γ ⟶ U0.Ty) (a0 a1 : Γ ⟶ U0.Tm) (p1 p2 : cyl.I.obj Γ ⟶ U0.Tm)
    (p1_tp : p1 ≫ U0.tp = cyl.π.app Γ ≫ A) (p2_tp : p2 ≫ U0.tp = cyl.π.app Γ ≫ A)
    (h : P0.path p1 p1_tp = P0.path p2 p2_tp)
    (δ0_p1 : cyl.δ0.app Γ ≫ p1 = a0) (δ1_p1 : cyl.δ1.app Γ ≫ p1 = a1)
    (δ0_p2 : cyl.δ0.app Γ ≫ p2 = a0) (δ1_p2 : cyl.δ1.app Γ ≫ p2 = a1) : p1 = p2 := by
  rw [← P0.unpath_path (A := A) a0 a1 p1 p1_tp δ0_p1 δ1_p1]
  rw [← P0.unpath_path a0 a1 p2 p2_tp δ0_p2 δ1_p2]
  rw! [h]
  rfl

lemma unpath_comp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Path a0 a1 a0_tp a1_tp) :
    P0.unpath (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) (σ ≫ p)
    (by simp [p_tp, ← Path_comp]) = cyl.I.map σ ≫ P0.unpath a0 a1 a0_tp a1_tp p p_tp := by
  apply P0.unpath_ext (σ ≫ A) (σ ≫ a0) (σ ≫ a1) <;> simp [path_comp, δ0_naturality_assoc,
    δ1_naturality_assoc]

/-- An alternative version of `path` that allows the domain context to be any context `Δ`,
not just the context `Γ`. -/
@[simp]
abbrev path' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (p : cyl.I.obj Δ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Δ ≫ σ ≫ A) : Δ ⟶ U0.Tm :=
  P0.path (A := σ ≫ A) p p_tp

/-- An alternative version of `unpath` that allows the domain context to be any context `Δ`,
not just the context `Γ`. -/
@[simp]
abbrev unpath' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Δ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = σ ≫ P0.Path a0 a1 a0_tp a1_tp) :
    cyl.I.obj Δ ⟶ U0.Tm :=
  P0.unpath (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) p
  (by simp [p_tp, ← Path_comp])

/-- Path types give rise to
formation and introduction rules for traditional HoTT identity types. -/
@[simps]
def polymorphicIdIntro : PolymorphicIdIntro U0 U0 where
  Id := P0.Path
  Id_comp := P0.Path_comp
  refl {_ A} a a_tp := P0.path (A := A) (cyl.π.app _ ≫ a) (by simp [a_tp])
  refl_comp σ A a a_tp := by simp [← path_comp, a_tp]
  refl_tp a a_tp := by simp

open PolymorphicIdIntro

section connection

variable (hrwcz0 : Hurewicz cyl U0.tp) {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)

/-- Fixing `Γ ⊢ a : A`, `ev` / `substConsEv` can be viewed as the cubical substitution
`(i : I);(x : A).(p : Id(a,x)) ⊢ p' i : A`,
satisfying equations `p' 0 = a` and `p' 1 = x`,
proven in `δ0_substConsEv` and `δ1_substConsEv`.
It can be thought of as the "evaluation" of the unpath `p` at a point in the interval.
It is defined by taking `unpath` of the map `var : Γ.(x:A).Id(a,x) ⟶ Tm`

```
               var
Γ.(x:A).Id(a,x) ---> Tm
    |                |
    |                |
  disp               tp
    |                |
    V                V
   Γ.A  --------->  Ty
        Id(a,x)

                   ev
I;(Γ.(x:A).Id(a,x) ---> Tm
    |                   |
    |                   |
    π                   tp
    |                   |
    V                   V
Γ.(x:A).Id(a,x)  ---->  Ty
              ↑↑A
```
-/
@[simp]
abbrev ev : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.Tm :=
  P0.unpath' (A := disp .. ≫ A) (disp ..) (disp .. ≫ a) (var ..)
  (by cat_disch) (by simp) (var ..) (by simp)

/-
                    ev
       ⌐----------------------------¬
       |      substCons             V
I;Γ.(x:A).Id(a,x) ····> Γ.A -------> Tm
    |                   |             |
    |                   |             |
    π                  disp          tp
    |                   |             |
    V                   V             V
Γ.(x:A).Id(a,x)  ---->  Γ ---------> Ty
                ↑↑          A

-/
@[inherit_doc ev]
def substConsEv : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.ext A :=
  U0.substCons (cyl.π.app _ ≫ disp .. ≫ disp ..) A
  (P0.ev a a_tp) (by simp)

@[reassoc (attr := simp)]
lemma substConsEv_disp : P0.substConsEv a a_tp ≫ disp .. = cyl.π.app _ ≫ U0.disp _ ≫ U0.disp A := by
  simp [substConsEv]

@[reassoc (attr := simp)]
lemma substConsEv_var : P0.substConsEv a a_tp ≫ var .. = P0.unpath (A := disp .. ≫ disp .. ≫ A)
    (U0.disp .. ≫ U0.disp A ≫ a) (U0.disp .. ≫ U0.var A)
    (by cat_disch) (by simp) (U0.var ..) (by simp [← Path_comp]) := by
  simp [substConsEv]

@[reassoc (attr := simp)]
lemma δ0_substConsEv : cyl.δ0.app _ ≫ P0.substConsEv a a_tp = disp .. ≫ disp .. ≫ U0.sec A a a_tp := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsEv]
  · simp [substConsEv]

@[reassoc (attr := simp)]
lemma δ1_substConsEv : cyl.δ1.app _ ≫ P0.substConsEv a a_tp = U0.disp .. := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsEv]
  · simp [substConsEv]

@[reassoc]
lemma substConsEv_comp_substWk : P0.substConsEv (A := σ ≫ A) (σ ≫ a) (by simp [a_tp]) ≫
    U0.substWk σ A =
    cyl.I.map (U0.substWk (U0.substWk σ A) (weakenId _ a a_tp) _ ((weakenId_comp ..).symm)) ≫
    P0.substConsEv a a_tp := by
  simp [substConsEv, ← unpath_comp, substWk]

@[reassoc]
lemma I_map_reflInst_comp_substConsEv : cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫
    P0.substConsEv a a_tp = cyl.π.app Γ ≫ U0.sec A a a_tp := by
  apply (disp_pullback ..).hom_ext <;> simp [substConsEv, reflInst, ← unpath_comp, motiveInst]

/-- An auxiliary definition for `connection`. -/
def connectionLift : cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp) ⟶ U0.Tm :=
  hrwcz0.lift (disp .. ≫ disp .. ≫ P0.polymorphicIdIntro.refl a a_tp)
  (P0.substConsEv a a_tp ≫ P0.polymorphicIdIntro.weakenId a a_tp) (by
    simp only [motiveCtx, polymorphicIdIntro_Id, polymorphicIdIntro_refl, Functor.id_obj,
      Category.assoc, δ0_π'_app_assoc, δ1_π'_app_assoc, path_tp', ← Path_comp, weakenId]
    rw! (transparency := .default) [P0.δ0_substConsEv_assoc a a_tp,
      P0.δ0_substConsEv_assoc a a_tp, P0.δ0_substConsEv_assoc a a_tp]
    simp)

@[reassoc (attr := simp)]
lemma δ0_connectionLift : cyl.δ0.app _ ≫ P0.connectionLift hrwcz0 a a_tp =
    disp .. ≫ disp .. ≫ P0.polymorphicIdIntro.refl a a_tp := by
  simp [connectionLift]

lemma connectionLift_comp [hrwcz0.IsUniform] :
    P0.connectionLift hrwcz0 (A := σ ≫ A) (σ ≫ a) (by simp [a_tp]) =
    cyl.I.map (P0.polymorphicIdIntro.motiveSubst σ a a_tp) ≫
    P0.connectionLift hrwcz0 a a_tp := by
  simp only [motiveCtx, polymorphicIdIntro_Id, connectionLift, polymorphicIdIntro_refl,
    Functor.id_obj, ← path_comp, NatTrans.naturality_assoc, Functor.id_map, weakenId, motiveSubst,
    ← Hurewicz.lift_comp, substWk_disp_assoc]
  congr 1
  erw [← P0.substConsEv_comp_substWk_assoc]
  simp [← Path_comp]

lemma I_map_reflInst_comp_connectionLift [hrwcz0.IsUniform] [hrwcz0.IsNormal] :
    cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫ P0.connectionLift hrwcz0 a a_tp =
    P0.path (A := cyl.π.app Γ ≫ A) (cyl.π.app _ ≫ cyl.π.app Γ ≫ a) (by simp [a_tp]) := by
  simp only [connectionLift]
  rw [← Hurewicz.lift_comp]
  rw [hrwcz0.isNormal _ _ _ (U0.sec A a a_tp ≫ P0.Path (A := U0.disp A ≫ A) (U0.disp A ≫ a)
    (U0.var A) (by simp [a_tp]) (by simp))]
  · simp [← path_comp, reflInst, motiveInst]
  · simp [I_map_reflInst_comp_substConsEv_assoc]

/-- Fix `Γ ⊢ a : A`, we think of `connection` as a cubical (as opposed to globular)
homotopy `(i j : I);(x : A)(p : Id(a,x)) ⊢ χ i j : A`
such that `χ 0 j = refl a j` is the reflexive unpath at `a : A` and `χ 1 j = p j`.
These are proven below as `δ0_connection` and `δ1_connection` respectively.
It will also satisfy `χ i 0 = refl a i`, proven in `I_δ0_connection`.
Note that we do not know how the bottom unpath `χ i 1` computes.
```
i→   j↓

a ====== p 0
‖         |
‖    χ    | p j
‖         V
a -----> p 1
```
-/
def connection : cyl.I.obj (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ⟶ U0.Tm :=
  P0.unpath' (A := disp .. ≫ A) (substConsEv ..) (disp .. ≫ a) (var ..) (by simp [a_tp])
    (by simp) (P0.connectionLift hrwcz0 a a_tp) (by simp [connectionLift])

@[simp]
lemma connection_tp : P0.connection hrwcz0 a a_tp ≫ U0.tp =
    cyl.π.app (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ≫
    cyl.π.app (P0.polymorphicIdIntro.motiveCtx a a_tp) ≫
    U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ A := by
  simp [connection]

@[reassoc (attr := simp)]
lemma δ0_connection : cyl.δ0.app _ ≫ P0.connection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  simp [connection]

@[reassoc (attr := simp)]
lemma δ1_connection : cyl.δ1.app _ ≫ P0.connection hrwcz0 a a_tp =
    P0.ev a a_tp := by
  simp [connection, unpath', δ1_unpath', ev]

@[simp]
lemma I_δ0_connection : cyl.I.map (cyl.δ0.app _) ≫ P0.connection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  fapply P0.unpath_ext (disp .. ≫ U0.disp A ≫ A) (disp .. ≫ U0.disp A ≫ a) (disp .. ≫ U0.disp A ≫ a)
    <;> simp [a_tp, connection, ← unpath_comp]
  erw [δ0_connectionLift] -- FIXME
  simp [← path_comp]

lemma connection_comp [hrwcz0.IsUniform] :
    P0.connection hrwcz0 (A := σ ≫ A) (σ ≫ a) (by simp [a_tp]) =
    cyl.I.map (cyl.I.map (P0.polymorphicIdIntro.motiveSubst σ a a_tp)) ≫
    P0.connection hrwcz0 (a) a_tp := by
  simp only [connection]
  rw! [connectionLift_comp _ _ _ _ a_tp]
  simp [← unpath_comp, motiveSubst]

lemma I_map_I_map_reflInst_comp_connection [hrwcz0.IsUniform] [hrwcz0.IsNormal] :
    cyl.I.map (cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp)) ≫ P0.connection hrwcz0 a a_tp =
    cyl.π.app (cyl.I.obj Γ) ≫ cyl.π.app Γ ≫ a := by
  simp only [connection, unpath']
  fapply P0.unpath_ext
    (cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫ P0.substConsEv a a_tp ≫ U0.disp A ≫ A)
    (cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫ P0.substConsEv a a_tp ≫ U0.disp A ≫ a)
    (cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫ P0.substConsEv a a_tp ≫ U0.var A)
    <;> simp [a_tp, ← unpath_comp, reflInst, motiveInst]
  erw [I_map_reflInst_comp_connectionLift]

/-- `symmConnection` is the symmetrically flipped homotopy `j i ⊢ χ i j` (of `connection`),
visualised as
```
j→   i↓

a ======  a
‖         |
‖    χ    | χ i 1
‖         V
p 0 ----> p 1
    p j
```
Note that we know the left unpath is `χ i 0 = refl a i`
but we do not know how the right unpath `χ i 1` computes.
We need to switch the indices using `cyl.symm` since
1. we need to do unpath lifting in the `j` direction (i.e. starting at `χ i 0 = refl a i`)
2. we ultimately want a homotopy in the `i` direction (i.e. from `χ 0 j` to `χ 1 j`)
-/
def symmConnection := cyl.symm.app _ ≫ P0.connection hrwcz0 a a_tp

@[simp]
lemma symmConnection_tp : P0.symmConnection hrwcz0 a a_tp ≫ U0.tp =
    cyl.π.app (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ≫
    cyl.π.app (P0.polymorphicIdIntro.motiveCtx a a_tp) ≫
    U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ A := by
  simp [symmConnection, symm_π_π'_app_assoc]

@[simp]
lemma δ0_symmConnection : cyl.δ0.app _ ≫ P0.symmConnection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  simp only [motiveCtx, polymorphicIdIntro_Id, Functor.id_obj, symmConnection, Functor.comp_obj,
    δ0_app_I_obj_comp_symm_app_assoc]
  erw [I_δ0_connection] -- FIXME
  simp

@[simp]
lemma I_δ0_symmConnection : cyl.I.map (cyl.δ0.app _) ≫ P0.symmConnection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  simp only [motiveCtx, Functor.id_obj, symmConnection, Functor.comp_obj,
    I_map_δ0_app_comp_symm_app_assoc]
  erw [δ0_connection] -- FIXME

@[simp]
lemma I_δ1_symmConnection : cyl.I.map (cyl.δ1.app _) ≫ P0.symmConnection hrwcz0 a a_tp =
    P0.ev a a_tp := by
  simp only [motiveCtx, polymorphicIdIntro_Id, Functor.id_obj, symmConnection, Functor.comp_obj,
    I_map_δ1_app_comp_symm_app_assoc]
  erw [δ1_connection] -- FIXME

lemma I_map_I_map_reflInst_comp_symmConnection [hrwcz0.IsUniform] [hrwcz0.IsNormal] :
    cyl.I.map (cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp)) ≫
    P0.symmConnection hrwcz0 a a_tp = cyl.π.app (cyl.I.obj Γ) ≫ cyl.π.app Γ ≫ a := by
  simp only [symmConnection]
  erw [cyl.symm.naturality_assoc]
  simp [I_map_I_map_reflInst_comp_connection, symm_π_π'_app_assoc]

lemma symmConnection_comp [hrwcz0.IsUniform] :
    P0.symmConnection hrwcz0 (A := σ ≫ A) (σ ≫ a) (by simp [a_tp]) =
    cyl.I.map (cyl.I.map (P0.polymorphicIdIntro.motiveSubst σ a a_tp)) ≫
    P0.symmConnection hrwcz0 a a_tp := by
  have := cyl.symm.naturality_assoc
  simp at this
  simp [symmConnection, connection_comp _ _ _ _ a_tp, ← this]

/-- An auxiliary definition for `substConnection`. -/
def pathSymmConnection : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.Tm :=
 P0.path (Γ := cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp))
  (A := cyl.π.app _ ≫ disp .. ≫ disp .. ≫ A) (P0.symmConnection hrwcz0 a a_tp)
  (by simp)

@[simp]
lemma pathSymmConnection_tp : P0.pathSymmConnection hrwcz0 a a_tp ≫ U0.tp =
    P0.Path (A := cyl.π.app _ ≫ disp .. ≫ disp .. ≫ A)
    (cyl.π.app _ ≫ disp .. ≫ disp .. ≫ a) (cyl.δ1.app _ ≫ P0.symmConnection hrwcz0 a a_tp)
    (by simp [a_tp]) (by simp) := by
  simp [pathSymmConnection]
  rw! (transparency := .default) [δ0_symmConnection]
  congr 1

@[simp]
lemma δ0_pathSymmConnection : cyl.δ0.app _ ≫ P0.pathSymmConnection hrwcz0 a a_tp =
    disp .. ≫ disp .. ≫ P0.polymorphicIdIntro.refl a a_tp := by
  simp only [polymorphicIdIntro_Id, Functor.id_obj, pathSymmConnection, motiveCtx, ← path_comp,
    δ0_π'_app_assoc, polymorphicIdIntro_refl, NatTrans.naturality_assoc, Functor.id_map]
  rw! (transparency := .default) [I_δ0_symmConnection]
  simp

@[simp]
lemma δ1_pathSymmConnection : cyl.δ1.app _ ≫ P0.pathSymmConnection hrwcz0 a a_tp =
    U0.var _ := by
  simp only [polymorphicIdIntro_Id, Functor.id_obj, pathSymmConnection, motiveCtx, ← path_comp,
    δ1_π'_app_assoc]
  rw! (transparency := .default) [I_δ1_symmConnection]
  simp

lemma pathSymmConnection_comp [hrwcz0.IsUniform] :
    P0.pathSymmConnection hrwcz0 (A := σ ≫ A) (σ ≫ a) (by simp [a_tp]) =
    cyl.I.map (U0.substWk (U0.substWk σ _ _ rfl) _ _ (by rw [weakenId_comp])) ≫
    P0.pathSymmConnection hrwcz0 a a_tp := by
  simp [pathSymmConnection, ← path_comp, symmConnection_comp _ _ _ _ a_tp, motiveSubst]

lemma I_map_reflInst_comp_pathSymmConnection [hrwcz0.IsUniform] [hrwcz0.IsNormal] :
    cyl.I.map (P0.polymorphicIdIntro.reflInst a a_tp) ≫ P0.pathSymmConnection hrwcz0 a a_tp =
    cyl.π.app Γ ≫ P0.path (A := A) (cyl.π.app Γ ≫ a) (by simp [a_tp]) := by
  simp only [pathSymmConnection, ← path_comp]
  congr 1
  · simp [reflInst, motiveInst]
  · simp [I_map_I_map_reflInst_comp_symmConnection]

/-- Fixing `Γ ⊢ a : A`, `substConnection` is thought of as a substitution
`(i : I); (x : A) (p : Id(a,x)) ⊢ (α i : A, β i : Id (a, α i))`
such that at the start and end-points we have
`(α 0, β 0) = (a, refl a)` and `(α 1, β 1) = (x, p)`.
These equations are `δ0_substConnection` and `δ1_substConnection`, proven below. -/
def substConnection : cyl.I.obj (U0.ext ((polymorphicIdIntro P0).weakenId a a_tp)) ⟶
    P0.polymorphicIdIntro.motiveCtx a a_tp :=
  let χi1 : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.Tm :=
    (cyl.δ1.app _ ≫ P0.symmConnection hrwcz0 a a_tp)
  -- the unpath `i ⊢ χ i 1 : A` is the endpoint of the homotopy `symmConnection`
  -- that we cannot compute
  let toΓ : cyl.I.obj (U0.ext ((polymorphicIdIntro P0).weakenId a a_tp)) ⟶ Γ :=
    cyl.π.app _ ≫ disp .. ≫ disp ..
  let toExtA : cyl.I.obj (U0.ext ((polymorphicIdIntro P0).weakenId a a_tp)) ⟶ U0.ext A :=
    U0.substCons toΓ A χi1 (by aesop_cat)
  U0.substCons toExtA (P0.polymorphicIdIntro.weakenId a a_tp)
    (P0.pathSymmConnection hrwcz0 a a_tp) (by
    simp [pathSymmConnection_tp, toExtA, toΓ, χi1, ← Path_comp])

@[simp]
lemma substConnection_var : P0.substConnection hrwcz0 a a_tp ≫ var .. =
    P0.pathSymmConnection hrwcz0 a a_tp := by
  simp [substConnection]

@[reassoc (attr := simp)]
lemma δ0_substConnection : cyl.δ0.app _ ≫ P0.substConnection hrwcz0 a a_tp =
    disp .. ≫ disp .. ≫ reflInst _ a a_tp := by
  simp only [polymorphicIdIntro_Id, Functor.id_obj, motiveCtx, substConnection, comp_substCons,
    δ0_π'_app_assoc, ← cyl.δ1_naturality_assoc, polymorphicIdIntro_refl]
  rw! (transparency := .default) [δ0_pathSymmConnection]
  apply (disp_pullback ..).hom_ext
  · simp
  · apply (disp_pullback ..).hom_ext
    · simp only [substCons_disp, substCons_var, Category.assoc, sec_var]
      rw! (transparency := .default) [I_δ0_symmConnection]
      simp
    · simp

@[reassoc (attr := simp)]
lemma δ1_substConnection : cyl.δ1.app _ ≫ P0.substConnection hrwcz0 a a_tp = 𝟙 _ := by
  simp [substConnection]
  apply (disp_pullback ..).hom_ext
  · simp only [substCons_var, Category.id_comp]
    rw! (transparency := .default) [δ1_pathSymmConnection]
    simp
  · apply (disp_pullback ..).hom_ext
    · simp only [symmConnection, motiveCtx, polymorphicIdIntro_Id, Functor.comp_obj,
        δ1_app_I_obj_comp_symm_app_assoc, cyl.δ1_naturality_assoc]
      rw! (transparency := .default) [δ1_connection]
      simp
    · simp

@[reassoc]
lemma substConnection_comp_motiveSubst [hrwcz0.IsUniform] :
    P0.substConnection hrwcz0 (σ ≫ a) (by simp [a_tp]) ≫ motiveSubst _ σ a a_tp rfl =
    cyl.I.map (motiveSubst _ σ a a_tp) ≫ P0.substConnection hrwcz0 a a_tp := by
  simp only [polymorphicIdIntro_Id, motiveCtx, motiveSubst]
  apply (disp_pullback ..).hom_ext
  · simp only [Category.assoc, substWk_var]
    erw [substConnection_var]
    simp [substConnection, pathSymmConnection_comp _ _ _ _ a_tp]
  · apply (disp_pullback ..).hom_ext
    · simp [substConnection, symmConnection_comp _ _ _ _ a_tp, δ1_naturality_assoc, motiveSubst]
    · simp [substConnection]

/-- `substConnection` is *normal*. -/
@[reassoc]
lemma reflInst_comp_substConnection [hrwcz0.IsUniform] [hrwcz0.IsNormal] :
    cyl.I.map (reflInst _ a a_tp) ≫
    P0.substConnection hrwcz0 a a_tp = cyl.π.app _ ≫ reflInst _ a a_tp := by
  simp only [substConnection]
  apply (disp_pullback ..).hom_ext
  · simp [I_map_reflInst_comp_pathSymmConnection]
  · apply (disp_pullback ..).hom_ext
    · simp [← δ1_naturality_assoc, I_map_I_map_reflInst_comp_symmConnection]
    · simp [reflInst, motiveInst]

end connection

def polymorphicIdElim (hrwcz0 : Hurewicz cyl U0.tp) [hrwcz0.IsUniform] [hrwcz0.IsNormal]
    (U1 : UnstructuredUniverse Ctx) (hrwcz1 : Hurewicz cyl U1.tp) [Hurewicz.IsUniform hrwcz1]
    [Hurewicz.IsNormal hrwcz1] : PolymorphicIdElim (polymorphicIdIntro P0) U1 where
  jElim a a_tp C c c_tp := cyl.δ1.app _ ≫ hrwcz1.lift (disp .. ≫ disp .. ≫ c)
    (substConnection P0 hrwcz0 a a_tp ≫ C) (by rw [δ0_substConnection_assoc]; simp [c_tp]) -- FIXME simp failed
  jElim_comp σ A a a_tp C c c_tp := by
    slice_rhs 1 2 => rw [← δ1_naturality]
    slice_rhs 2 3 => rw [← hrwcz1.lift_comp]
    congr 2
    · simp [motiveSubst, substWk_disp_assoc]
    · rw [substConnection_comp_motiveSubst_assoc]
  jElim_tp a a_tp C c c_tp := by
    simp only [motiveCtx, polymorphicIdIntro_Id, Category.assoc, Hurewicz.lift_comp_self']
    erw [δ1_substConnection_assoc] -- FIXME simp, rw failed
  reflSubst_jElim {Γ A} a a_tp C c c_tp := calc _
    _ = cyl.δ1.app Γ ≫ cyl.I.map (reflInst _ a a_tp) ≫
        hrwcz1.lift (U0.disp (weakenId _ a a_tp) ≫ U0.disp A ≫ c)
        (P0.substConnection hrwcz0 a a_tp ≫ C) _ := by
      rw [← δ1_naturality_assoc]
    _ = cyl.δ1.app Γ ≫
    hrwcz1.lift
      (reflInst _ a a_tp ≫ disp .. ≫ disp .. ≫ c)
      (cyl.I.map (reflInst _ a a_tp) ≫ P0.substConnection hrwcz0 a a_tp ≫ C) _ := by
      rw [← Hurewicz.lift_comp]
    _ = cyl.δ1.app Γ ≫ cyl.π.app Γ ≫ P0.polymorphicIdIntro.reflInst a a_tp ≫
        U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ c := by
      rw [Hurewicz.isNormal hrwcz1 _ _ _ (P0.polymorphicIdIntro.reflInst a a_tp ≫ C)]
      rw [reflInst_comp_substConnection_assoc]
    _ = c := by simp [reflInst, motiveInst]

end PathType
