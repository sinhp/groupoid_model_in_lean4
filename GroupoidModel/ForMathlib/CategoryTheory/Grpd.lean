import GroupoidModel.ForMathlib

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace Grpd

open Limits

/-- The chosen terminal object in `Grpd`. -/
abbrev chosenTerminal : Grpd.{u,u} := Grpd.of (Discrete.{u} PUnit)

/-- The chosen terminal object in `Grpd` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal :=
  IsTerminal.ofUniqueHom (fun _ ↦ (Functor.const _).obj ⟨⟨⟩⟩) fun _ _ ↦ rfl

/-- The chosen product of categories `C × D` yields a product cone in `Grpd`. -/
def prodCone (C D : Grpd.{u,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Grpd` is indeed a product. -/
def isLimitProdCone (X Y : Grpd) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => S.fst.prod' S.snd) (fun _ => rfl) (fun _ => rfl) (fun A B h1 h2 =>
    Functor.hext
      (fun x ↦ Prod.ext (by dsimp; rw [← h1]; rfl)
      (by dsimp; rw [← h2]; rfl))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : CartesianMonoidalCategory Grpd :=
  .ofChosenFiniteProducts
    { cone := asEmptyCone chosenTerminal
      isLimit := chosenTerminalIsTerminal }
    (fun X Y => {
      cone := prodCone X Y
      isLimit := isLimitProdCone X Y })

/-- The identity in the category of groupoids equals the identity functor.-/
theorem id_eq_id (X : Grpd) : 𝟙 X = 𝟭 X := rfl

-- NOTE this is currently called `Grpd.hom_to_functor` in mathlib,
-- but this naming is inconsistent with that of `Cat`
/-- Composition in the category of groupoids equals functor composition.-/
theorem comp_eq_comp {X Y Z : Grpd} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

theorem eqToHom_obj
  {C1 C2 : Grpd.{v,u}} (x : C1) (eq : C1 = C2) :
    (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp [id_eq_id]

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}

@[simp] theorem map_id_obj {x : Γ} {a : A.obj x} :
    (A.map (𝟙 x)).obj a = a := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_obj this a

@[simp] theorem map_id_map
    {x : Γ} {a b : A.obj x} {f : a ⟶ b} :
    (A.map (𝟙 x)).map f = eqToHom Grpd.map_id_obj
      ≫ f ≫ eqToHom Grpd.map_id_obj.symm := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_hom this f

@[simp] theorem map_comp_obj
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a : A.obj x} :
    (A.map (f ≫ g)).obj a = (A.map g).obj ((A.map f).obj a) := by
  have : A.map (f ≫ g) = A.map f ⋙ A.map g := by
    simp [Grpd.comp_eq_comp]
  have h := Functor.congr_obj this a
  simp only [Functor.comp_obj] at h
  exact h

@[simp] theorem map_comp_map
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map (f ≫ g)).map φ
    = eqToHom Grpd.map_comp_obj ≫ (A.map g).map ((A.map f).map φ)
    ≫ eqToHom Grpd.map_comp_obj.symm := by
  have : A.map (f ≫ g) = A.map f ≫ A.map g := by simp
  exact Functor.congr_hom this φ

theorem map_comp_map'
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map g).map ((A.map f).map φ)
    = eqToHom Grpd.map_comp_obj.symm ≫ (A.map (f ≫ g)).map φ ≫ eqToHom Grpd.map_comp_obj
    := by
  simp [Grpd.map_comp_map]
end

@[simp] theorem id_obj {C : Grpd} (X : C) :
    (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp] theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E)
    (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

variable {Γ : Type u} [Category.{v} Γ] (F : Γ ⥤ Grpd.{v₁,u₁})

theorem map_eqToHom_obj {x y : Γ} (h : x = y) (t) :
    (F.map (eqToHom h)).obj t = cast (by rw [h]) t := by
  subst h
  simp

/-- This is the proof of equality used in the eqToHom in `Grpd.eqToHom_hom` -/
theorem eqToHom_hom_aux {C1 C2 : Grpd.{v,u}} (x y: C1) (eq : C1 = C2) :
    (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem eqToHom_hom {C1 C2 : Grpd.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (Grpd.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp only [eqToHom_refl, id_eq_id, Functor.id_map, cast_eq]

@[simp] theorem map_eqToHom_map {x y : Γ} (h : x = y) {t s} (f : t ⟶ s) :
    (F.map (eqToHom h)).map f =
    eqToHom (Functor.congr_obj (eqToHom_map _ _) t)
    ≫ cast (Grpd.eqToHom_hom_aux t s (by rw [h])) f
    ≫ eqToHom (Eq.symm (Functor.congr_obj (eqToHom_map _ _) s)) := by
  have h1 : F.map (eqToHom h) = eqToHom (by rw [h]) := eqToHom_map _ _
  rw [Functor.congr_hom h1, Grpd.eqToHom_hom]

@[simp] theorem eqToHom_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F G : C ⥤ D) (h : F = G) (X : C) :
    (eqToHom h).app X = eqToHom (by subst h; rfl) := by
  subst h
  simp

end Grpd
end CategoryTheory
