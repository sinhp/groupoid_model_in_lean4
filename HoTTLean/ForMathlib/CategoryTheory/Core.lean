import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.Tactic.CategoryTheory.Coherence
import HoTTLean.ForMathlib.CategoryTheory.Functor.IsPullback
import HoTTLean.ForMathlib.CategoryTheory.Grpd

universe w v u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory
namespace Core

@[ext]
theorem obj_ext {C : Type*} {X Y : Core C} (h : X.of = Y.of) :
    X = Y := by
  cases X
  cases h
  rfl

@[simp]
theorem eqToHom_iso {C : Type*} [Category C] {X Y : Core C} (h : X = Y) :
    (eqToHom h).iso = eqToIso (by subst h; rfl) := by
  subst h
  rfl

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- Compatibility alias for the upstream `Functor.core_comp_inclusion`. -/
lemma core_comp_inclusion (F : C ⥤ D) :
    F.core ⋙ inclusion D = inclusion C ⋙ F :=
  Functor.core_comp_inclusion F

def comp_inclusion_injective {E : Type w} [Category E] {l0 l1 : E ⥤ Core C}
    (hl : l0 ⋙ inclusion C = l1 ⋙ inclusion C) : l0 = l1 := by
  fapply Functor.ext
  · intro x
    ext
    exact Functor.congr_obj hl x
  · intro x y f
    apply (inclusion C).map_injective
    convert Functor.congr_hom hl f using 1
    rw [Functor.map_comp, Functor.map_comp]
    cat_disch

/-- Functors from a groupoid to a category are equivalently functors into its core. -/
def functorToCoreEquiv {G : Type w} [Groupoid G] {C : Type u} [Category.{v} C] :
    (G ⥤ C) ≃ (G ⥤ Core C) where
  toFun F := functorToCore F
  invFun F := F ⋙ inclusion C
  left_inv F := by
    apply Functor.hext
    · intro X; rfl
    · intro X Y f; rfl
  right_inv F := by
    apply comp_inclusion_injective
    apply Functor.hext
    · intro X; rfl
    · intro X Y f; rfl

@[simp] lemma functorToCoreEquiv_apply {G : Type w} [Groupoid G]
    {C : Type u} [Category.{v} C] (F : G ⥤ C) :
    functorToCoreEquiv F = functorToCore F := rfl

lemma functorToCore_comp_inclusion {G : Type w} [Groupoid G]
    {C : Type u} [Category.{v} C] (F : G ⥤ C) :
    functorToCore F ⋙ inclusion C = F := by
  apply Functor.hext
  · intro X; rfl
  · intro X Y f; rfl

/-- The core construction as a functor from categories to groupoids. -/
def map : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := F.toFunctor.core
  map_id C := by
    exact Functor.ext_of_iso (Functor.coreId C) (by cat_disch)
  map_comp F G := by
    exact Functor.ext_of_iso (Functor.coreComp F.toFunctor G.toFunctor) (by cat_disch)

namespace IsPullback

variable (F : C ⥤ D) [F.ReflectsIsomorphisms]

variable {E : Type w} [Category E] (En : E ⥤ C) (Ew : E ⥤ Core D)
  (hE : En ⋙ F = Ew ⋙ inclusion D)

def lift : E ⥤ Core C where
  obj x := ⟨En.obj x⟩
  map {x y} f := ⟨@asIso _ _ _ _ (En.map f) <| by
    let f' : F.obj (En.obj x) ≅ F.obj (En.obj y) :=
      (eqToIso hE).app x ≪≫ (Ew.map f).iso ≪≫ (eqToIso hE.symm).app y
    have hnat : F.map (En.map f) ≫ _ = _ ≫ (inclusion D).map (Ew.map f) :=
      (eqToHom hE).naturality f
    have h : F.map (En.map f) = f'.hom := by
      rw [← cancel_mono ((eqToIso hE).app y).hom]
      simpa [f', Category.assoc] using hnat
    have : IsIso (F.map (En.map f)) := by
      rw [h]
      exact Iso.isIso_hom f'
    exact Functor.ReflectsIsomorphisms.reflects F (En.map f)⟩

def fac_left : lift F En Ew hE ⋙ inclusion C = En := rfl

def fac_right : lift F En Ew hE ⋙ F.core = Ew := by
  fapply Functor.ext
  · intro x
    ext
    exact Functor.congr_obj hE x
  · intro x y f
    apply (inclusion D).map_injective
    convert Functor.congr_hom hE f using 1
    rw [Functor.map_comp, Functor.map_comp]
    cat_disch

def universal : (lift : E ⥤ Core C) ×'
    lift ⋙ inclusion C = En ∧ lift ⋙ F.core = Ew ∧
      ∀ {l0 l1 : E ⥤ Core C},
        l0 ⋙ inclusion C = l1 ⋙ inclusion C →
          l0 ⋙ F.core = l1 ⋙ F.core → l0 = l1 :=
  ⟨lift F En Ew hE, fac_left _ _ _ _, fac_right _ _ _ _,
    fun hl _ => comp_inclusion_injective hl⟩

end IsPullback

open IsPullback

/--
In `Cat`, if a functor `F : C ⥤ D` reflects isomorphisms, then taking cores is
pullback-stable along `F`.
-/
def isPullback_map'_self (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    Functor.IsPullback (inclusion C) F.core F (inclusion D) :=
  Functor.IsPullback.ofUniversal _ _ _ _ (Functor.core_comp_inclusion F)
    (universal F) (universal F)

end Core
end CategoryTheory
