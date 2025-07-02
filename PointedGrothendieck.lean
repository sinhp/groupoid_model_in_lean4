import GroupoidModel.Grothendieck.Groupoidal
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

noncomputable section GrothendieckPointedCategories

namespace GrothendieckPointedCategories

def PCat := Grothendieck (Functor.id (Cat.{v,u}))

instance : Category.{max v u} PCat.{v,u} :=
  inferInstanceAs (Category <| Grothendieck ..)

def PCat.of (C : Type u) [Category.{v} C] (pt : C) : PCat := {base := Cat.of C, fiber := pt}

def PCat.Lift {C : Type} [Category C] {c1 c2 : C} (f : c1 ⟶ c2) : (PCat.of C c1) ⟶ (PCat.of C c2) := {base := Functor.id C, fiber := f}

-- factor with ι
def PCat.inc {C : Type} [Category C] : C ⥤ PCat where
  obj x := PCat.of C x
  map f := PCat.Lift f
  map_comp f g := by
    simp[Lift,CategoryStruct.comp,Grothendieck.comp]
    congr

def PCatFunc.of {C D: Type u} [Category.{v} C] [Category.{v} D]
  (Cpt : C) (Dpt : D) (F : C ⥤ D) (f : F.obj Cpt ⟶ Dpt)
  : (PCat.of C Cpt) ⟶ (PCat.of D Dpt) := {base := F, fiber := f}

def PCat.ForgetToCat : PCat ⥤ Cat := Grothendieck.forget (Functor.id (Cat.{v,u}))

def PCat.pt (P : PCat) : PCat.ForgetToCat.obj P := P.fiber

@[simp]
theorem PCatFunc.comp {C D E: Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E] (Cpt : C) (Dpt : D) (Ept : E) (F : C ⥤ D) (G : D ⥤ E) (f : F.obj Cpt ⟶ Dpt) (g : G.obj Dpt ⟶ Ept)
  : (PCatFunc.of Cpt Dpt F f) ≫ (PCatFunc.of Dpt Ept G g) = PCatFunc.of Cpt Ept (F ⋙ G) ((G.map f) ≫ g) := by
  simp [PCatFunc.of,CategoryStruct.comp,Grothendieck.comp]

def PCat.var (C : Type u₁) [Category.{v₁} C] (F : C ⥤ Cat.{v₂,u₂}) : Grothendieck F ⥤ PCat := Grothendieck.pre (Functor.id (Cat)) F

theorem PCat.comm {C : Type} [Category C] (F : C ⥤ Cat) : PCat.var C F ⋙ PCat.ForgetToCat = Grothendieck.forget F ⋙ F := rfl

def GetPointInCat {C : Type} [Category C] (F : C ⥤ Cat) (L : C ⥤ PCat) (x : C) (h : L ⋙ PCat.ForgetToCat = F) : F.obj x := by
  cases h
  exact (L.obj x).fiber

def PointToSec {C : Type} [Category C] (F : C ⥤ Cat) (L : C ⥤ PCat) (h : L ⋙ PCat.ForgetToCat = F) : C ⥤ Grothendieck F where
  obj x := {base := x, fiber := GetPointInCat F L x h}
  map {x y}f := by
    refine {base := f, fiber := ?_}
    . cases h
      exact (L.map f).fiber
  map_id x := sorry
  map_comp {x y z}f g := sorry

-- def UP {C X: Type} [Category C] [Category X] (F : C ⥤ Cat) (top : X ⥤ PCat) (left : X ⥤ C) (h : top ⋙ PCat.ForgetToCat = left ⋙ F ) : X ⥤ Grothendieck F where
--   obj x:= by
--     refine {base := (left.obj x), fiber := ?_}
--     . have rw1 := (CategoryTheory.Functor.congr_obj h x).symm
--       dsimp at rw1
--       rw[rw1]
--       exact (top.obj x).pt
--   map {x y}f := by
--     refine {base := left.map f, fiber := ?_}
--     . simp
--       have f' := PCat.ForgetToCat.map (top.map f)
--       have rwl : (F.map (left.map f)).obj (cast _ (top.obj x).pt) = (top.obj x).fiber := by

-- def UP.unic {C X: Type} [Category C] [Category X] (F : C ⥤ Cat) (U1 U2 : X ⥤ Grothendieck F) (htop : U1 ⋙ PCat.var C F  = U2 ⋙ PCat.var C F) (hleft : U1 ⋙ Grothendieck.forget F = U2 ⋙ Grothendieck.forget F) : U1 = U2 := by
--   refine (Functor.ext ?_ ?_)
--   . intro x
--     refine Grothendieck.obj_ext_hEq (CategoryTheory.Functor.congr_obj hleft x) ?_
--     . have h1 := (CategoryTheory.Functor.congr_obj htop x)
--       simp[PCat.var,Grothendieck.pre] at h1
--       sorry
--   . intros x y f
