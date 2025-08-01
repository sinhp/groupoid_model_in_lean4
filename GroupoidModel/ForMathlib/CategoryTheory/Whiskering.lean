import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EqToHom

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

section
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

@[simp]
theorem whiskerLeft_eqToHom (F : C ⥤ D) {G H : D ⥤ E} (η : G = H) :
    whiskerLeft F (eqToHom η) = eqToHom (by cases η; rfl) := by
  cases η
  simp only [whiskerLeft_id', eqToHom_refl]

@[simp]
theorem eqToHom_whiskerRight {F G : C ⥤ D} (η : F = G) (H : D ⥤ E) :
    whiskerRight (eqToHom η) H = eqToHom (by cases η; rfl) := by
  cases η
  simp only [whiskerRight_id', eqToHom_refl]

end

section


variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  (F : C ⥤ A) (G : B ⥤ D)

/--
The functor that, on objects `H : A ⥤ B` acts by
composing left and right with functors `F ⋙ H ⋙ G`
         F
   A <---------  C
   |             .
   |             |
   |             .
H  |             | whiskeringLeftObjWhiskeringRightObj.obj H
   |             .
   V             V
   B ----------> D
         G
-/
def whiskeringLeftObjWhiskeringRightObj : (A ⥤ B) ⥤ (C ⥤ D) :=
  (whiskeringLeft C A B).obj F ⋙ (whiskeringRight C B D).obj G

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_obj (S : A ⥤ B) :
    (whiskeringLeftObjWhiskeringRightObj F G).obj S
    = F ⋙ S ⋙ G := by
  simp [whiskeringLeftObjWhiskeringRightObj, Functor.assoc]

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_map {S1 S2 : A ⥤ B} (η : S1 ⟶ S2) :
    (whiskeringLeftObjWhiskeringRightObj F G).map η
    = whiskerRight (F.whiskerLeft η) G := by
  simp [whiskeringLeftObjWhiskeringRightObj]

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_id_id :
    whiskeringLeftObjWhiskeringRightObj (𝟭 A) (𝟭 B) = 𝟭 (A ⥤ B) :=
  rfl

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_comp_comp {C' D' : Type*} [Category C']
    [Category D'] (F' : C' ⥤ C) (G' : D ⥤ D') :
    whiskeringLeftObjWhiskeringRightObj (F' ⋙ F) (G ⋙ G')
    = whiskeringLeftObjWhiskeringRightObj F G ⋙ whiskeringLeftObjWhiskeringRightObj F' G' :=
  rfl

end

end CategoryTheory.Functor
