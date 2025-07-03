import Mathlib.CategoryTheory.Whiskering

namespace CategoryTheory
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

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_id_id :
    whiskeringLeftObjWhiskeringRightObj (𝟭 A) (𝟭 B) = 𝟭 (A ⥤ B) :=
  rfl

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_comp_comp {C' D' : Type*} [Category C']
    [Category D'] (F' : C' ⥤ C) (G' : D ⥤ D') :
    whiskeringLeftObjWhiskeringRightObj (F' ⋙ F) (G ⋙ G')
    = whiskeringLeftObjWhiskeringRightObj F G ⋙ whiskeringLeftObjWhiskeringRightObj F' G' :=
  rfl

end

end CategoryTheory
