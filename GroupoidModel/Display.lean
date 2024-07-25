import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Over
import Poly.LCCC.Presheaf
import Poly.Polynomial
import GroupoidModel.NaturalModel

universe u

open CategoryTheory Category Limits

noncomputable section

variable {C : Type u} [Category C] [HasTerminal C] [HasPullbacks C]

variable {E B : C} (π : E ⟶ B)

class DisplayStruct {D A : C} (p : D ⟶ A) where
  char : A ⟶ B
  var : D ⟶ E
  disp_pullback : IsPullback var p π char

def IsDisplay : MorphismProperty C  :=
  fun D A (p : D ⟶ A) ↦ Nonempty (DisplayStruct π p)

structure Disp where
  T : C
  B : C
  p : T ⟶ B
  disp : DisplayStruct π p := by infer_instance

namespace DisplayStruct

structure Hom {D A E B : C} (p : D ⟶ A) [i : DisplayStruct π p]
    (q : E ⟶ B) [j : DisplayStruct π q] where
  base : B ⟶ A
  base_eq : base ≫ i.char = j.char

instance category : Category (Disp π) where
  Hom P Q :=  {t : P.B ⟶ Q.B // (t ≫ Q.disp.char) = P.disp.char}
  id (P : Disp π) := ⟨𝟙 P.B, by simp only [id_comp]⟩
  comp {P Q R : Disp π} f g := ⟨f.1 ≫ g.1, by simp only [assoc, f.2, g.2]⟩

/-- A morphism of display maps is necessarily cartesian: The cartesian square is obtained by the
pullback pasting lemma. -/
theorem is_cartesian {Q P : Disp π} (f : Q ⟶ P) :
    let cone := PullbackCone.mk Q.disp.var (Q.p ≫ f.1) <| by
      rw [Category.assoc, f.2]; exact Q.disp.disp_pullback.w
    IsPullback (P.disp.disp_pullback.isLimit.lift cone) Q.p P.p f.1 := by
  let cone := PullbackCone.mk Q.disp.var (Q.p ≫ f.1) <| by
    rw [Category.assoc, f.2]
    exact Q.disp.disp_pullback.w
  let v := P.disp.disp_pullback.isLimit.lift cone
  have h₁ := P.disp.disp_pullback
  have h₂ := Q.disp.disp_pullback
  have h₃ : v ≫ P.disp.var = Q.disp.var := P.disp.disp_pullback.isLimit.fac cone (some .left)
  rw [← f.2, ← h₃] at h₂
  exact (IsPullback.of_right h₂ (P.disp.disp_pullback.isLimit.fac cone (some .right)) h₁)

def pullback {D A E B : C} (π : E ⟶ B) (p : D ⟶ A) (q : E ⟶ B)
    [i : DisplayStruct π p] [j : DisplayStruct π q]
    (t : B ⟶ A) (h : t ≫ i.char = j.char) :
    DisplayStruct p q  where -- should be changed to a morphism from Disp.mk p to Disp.mk q
  char := t
  var := i.disp_pullback.isLimit.lift <| PullbackCone.mk j.var (q ≫ t) <| by
    rw [Category.assoc, h]
    exact j.disp_pullback.w
  disp_pullback := by
    let c := PullbackCone.mk j.var (q ≫ t) (by rw [Category.assoc, h]; exact j.disp_pullback.w)
    let v := i.disp_pullback.isLimit.lift c
    show IsPullback v ..
    have h₁ := i.disp_pullback
    have h₂ := j.disp_pullback
    have h₃ : v ≫ i.var = j.var := i.disp_pullback.isLimit.fac c (some .left)
    rw [← h, ← h₃] at h₂
    exact (IsPullback.of_right h₂ (i.disp_pullback.isLimit.fac c (some .right)) h₁)

def displayMapOfPullback {D A B : C} (p : D ⟶ A) [i : DisplayStruct π p] (t : B ⟶ A) :
    DisplayStruct π (pullback.snd : Limits.pullback p t ⟶ B) where
  char := t ≫ i.char
  var := pullback.fst ≫ i.var
  disp_pullback := IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) i.disp_pullback

end DisplayStruct

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]

open NaturalModel in

instance [NaturalModelBase Ctx] (Γ : Ctx) (A : y(Γ) ⟶ Ty) :
    DisplayStruct tp (yoneda.map (disp Γ A)) where
  char := A
  var := var Γ A
  disp_pullback := disp_pullback A
