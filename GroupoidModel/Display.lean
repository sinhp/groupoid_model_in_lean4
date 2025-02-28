import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Adjunction.Over
import Poly.LCCC.Presheaf
import Poly.UvPoly
import GroupoidModel.Tarski.NaturalModel

-- (SH) TODO: Make the proof and construction work with `Disp` rather than `Disp'`.

universe u

open CategoryTheory Category Limits

noncomputable section

variable {C : Type u} [Category C] [HasTerminal C] [HasPullbacks C]

variable {𝔼 𝕌 : C} (π : 𝔼 ⟶ 𝕌)

class DisplayStruct {D A : C} (p : D ⟶ A) where
  char : A ⟶ 𝕌
  var : D ⟶ 𝔼
  disp_pullback : IsPullback var p π char

def IsDisplay : MorphismProperty C  :=
  fun D A (p : D ⟶ A) ↦ Nonempty (DisplayStruct π p)

structure Disp' where
  T : C
  B : C
  p : T ⟶ B
  disp : DisplayStruct π p := by infer_instance

variable (C) in

/-- `Cart C` is a typeclass synonym for `Arrow C` which comes equipped with
a cateogry structure whereby morphisms between arrows `p` and `q` are cartesian
squares between them. -/
abbrev Cart := Arrow C

@[simp]
lemma IsPullback.of_horiz_id {X Y : C} (f : X ⟶ Y) : IsPullback (𝟙 X) f f (𝟙 Y) := by
  apply IsPullback.of_horiz_isIso
  simp only [CommSq.mk, id_comp, comp_id]

instance : Category (Cart C) where
  Hom p q := { v : p ⟶ q // IsPullback v.left p.hom q.hom v.right}
  id p := ⟨ ⟨𝟙 _, 𝟙 _, by simp⟩, IsPullback.of_horiz_id p.hom⟩
  comp {p q r} u v := ⟨⟨u.1.left ≫ v.1.left, u.1.right ≫ v.1.right, by simp⟩,
    IsPullback.paste_horiz u.2 v.2⟩
  id_comp {p q} f:= by
    simp only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, id_comp]
    rfl -- we can replace by aesop, but they are a bit slow
  comp_id {p q} f := by
    simp only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, comp_id]
    rfl
  assoc {p q r s} f g h := by
    simp_all only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, assoc]

def WideSubcategory (C) [Category C] := WideSubquiver C

def displayStructPresheaf : (Cart C)ᵒᵖ  ⥤ Type u where
  obj p := DisplayStruct π p.unop.hom
  map {p q} f := fun d ↦ ⟨f.unop.1.right ≫ d.char , f.unop.1.left ≫ d.var, by
    apply IsPullback.paste_horiz f.unop.2 d.disp_pullback⟩
  map_id := by sorry
  map_comp := by sorry

abbrev Disp := ((displayStructPresheaf π).Elements)ᵒᵖ

def forget : Disp π ⥤ Cart C :=
(CategoryOfElements.π (displayStructPresheaf π)).leftOp

namespace DisplayStruct

structure Hom {D A E B : C} (p : D ⟶ A) [i : DisplayStruct π p]
    (q : E ⟶ B) [j : DisplayStruct π q] where
  base : B ⟶ A
  base_eq : base ≫ i.char = j.char

instance category : Category (Disp' π) where
  Hom P Q :=  {t : P.B ⟶ Q.B // (t ≫ Q.disp.char) = P.disp.char}
  id (P : Disp' π) := ⟨𝟙 P.B, by simp only [id_comp]⟩
  comp {P Q R : Disp' π} f g := ⟨f.1 ≫ g.1, by simp only [assoc, f.2, g.2]⟩

/-- A morphism of display maps is necessarily cartesian: The cartesian square is obtained by the
pullback pasting lemma. -/
theorem is_cartesian {Q P : Disp' π} (f : Q ⟶ P) :
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
    DisplayStruct p q  where -- should be changed to a morphism from Disp'.mk p to Disp'.mk q
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
    DisplayStruct π (pullback.snd p t) where
  char := t ≫ i.char
  var := pullback.fst .. ≫ i.var
  disp_pullback := IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) i.disp_pullback

end DisplayStruct

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]

open NaturalModel in

instance [NaturalModelBase Ctx] (Γ : Ctx) (A : y(Γ) ⟶ Ty) :
    DisplayStruct tp (yoneda.map (disp Γ A)) where
  char := A
  var := var Γ A
  disp_pullback := disp_pullback A
