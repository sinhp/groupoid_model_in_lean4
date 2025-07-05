import GroupoidModel.ForMathlib

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace NatTrans

section
variable {A : Type u} [Category.{v} A] {B: Type u₁} [Groupoid.{v₁} B]
    {F G : A ⥤ B} (h : NatTrans F G)

-- NOTE not sure if this is the best way to organize this
@[simps] def isoOfCodGroupoid : F ≅ G where
  hom := h
  inv := {app a := Groupoid.inv (h.app a)}

def inv : G ⟶ F := h.isoOfCodGroupoid.inv

@[simp] lemma inv_vcomp : h.inv.vcomp h = NatTrans.id G := by
  ext a
  simp [NatTrans.inv]

@[simp] lemma vcomp_inv : h.vcomp h.inv = NatTrans.id F := by
  ext a
  simp [NatTrans.inv]

end
end NatTrans

instance {A : Type*} [Category A] {B : Type*} [Groupoid B] :
    Groupoid (A ⥤ B) where
  inv nt := nt.inv
  inv_comp := NatTrans.inv_vcomp
  comp_inv := NatTrans.vcomp_inv

end CategoryTheory
