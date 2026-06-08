import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Category.ULift

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

structure Iso (C D : Type*) [Category C] [Category D] where
  hom : C ⥤ D
  inv : D ⥤ C
  hom_inv_id : hom ⋙ inv = 𝟭 _  := by aesop_cat
  inv_hom_id : inv ⋙ hom = 𝟭 _  := by aesop_cat

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅≅ " => Iso -- type as \cong or \iso

variable {X Y Z : Type*} [Category X] [Category Y] [Category Z]

namespace Iso

@[simp]
lemma hom_inv_id_assoc (I : X ≅≅ Y) (H : X ⥤ Z) : I.hom ⋙ I.inv ⋙ H = H := by
  rw [← Functor.assoc, hom_inv_id, Functor.id_comp]

@[simp]
lemma inv_hom_id_assoc (I : X ≅≅ Y) (H : Y ⥤ Z) : I.inv ⋙ I.hom ⋙ H = H := by
  rw [← Functor.assoc, inv_hom_id, Functor.id_comp]

@[simp] lemma hom_inv_id' (I : X ≅≅ Y) : I.hom ⋙ I.inv = 𝟭 _ := I.hom_inv_id

@[simp] lemma inv_hom_id' (I : X ≅≅ Y) : I.inv ⋙ I.hom = 𝟭 _ := I.inv_hom_id

@[ext]
theorem ext ⦃α β : X ≅≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by
    cases α
    cases β
    cases w
    cases this
    rfl
  calc
    α.inv = α.inv ⋙ β.hom ⋙ β.inv   := by rw [Iso.hom_inv_id, Functor.comp_id]
    _     = (α.inv ⋙ α.hom) ⋙ β.inv := by rw [Functor.assoc, ← w]
    _     = β.inv                    := by rw [Iso.inv_hom_id, Functor.id_comp]

theorem ext_inv ⦃α β : X ≅≅ Y⦄ (w : α.inv = β.inv) : α = β :=
  suffices α.hom = β.hom by
    cases α
    cases β
    cases w
    cases this
    rfl
  calc
    α.hom = α.hom ⋙ β.inv ⋙ β.hom   := by rw [inv_hom_id', Functor.comp_id]
    _     = (α.hom ⋙ α.inv) ⋙ β.hom := by rw [Functor.assoc, ← w]
    _     = β.hom                    := by rw [hom_inv_id, Functor.id_comp]

/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅≅ Y) : Y ≅≅ X where
  hom := I.inv
  inv := I.hom
  hom_inv_id := I.inv_hom_id
  inv_hom_id := I.hom_inv_id

@[simp]
theorem symm_hom (α : X ≅≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp]
theorem symm_inv (α : X ≅≅ Y) : α.symm.inv = α.hom :=
  rfl

@[simp]
theorem symm_mk (hom : X ⥤ Y) (inv : Y ⥤ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =
      { hom := inv, inv := hom, hom_inv_id := inv_hom_id, inv_hom_id := hom_inv_id } :=
  rfl

@[simp]
theorem symm_symm_eq (α : X ≅≅ Y) : α.symm.symm = α := rfl

theorem symm_bijective : Function.Bijective (symm : (X ≅≅ Y) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]
theorem symm_eq_iff {α β : X ≅≅ Y} : α.symm = β.symm ↔ α = β :=
  symm_bijective.injective.eq_iff

variable (X) (Y) in
theorem nonempty_iso_symm : Nonempty (X ≅≅ Y) ↔ Nonempty (Y ≅≅ X) :=
  ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

variable (X) in
/-- Identity isomorphism. -/
@[refl, simps]
def refl : X ≅≅ X where
  hom := Functor.id X
  inv := Functor.id X

instance : Inhabited (X ≅≅ X) := ⟨Iso.refl X⟩

variable (X) in
theorem nonempty_iso_refl : Nonempty (X ≅≅ X) := ⟨default⟩

variable (X) in
@[simp]
theorem refl_symm : (Iso.refl X).symm = Iso.refl X := rfl

/-- Composition of two category isomorphisms. -/
@[simps]
def trans (α : X ≅≅ Y) (β : Y ≅≅ Z) : X ≅≅ Z where
  hom := α.hom ⋙ β.hom
  inv := β.inv ⋙ α.inv
  hom_inv_id := by
    calc (α.hom ⋙ β.hom) ⋙ β.inv ⋙ α.inv = α.hom ⋙ (β.hom ⋙ β.inv) ⋙ α.inv := rfl
    _ = α.hom ⋙ 𝟭 _ ⋙ α.inv := by rw [β.hom_inv_id]
    _ = α.hom ⋙ α.inv := by rw [Functor.id_comp]
    _ = 𝟭 _ := by rw [α.hom_inv_id']
  inv_hom_id := by
    calc (β.inv ⋙ α.inv) ⋙ α.hom ⋙ β.hom = β.inv ⋙ (α.inv ⋙ α.hom) ⋙ β.hom := rfl
    _ = β.inv ⋙ 𝟭 _ ⋙ β.hom := by rw [α.inv_hom_id]
    _ = β.inv ⋙ β.hom := by rw [Functor.id_comp]
    _ = 𝟭 _ := by rw [β.inv_hom_id']

/-- Notation for composition of isomorphisms. -/
infixr:80 " ≪⋙ " => Iso.trans -- type as `\ll \ggg`.

@[simp]
theorem trans_mk (hom : X ⥤ Y) (inv : Y ⥤ X) (hom_inv_id) (inv_hom_id)
    (hom' : Y ⥤ Z) (inv' : Z ⥤ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans ⟨hom, inv, hom_inv_id, inv_hom_id⟩ ⟨hom', inv', hom_inv_id', inv_hom_id'⟩ =
     ⟨hom ⋙ hom', inv' ⋙ inv, hom_inv_id'', inv_hom_id''⟩ :=
  rfl

@[simp]
theorem trans_symm (α : X ≅≅ Y) (β : Y ≅≅ Z) : (α ≪⋙ β).symm = β.symm ≪⋙ α.symm :=
  rfl

variable {Z' : Type*} [Category Z'] in
@[simp]
theorem trans_assoc (α : X ≅≅ Y) (β : Y ≅≅ Z) (γ : Z ≅≅ Z') :
    (α ≪⋙ β) ≪⋙ γ = α ≪⋙ β ≪⋙ γ := by
  ext; simp only [trans_hom, Functor.assoc]

@[simp]
theorem refl_trans (α : X ≅≅ Y) : Iso.refl X ≪⋙ α = α := by ext; apply Functor.id_comp

@[simp]
theorem trans_refl (α : X ≅≅ Y) : α ≪⋙ Iso.refl Y = α := by ext; apply Functor.comp_id

@[simp]
theorem symm_self_id (α : X ≅≅ Y) : α.symm ≪⋙ α = Iso.refl Y :=
  ext α.inv_hom_id

@[simp]
theorem self_symm_id (α : X ≅≅ Y) : α ≪⋙ α.symm = Iso.refl X :=
  ext α.hom_inv_id

@[simp]
theorem symm_self_id_assoc (α : X ≅≅ Y) (β : Y ≅≅ Z) : α.symm ≪⋙ α ≪⋙ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]

@[simp]
theorem self_symm_id_assoc (α : X ≅≅ Y) (β : X ≅≅ Z) : α ≪⋙ α.symm ≪⋙ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]

theorem inv_comp_eq (α : X ≅≅ Y) {f : X ⥤ Z} {g : Y ⥤ Z} : α.inv ⋙ f = g ↔ f = α.hom ⋙ g :=
  ⟨fun H => by simp [H.symm, ← Functor.assoc, Functor.id_comp],
   fun H => by simp [H, ← Functor.assoc, Functor.id_comp]⟩

theorem eq_inv_comp (α : X ≅≅ Y) {f : X ⥤ Z} {g : Y ⥤ Z} : g = α.inv ⋙ f ↔ α.hom ⋙ g = f :=
  (inv_comp_eq α.symm).symm

theorem comp_inv_eq (α : X ≅≅ Y) {f : Z ⥤ Y} {g : Z ⥤ X} : f ⋙ α.inv = g ↔ f = g ⋙ α.hom :=
  ⟨fun H => by simp [H.symm, Functor.assoc, Functor.comp_id],
   fun H => by simp [H, Functor.assoc, Functor.comp_id]⟩

theorem eq_comp_inv (α : X ≅≅ Y) {f : Z ⥤ Y} {g : Z ⥤ X} : g = f ⋙ α.inv ↔ g ⋙ α.hom = f :=
  (comp_inv_eq α.symm).symm

theorem inv_eq_inv (f g : X ≅≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
  ⟨fun h => by rw [ext_inv h], fun h => by rw [ext h]⟩

theorem hom_comp_eq_id (α : X ≅≅ Y) {f : Y ⥤ X} : α.hom ⋙ f = Functor.id X ↔ f = α.inv := by
  rw [← eq_inv_comp, Functor.comp_id]

theorem comp_hom_eq_id (α : X ≅≅ Y) {f : Y ⥤ X} : f ⋙ α.hom = Functor.id Y ↔ f = α.inv := by
  rw [← eq_comp_inv, Functor.id_comp]

theorem inv_comp_eq_id (α : X ≅≅ Y) {f : X ⥤ Y} : α.inv ⋙ f = Functor.id Y ↔ f = α.hom :=
  hom_comp_eq_id α.symm

theorem comp_inv_eq_id (α : X ≅≅ Y) {f : X ⥤ Y} : f ⋙ α.inv = Functor.id X ↔ f = α.hom :=
  comp_hom_eq_id α.symm

theorem hom_eq_inv (α : X ≅≅ Y) (β : Y ≅≅ X) : α.hom = β.inv ↔ β.hom = α.inv := by
  rw [← symm_inv, inv_eq_inv α.symm β, eq_comm]
  rfl

/-- The bijection `(Z ⥤ X) ≃ (Z ⥤ Y)` induced by `α : X ≅≅ Y`. -/
@[simps]
def homToEquiv (α : X ≅≅ Y) : (Z ⥤ X) ≃ (Z ⥤ Y) where
  toFun f := f ⋙ α.hom
  invFun g := g ⋙ α.inv
  left_inv := by
    refine Function.leftInverse_iff_comp.mpr ?_
    ext g
    rw [Function.comp_apply, id_eq, Functor.assoc, hom_inv_id, Functor.comp_id]
  right_inv := by
    refine Function.rightInverse_iff_comp.mpr ?_
    ext g
    rw [Function.comp_apply, id_eq, Functor.assoc, inv_hom_id, Functor.comp_id]

/-- The bijection `(X ⥤ Z) ≃ (Y ⥤ Z)` induced by `α : X ≅≅ Y`. -/
@[simps]
def homFromEquiv (α : X ≅≅ Y) : (X ⥤ Z) ≃ (Y ⥤ Z) where
  toFun f := α.inv ⋙ f
  invFun g := α.hom ⋙ g
  left_inv := by
    refine Function.leftInverse_iff_comp.mpr ?_
    ext g
    rw [Function.comp_apply, id_eq, ← Functor.assoc, hom_inv_id, Functor.id_comp]
  right_inv := by
    refine Function.rightInverse_iff_comp.mpr ?_
    ext g
    rw [Function.comp_apply, id_eq, ← Functor.assoc, inv_hom_id, Functor.id_comp]

@[aesop apply safe (rule_sets := [CategoryTheory])]
theorem inv_ext {f : X ≅≅ Y} {g : Y ⥤ X} (hom_inv_id : f.hom ⋙ g = Functor.id X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory])]
theorem inv_ext' {f : X ≅≅ Y} {g : Y ⥤ X} (hom_inv_id : f.hom ⋙ g = Functor.id X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id

@[simp]
theorem cancel_iso_hom_left (f : X ≅≅ Y) (g g' : Y ⥤ Z) :
    f.hom ⋙ g = f.hom ⋙ g' ↔ g = g' := by
  constructor
  . intro h
    calc g = (f.inv ⋙ f.hom) ⋙ g := by rw [f.inv_hom_id, Functor.id_comp]
    _ = f.inv ⋙ (f.hom ⋙ g) := by rw [Functor.assoc]
    _ = f.inv ⋙ (f.hom ⋙ g') := by rw [h]
    _ = (f.inv ⋙ f.hom) ⋙ g' := by rw [Functor.assoc]
    _ = g' := by rw [f.inv_hom_id, Functor.id_comp]
  . intro h
    rw[h]

@[simp]
theorem cancel_iso_inv_left (f : Y ≅≅ X) (g g' : Y ⥤ Z) :
    f.inv ⋙ g = f.inv ⋙ g' ↔ g = g' := by
  constructor
  . intro h
    calc g = (f.hom ⋙ f.inv) ⋙ g := by rw [f.hom_inv_id, Functor.id_comp]
    _ = f.hom ⋙ (f.inv ⋙ g) := by rw [Functor.assoc]
    _ = f.hom ⋙ (f.inv ⋙ g') := by rw [h]
    _ = (f.hom ⋙ f.inv) ⋙ g' := by rw [Functor.assoc]
    _ = g' := by rw [f.hom_inv_id, Functor.id_comp]
  . intro h
    rw[h]

@[simp]
theorem cancel_iso_hom_right (f f' : X ⥤ Y) (g : Y ≅≅ Z) :
    f ⋙ g.hom = f' ⋙ g.hom ↔ f = f' := by
  constructor
  . intro h
    calc f = f ⋙ (g.hom ⋙ g.inv) := by rw [g.hom_inv_id, Functor.comp_id]
    _ = (f ⋙ g.hom) ⋙ g.inv := by rw [Functor.assoc]
    _ = (f' ⋙ g.hom) ⋙ g.inv := by rw [h]
    _ = f' ⋙ (g.hom ⋙ g.inv) := by rw [Functor.assoc]
    _ = f' := by rw [g.hom_inv_id, Functor.comp_id]
  . intro h
    rw[h]

@[simp]
theorem cancel_iso_inv_right (f f' : X ⥤ Y) (g : Z ≅≅ Y) :
    f ⋙ g.inv = f' ⋙ g.inv ↔ f = f' := by
  constructor
  . intro h
    calc f = f ⋙ (g.inv ⋙ g.hom) := by rw [g.inv_hom_id, Functor.comp_id]
    _ = (f ⋙ g.inv) ⋙ g.hom := by rw [Functor.assoc]
    _ = (f' ⋙ g.inv) ⋙ g.hom := by rw [h]
    _ = f' ⋙ (g.inv ⋙ g.hom) := by rw [Functor.assoc]
    _ = f' := by rw [g.inv_hom_id, Functor.comp_id]
  . intro h
    rw[h]

variable {W X' : Type*} [Category W] [Category X']
/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp]
theorem cancel_iso_hom_right_assoc (f : W ⥤ X) (g : X ⥤ Y) (f' : W ⥤ X')
    (g' : X' ⥤ Y) (h : Y ≅≅ Z) : f ⋙ g ⋙ h.hom = f' ⋙ g' ⋙ h.hom ↔ f ⋙ g = f' ⋙ g' := by
  constructor
  . intro hy
    rw [← Functor.assoc, ← Functor.assoc] at hy
    exact (cancel_iso_hom_right (f ⋙ g) (f' ⋙ g') h).mp hy
  . intro hy
    simp only [← Functor.assoc, cancel_iso_hom_right]
    exact hy

@[simp]
theorem cancel_iso_inv_right_assoc (f : W ⥤ X) (g : X ⥤ Y) (f' : W ⥤ X')
    (g' : X' ⥤ Y) (h : Z ≅≅ Y) : f ⋙ g ⋙ h.inv = f' ⋙ g' ⋙ h.inv ↔ f ⋙ g = f' ⋙ g' := by
  constructor
  . intro hy
    rw [← Functor.assoc, ← Functor.assoc] at hy
    exact (cancel_iso_inv_right (f ⋙ g) (f' ⋙ g') h).mp hy
  . intro hy
    simp only [← Functor.assoc, cancel_iso_inv_right]
    exact hy

def toEquivalence (h : X ≅≅ Y) : X ≌ Y where
  functor := h.hom
  inverse := h.inv
  unitIso := eqToIso h.hom_inv_id.symm
  counitIso := eqToIso h.inv_hom_id
  functor_unitIso_comp x := by simp [eqToHom_map]

lemma whiskerLeft_inv_hom_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η ≍ η := by
  rw [F.inv_hom_id]
  aesop_cat

lemma whiskerLeft_inv_hom {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    whiskerLeft_inv_hom_heq F G H η

lemma whiskerLeft_hom_inv_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η ≍ η := by
  rw [F.hom_inv_id]
  aesop_cat

lemma whiskerLeft_hom_inv {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    whiskerLeft_hom_inv_heq F G H η

end Iso

end CategoryTheory.Functor

namespace CategoryTheory.AsSmall

variable {C : Type*} [Category C]

def downIso : AsSmall C ≅≅ C where
  hom := AsSmall.down
  inv := AsSmall.up

instance : (AsSmall.down (C := C)).Full where
  map_surjective f := ⟨⟨f⟩, rfl⟩

instance : (AsSmall.down (C := C)).Faithful where
  map_injective := by
    intro _ _ f g h
    cases f
    cases g
    cases h
    rfl

instance : (AsSmall.up (C := C)).Full where
  map_surjective f := ⟨f.down, by cases f; rfl⟩

instance : (AsSmall.up (C := C)).Faithful where
  map_injective := by
    intro _ _ f g h
    exact congrArg ULift.down h

end CategoryTheory.AsSmall
