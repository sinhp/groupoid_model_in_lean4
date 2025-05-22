import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.ForMathlib
import GroupoidModel.Grothendieck.Groupoidal.Basic

/-!
Here we define pointed categories and pointed groupoids as well as prove some basic lemmas.
-/

universe w v u v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory

abbrev PCat := Grothendieck (Functor.id Cat.{v,u})

namespace PCat

open Grothendieck

-- TODO remove this
/-- The functor that takes PCat to Cat by forgetting the points-/
abbrev forgetToCat : PCat.{v,u} ⥤ Cat.{v,u} :=
  Grothendieck.forget _

-- write using `\d=`
prefix:max "⇓" => forgetToCat.obj

-- write using `\d==`
postfix:max "⟱" => forgetToCat.map

lemma forgetToCat_map {C D : PCat} (F : C ⟶ D) :
    F⟱ = F.base := rfl

@[simp]
theorem id_obj {C : PCat} (X : C.base) : (𝟙 C)⟱.obj X = X :=
  rfl

@[simp]
theorem id_map {C : PCat} {X Y : C.base} (f : X ⟶ Y) :
    (𝟙 C)⟱.map f = f :=
  rfl

@[simp] lemma id_fiber {C : PCat} : Hom.fiber (𝟙 C) = 𝟙 _ := by
  rfl

@[simp]
theorem comp_obj {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) (X : C.base) :
    (F ≫ G)⟱.obj X = G⟱.obj (F⟱.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C.base}
    (f : X ⟶ Y) : (F ≫ G)⟱.map f = G⟱.map (F⟱.map f) :=
  rfl

@[simp] lemma comp_fiber {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).fiber = G⟱.map F.fiber ≫ G.fiber := by
  simp

-- formerly `map_id_point`
@[simp] theorem map_id_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PCat}
    {x : C} : (F.map (𝟙 x)).fiber =
    eqToHom (by simp) := by
  rw! [Functor.map_id]
  simp

-- formerly `map_comp_point`
@[simp] theorem map_comp_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PCat}
    {x y z: C} (f : x ⟶ y) (g : y ⟶ z) : (F.map (f ≫ g)).fiber =
    eqToHom (by simp) ≫ (F.map g)⟱.map (F.map f).fiber ≫ (F.map g).fiber := by
  rw! [Functor.map_comp]
  simp

/-- This is the proof of equality used in the eqToHom in `PCat.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PCat.{v,u}} (eq : P1 = P2) :
    (eqToHom eq)⟱.obj P1.fiber = P2.fiber := by
  subst eq
  simp

/-- This shows that the fiber map of an eqToHom in PCat is an eqToHom-/
theorem eqToHom_fiber {P1 P2 : PCat.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).fiber = (eqToHom (eqToHom_point_aux eq)) := by
  subst eq
  simp

section
variable {Γ : Type u₂} [Category.{v₂} Γ]

-- TODO factor through `objFiber'`
section
variable (α : Γ ⥤ PCat.{v₁,u₁})

-- formerly `objPt`
def objFiber (x : Γ) : ⇓(α.obj x) := (α.obj x).fiber

-- formerly `mapObjPt`
def mapObjFiber {x y : Γ} (f : x ⟶ y) : ⇓(α.obj y) :=
    (α.map f)⟱.obj (objFiber α x)

-- formerly `mapPoint`
def mapFiber {x y : Γ} (f : x ⟶ y) :
    mapObjFiber α f ⟶ objFiber α y := (α.map f).fiber

-- formerly `mapPoint_id`
@[simp] theorem mapFiber_id {x} : mapFiber α (𝟙 x) =
    eqToHom (by simp [mapObjFiber]) := by
  simp [mapFiber]

-- formerly `mapPoint_comp`
theorem mapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    mapFiber α (f ≫ g)
    = eqToHom (by simp [mapObjFiber, objFiber])
      ≫ (α.map g)⟱.map (mapFiber α f) ≫ mapFiber α g := by
  simp [mapFiber]

end

theorem eqToHom_base_map {x y : PCat} (eq : x = y) {a b} (f : a ⟶ b) :
    (eqToHom eq).base.map f = eqToHom (by simp) ≫ (eqToHom (by simp [eq] : x.base = y.base)).map f ≫ eqToHom (by simp) := by
  cases eq
  simp

end

def asSmallFunctor : PCat.{v, u} ⥤ PCat.{max w v u, max w v u} :=
  Grothendieck.functorTo
    (Grothendieck.forget _ ⋙ Cat.asSmallFunctor.{w,v,u})
    (fun x => ⟨x.fiber⟩)
    (fun f => ⟨f.fiber⟩)
    (fun _ => rfl)
    (fun _ _ => rfl)

end PCat

/- Implementation note:
  Unlike with `Grothendieck.Groupoidal` we simplify everything down to
  the underlying `Grothendieck` definitions
-/

abbrev PGrpd := Grothendieck Grpd.forgetToCat.{v,u}

namespace PGrpd

open Grothendieck Grpd

-- TODO remove this
/-- The functor that takes PGrpd to Grpd by forgetting the points -/
abbrev forgetToGrpd : PGrpd.{v,u} ⥤ Grpd.{v,u} :=
  Grothendieck.forget _

/-- The forgetful functor from PGrpd to PCat -/
def forgetToPCat : PGrpd.{v,u} ⥤ PCat.{v,u} :=
  pre (Functor.id Cat) forgetToCat

-- write using `\d=`
prefix:max "⇓" => forgetToGrpd.obj

-- write using `\d==`
postfix:max "⟱" => forgetToGrpd.map

lemma forgetToGrpd_map {C D : PGrpd} (F : C ⟶ D) :
    F⟱ = F.base := rfl

@[simp]
theorem id_obj {C : PGrpd} (X : C.base) : (𝟙 C)⟱.obj X = X :=
  rfl

@[simp]
theorem id_map {C : PGrpd} {X Y : C.base} (f : X ⟶ Y) :
    (𝟙 C)⟱.map f = f :=
  rfl

@[simp] lemma id_fiber {C : PGrpd} : Hom.fiber (𝟙 C) = 𝟙 _ := by
  rfl

@[simp]
theorem comp_obj {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) (X : C.base) :
    (F ≫ G)⟱.obj X = G⟱.obj (F⟱.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) {X Y : C.base}
    (f : X ⟶ Y) : (F ≫ G)⟱.map f = G⟱.map (F⟱.map f) :=
  rfl

-- formerly `comp_point`
@[simp] lemma comp_fiber {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).fiber = G⟱.map F.fiber ≫ G.fiber := by
  simp

-- formerly `map_id_point`
@[simp] theorem map_id_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd}
    {x : C} : (F.map (𝟙 x)).fiber =
    eqToHom (by simp) := by
  rw! [Functor.map_id]
  simp

-- formerly `map_comp_point`
@[simp] theorem map_comp_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd}
    {x y z: C} (f : x ⟶ y) (g : y ⟶ z) : (F.map (f ≫ g)).fiber =
    eqToHom (by simp) ≫ (F.map g)⟱.map (F.map f).fiber ≫ (F.map g).fiber := by
  rw! [Functor.map_comp]
  simp

/-- This is the proof of equality used in the eqToHom in `PGrpd.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq)⟱.obj P1.fiber = P2.fiber := by
  subst eq
  simp

/-- This shows that the fiber map of an eqToHom in PGrpd is an eqToHom-/
theorem eqToHom_fiber {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).fiber = (eqToHom (eqToHom_point_aux eq)) := by
  subst eq
  simp

instance : forgetToGrpd.ReflectsIsomorphisms := by
  constructor
  intro A B F hiso
  rcases hiso with ⟨ G , hFG , hGF ⟩
  use ⟨ G , G.map (Groupoid.inv F.fiber)
    ≫ eqToHom (Functor.congr_obj hFG A.fiber) ⟩
  constructor
  · apply Grothendieck.ext
    · simp
    · exact hFG
  · apply Grothendieck.ext
    · simp
      have h := Functor.congr_hom hGF F.fiber
      simp [Grpd.id_eq_id, Grpd.comp_eq_comp, Functor.comp_map] at h
      simp [h, eqToHom_map]
    · exact hGF

section
variable {Γ : Type u₂} [Category.{v₂} Γ]

-- TODO factor through `objFiber'`
section
variable (α : Γ ⥤ PGrpd.{v₁,u₁})

-- formerly `objPt`
def objFiber (x : Γ) : ⇓(α.obj x) := (α.obj x).fiber

-- formerly `mapObjPt`
def mapObjFiber {x y : Γ} (f : x ⟶ y) : ⇓(α.obj y) :=
    (α.map f)⟱.obj (objFiber α x)

-- formerly `mapPoint`
def mapFiber {x y : Γ} (f : x ⟶ y) :
    mapObjFiber α f ⟶ objFiber α y := (α.map f).fiber

-- formerly `mapPoint_id`
@[simp] theorem mapFiber_id {x} : mapFiber α (𝟙 x) =
    eqToHom (by simp [mapObjFiber]) := by
  simp [mapFiber]

-- formerly `mapPoint_comp`
theorem mapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    mapFiber α (f ≫ g)
    = eqToHom (by simp [mapObjFiber, objFiber])
      ≫ (α.map g)⟱.map (mapFiber α f) ≫ mapFiber α g := by
  simp [mapFiber]

end

section
/-
     ---------------> PGrpd
   α |                  |
     |                  | forgetToGrpd
     |                  V
    Γ ---------------> Grpd
            A
-/
variable {A : Γ ⥤ Grpd.{v₁,u₁}} {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A)

-- formerly `objPt'`
def objFiber' (x : Γ) : A.obj x :=
  (eqToHom (Functor.congr_obj h x)).obj (objFiber α x)

@[simp] lemma objFiber'_rfl (x : Γ) : objFiber' rfl x = objFiber α x := rfl

-- formerly `mapPoint'`
def mapFiber' {x y : Γ} (f : x ⟶ y) :
    (A.map f).obj (objFiber' h x) ⟶ objFiber' h y :=
  eqToHom (by
    simp only [Functor.congr_hom h.symm f, Functor.comp_obj,
      Grpd.comp_eq_comp, objFiber', Grpd.eqToHom_obj, cast_cast]
    rfl)
    ≫ (eqToHom (Functor.congr_obj h y)).map (α.map f).fiber

@[simp] theorem mapFiber'_id {x} :
    mapFiber' h (𝟙 x) = eqToHom (by simp) := by
  subst h
  simp only [mapFiber', map_id_fiber]
  apply eq_of_heq
  simp [eqToHom_comp_heq_iff]

include h in
theorem mapFiber'_comp_aux0 {z} : Grpd.of ⇓(α.obj z) = A.obj z := by
  subst h
  rfl

theorem mapFiber'_comp_aux1 {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (A.map (f ≫ g)).obj (objFiber' h x) =
    (eqToHom (mapFiber'_comp_aux0 h)).obj ((α.map (f ≫ g))⟱.obj ((α.obj x)).fiber) := by
  subst h
  simp [objFiber]

theorem mapPoint'_comp {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : mapFiber' h (f ≫ g)
    = eqToHom (by rw [mapFiber'_comp_aux1 h f g]; simp) ≫
    (eqToHom (mapFiber'_comp_aux0 h)).map ((α.map g).base.map (α.map f).fiber)
    ≫ (eqToHom (mapFiber'_comp_aux0 h)).map (α.map g).fiber := by
  simp [mapFiber', eqToHom_map]

end

def asSmallFunctor : PGrpd.{v, u} ⥤ PGrpd.{max w v u, max w v u} :=
  Grothendieck.functorTo
    (Grothendieck.forget Grpd.forgetToCat ⋙ Grpd.asSmallFunctor.{w,v,u})
    (fun x => ⟨x.fiber⟩)
    (fun f => ⟨f.fiber⟩)
    (fun _ => rfl)
    (fun _ _ => rfl)

theorem asSmallFunctor_forget : asSmallFunctor.{w,v,u} ⋙ Grothendieck.forget _
  = Grothendieck.forget _ ⋙ Grpd.asSmallFunctor := rfl

end

end PGrpd

end CategoryTheory

end
