import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import HoTTLean.ForMathlib
import HoTTLean.Grothendieck.Groupoidal.Basic
import HoTTLean.ForMathlib.CategoryTheory.Functor.IsPullback

/-!
Here we define pointed categories and pointed groupoids as well as prove some basic lemmas.
-/

universe w v u v₁ u₁ v₂ u₂

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp

open Functor

abbrev PCat := ∫ 𝟭 Cat.{v,u}

namespace PCat

open Grothendieck

-- TODO remove this
/-- The functor that takes PCat to Cat by forgetting the points-/
abbrev forgetToCat : PCat.{v,u} ⥤ Cat.{v,u} :=
  Functor.Grothendieck.forget _

-- write using `\d=`
prefix:max "⇓" => forgetToCat.obj

-- write using `\d==`
postfix:max "⟱" => fun F => Cat.Hom.toFunctor (forgetToCat.map F)

lemma forgetToCat_map {C D : PCat} (F : C ⟶ D) :
    F⟱ = F.base.toFunctor := rfl

@[simp]
theorem id_obj {C : PCat} (X : C.base) : (𝟙 C)⟱.obj X = X :=
  rfl

@[simp]
theorem id_map {C : PCat} {X Y : C.base} (f : X ⟶ Y) :
    (𝟙 C)⟱.map f = f :=
  rfl

@[simp] lemma id_fiber {C : PCat} : Hom.fiber (𝟙 C) = 𝟙 _ := rfl

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
    mapFiber α (f ≫ g) = eqToHom (by simp [mapObjFiber, objFiber])
      ≫ (α.map g)⟱.map (mapFiber α f) ≫ mapFiber α g := by
  simp [mapFiber]

theorem mapFiber_inv {x y} (f : x ⟶ y) [IsIso f] :
    mapFiber α (inv f) = eqToHom (Functor.map_inv α f ▸ rfl) ≫ (inv (α.map f)).fiber := by
  simp [mapFiber, Grothendieck.congr (Functor.map_inv α f)]

end

theorem eqToHom_base_map {x y : PCat} (eq : x = y) {a b} (f : a ⟶ b) :
    (eqToHom eq).base.toFunctor.map f =
      eqToHom (by simp) ≫ (eqToHom (by simp [eq] : x.base = y.base)).toFunctor.map f ≫
        eqToHom (by simp) := by
  cases eq
  simp

end

def asSmallFunctor : PCat.{v, u} ⥤ PCat.{max w v u, max w v u} :=
  Grothendieck.functorTo
    (Functor.Grothendieck.forget _ ⋙ Cat.asSmallFunctor.{w,v,u})
    (fun x => ⟨x.fiber⟩)
    (fun f => ⟨f.fiber⟩)
    (fun _ => rfl)
    (fun _ _ => rfl)

end PCat

/- Implementation note:
  Unlike with `Grothendieck.Groupoidal` we simplify everything down to
  the underlying `Grothendieck` definitions
-/

abbrev PGrpd := Functor.Grothendieck Grpd.forgetToCat.{v,u}

namespace PGrpd

open Grothendieck Grpd

-- TODO remove this
/-- The functor that takes PGrpd to Grpd by forgetting the points -/
abbrev forgetToGrpd : PGrpd.{v,u} ⥤ Grpd.{v,u} :=
  Functor.Grothendieck.forget _

/-- The forgetful functor from PGrpd to PCat -/
def forgetToPCat : PGrpd.{v,u} ⥤ PCat.{v,u} :=
  Functor.Grothendieck.pre (Functor.id Cat) forgetToCat

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

@[simp] lemma id_fiber {C : PGrpd} : Hom.fiber (𝟙 C) = 𝟙 _ := rfl

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
  simp [forgetToCat]

-- formerly `map_id_point`
@[simp] theorem map_id_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd}
    {x : C} : (F.map (𝟙 x)).fiber =
    eqToHom (by simp [forgetToCat]) := by
  rw! [Functor.map_id]
  simp

-- formerly `map_comp_point`
@[simp] theorem map_comp_fiber {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd}
    {x y z: C} (f : x ⟶ y) (g : y ⟶ z) : (F.map (f ≫ g)).fiber =
    eqToHom (by simp [forgetToCat]) ≫ (F.map g)⟱.map (F.map f).fiber ≫ (F.map g).fiber := by
  rw! [Functor.map_comp]
  simp
  rfl

/-- This is the proof of equality used in the eqToHom in `PGrpd.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq)⟱.obj P1.fiber = P2.fiber := by
  subst eq
  simp

/-- This shows that the fiber map of an eqToHom in PGrpd is an eqToHom-/
theorem eqToHom_fiber {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).fiber = (eqToHom (eqToHom_point_aux eq)) := by
  subst eq
  simp [forgetToCat]

instance : forgetToGrpd.ReflectsIsomorphisms := by
  constructor
  intro A B F hiso
  rcases hiso with ⟨ G , hFG , hGF ⟩
  use Hom.mk G (G.map (Groupoid.inv F.fiber)
    ≫ eqToHom (Functor.congr_obj hFG A.fiber))
  constructor
  · apply Grothendieck.Hom.ext
    · simp [Grpd.forgetToCat]
    · exact hFG
  · apply Grothendieck.Hom.ext
    · have := Functor.congr_hom hGF F.fiber
      simp only [Grpd.comp_eq_comp, Functor.comp_map, forgetToGrpd_map] at this
      simp [this, Grpd.forgetToCat]
    · exact hGF

section
variable {Γ : Type u₂} [Category.{v₂} Γ]

-- TODO factor through `objFiber'`
section
variable (α : Γ ⥤ PGrpd.{v₁,u₁})

-- formerly `objPt`
def objFiber (x : Γ) : ⇓(α.obj x) := (α.obj x).fiber

theorem objFiber_naturality {Δ : Type*} [Category Δ] (σ : Δ ⥤ Γ) (α : Γ ⥤ PGrpd) (x : Δ) :
    objFiber (σ ⋙ α) x = objFiber α (σ.obj x) :=
  rfl

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

theorem mapFiber_naturality {Δ : Type*} [Category Δ] (σ : Δ ⥤ Γ) {x y} (f : x ⟶ y) :
    mapFiber (σ ⋙ α) f = mapFiber α (σ.map f) := by
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

/-- This definition ensures that we deal with the functor
(α ⋙ forgetToGrpd).obj x ⥤ A.obj x
as opposed to the
-/
@[simp] abbrev objFiber'EqToHom (x : Γ) : (α ⋙ forgetToGrpd).obj x ⥤ A.obj x :=
  eqToHom (Functor.congr_obj h x)

-- formerly `objPt'`
def objFiber' (x : Γ) : A.obj x :=
  (objFiber'EqToHom h x).obj (objFiber α x)

@[simp] lemma objFiber'_rfl (x : Γ) : objFiber' rfl x = objFiber α x := rfl

@[simp] theorem objFiber'_heq {x} : HEq (PGrpd.objFiber' h x) (α.obj x).fiber := by
  simp [PGrpd.objFiber', PGrpd.objFiber, Grpd.eqToHom_obj]

theorem objFiber'_naturality {Δ : Type*} [Category Δ] (σ : Δ ⥤ Γ) {A : Γ ⥤ Grpd.{v₁,u₁}}
    {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A) (x : Δ) :
    @objFiber' _ _ (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) x = objFiber' h (σ.obj x) :=
  rfl

def mapFiber'EqToHom {x y : Γ} (f : x ⟶ y) : (A.map f).obj (objFiber' h x) ⟶
    (objFiber'EqToHom h y).obj (((α.map f).base).obj (α.obj x).fiber) :=
  eqToHom (by
  simp [Functor.congr_hom h.symm f, Functor.comp_obj, Grpd.comp_eq_comp, objFiber',
    Grpd.eqToHom_obj, cast_cast]
  rfl)

-- formerly `mapPoint'`
def mapFiber' {x y : Γ} (f : x ⟶ y) :
    (A.map f).obj (objFiber' h x) ⟶ objFiber' h y :=
  mapFiber'EqToHom h f ≫ (objFiber'EqToHom h y).map (α.map f).fiber

@[simp] theorem mapFiber'_id {x} :
    mapFiber' h (𝟙 x) = eqToHom (by simp) := by
  subst h
  simp only [mapFiber', map_id_fiber]
  apply eq_of_heq
  simp [mapFiber'EqToHom]

@[simp] theorem mapFiber'_heq {x y} (f : x ⟶ y) :
    HEq (PGrpd.mapFiber' h f) (α.map f).fiber := by
  simp only [PGrpd.mapFiber', mapFiber'EqToHom]
  aesop_cat

include h in
theorem mapFiber'_comp_aux0 {z} : Grpd.of ⇓(α.obj z) = A.obj z := by
  subst h
  rfl

theorem mapFiber'_comp_aux1 {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (A.map (f ≫ g)).obj (objFiber' h x) =
    (eqToHom (mapFiber'_comp_aux0 h)).obj ((α.map (f ≫ g))⟱.obj ((α.obj x)).fiber) := by
  subst h
  simp [objFiber]

theorem mapFiber'_naturality {Δ : Type*} [Category Δ] (σ : Δ ⥤ Γ) {x y} (f : x ⟶ y) :
    @mapFiber' _ _ (σ ⋙ A) (σ ⋙ α) (by rw [Functor.assoc, h]) _ _ f
    = mapFiber' h (σ.map f) := by
  simp [mapFiber', mapFiber'EqToHom]

@[simp] theorem mapFiber'_rfl {x y : Γ} (f : x ⟶ y) : mapFiber' rfl f = mapFiber α f := by
  simp [mapFiber', mapFiber, mapFiber'EqToHom]

theorem mapFiber'_comp'
    {A : Γ ⥤ Grpd.{v₁,u₁}} {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A)
    {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : mapFiber' h (f ≫ g)
    = eqToHom (by simp) ≫ (A.map g).map (mapFiber' h f) ≫ mapFiber' h g := by
  subst h
  simp [mapFiber]

-- TODO: remove and replace with `mapFiber'_comp'`
theorem mapFiber'_comp {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : mapFiber' h (f ≫ g)
    = eqToHom (by rw [mapFiber'_comp_aux1 h f g]; simp [forgetToCat]) ≫
    (eqToHom (mapFiber'_comp_aux0 h)).map ((α.map g).base.map (α.map f).fiber)
    ≫ (eqToHom (mapFiber'_comp_aux0 h)).map (α.map g).fiber := by
  simp [mapFiber', eqToHom_map, mapFiber'EqToHom]

theorem mapFiber_inv {x y} (f : x ⟶ y) [IsIso f] :
    mapFiber α (inv f) = eqToHom (Functor.map_inv α f ▸ rfl) ≫ (inv (α.map f)).fiber := by
  simp [mapFiber, Grothendieck.congr (Functor.map_inv α f)]

theorem inv_mapFiber_heq {x y} (f : x ⟶ y) [IsIso f] :
    inv (mapFiber α f) ≍ ((α ⋙ forgetToGrpd).map f).map (mapFiber α (inv f)) := by
  rw! [mapFiber_inv]
  simp [eqToHom_map, mapFiber, Grpd.forgetToCat]
  let H := α.map f
  let hobj : H.base.obj ((CategoryTheory.inv H).base.obj (α.obj y).fiber) = (α.obj y).fiber := by
    change ((CategoryTheory.inv H ≫ H).base).obj (α.obj y).fiber =
      (𝟙 (α.obj y) : α.obj y ⟶ α.obj y).base.obj (α.obj y).fiber
    rw [IsIso.inv_hom_id]
  have hleft :
      (eqToHom hobj.symm ≫ H.base.map (CategoryTheory.inv H).fiber) ≫ H.fiber = 𝟙 _ := by
    have hfib := Grothendieck.congr (IsIso.inv_hom_id H)
    simp [H, Grothendieck.comp_fiber, Grothendieck.id_fiber] at hfib
    dsimp [H]
    have hfib' : (α.map f).base.map (CategoryTheory.inv (α.map f)).fiber ≫ (α.map f).fiber = eqToHom hobj := by
      simpa [Grpd.forgetToCat] using hfib
    rw [Category.assoc, hfib']
    simp
  have hEq : CategoryTheory.inv (C := (α.obj y).base) H.fiber =
      eqToHom hobj.symm ≫ H.base.map (CategoryTheory.inv H).fiber := by
    apply IsIso.inv_eq_of_inv_hom_id
    simpa [Category.assoc] using hleft
  exact (heq_of_eq hEq).trans (eqToHom_comp_heq _ hobj.symm)

end

theorem Functor.hext (F G : Γ ⥤ PGrpd)
    (hbase : F ⋙ forgetToGrpd = G ⋙ forgetToGrpd)
    (hfiber_obj : ∀ x : Γ, HEq (F.obj x).fiber (G.obj x).fiber)
    (hfiber_map : ∀ {x y : Γ} (f : x ⟶ y), HEq (F.map f).fiber (G.map f).fiber)
    : F = G :=
  Functor.Grothendieck.FunctorTo.hext hbase hfiber_obj hfiber_map

section
variable {Γ : Type u₁} [Category.{v₁} Γ]
variable (A : Γ ⥤ Grpd) (fibObj : Π (x : Γ), A.obj x)
    (fibMap : Π {x y : Γ} (f : x ⟶ y),
      (A.map f).obj (fibObj x) ⟶ fibObj y)

theorem functorTo_map_id_aux (x : Γ) : (A.map (𝟙 x)).obj (fibObj x) = fibObj x := by
  simp

theorem functorTo_map_comp_aux {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    (A.map (f ≫ g)).obj (fibObj x)
    = (A.map g).obj ((A.map f).obj (fibObj x)) := by
  simp

section
variable
    (map_id : Π (x : Γ), fibMap (CategoryStruct.id x) = eqToHom (functorTo_map_id_aux _ _ _))
    (map_comp : Π {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z), fibMap (f ≫ g)
      = eqToHom (functorTo_map_comp_aux _ _ _ _) ≫ (A.map g).map (fibMap f) ≫ fibMap g)

/-- To define a functor into `PGrpd` we can make use of an existing functor into `Grpd`.
  This is definitinoally just `Grothendieck.functorTo`,
  but giving the user a slightly less bloated context. -/
def functorTo : Γ ⥤ PGrpd := Grothendieck.functorTo A fibObj fibMap map_id map_comp

@[simp] theorem functorTo_obj_base (x) :
    ((functorTo A fibObj fibMap map_id map_comp).obj x).base = A.obj x :=
  rfl

@[simp] theorem functorTo_obj_fiber (x) :
    ((functorTo A fibObj fibMap map_id map_comp).obj x).fiber = fibObj x :=
  rfl

@[simp] theorem functorTo_map_base {x y} (f : x ⟶ y) :
    ((functorTo A fibObj fibMap map_id map_comp).map f).base = A.map f :=
  rfl

@[simp] theorem functorTo_map_fiber {x y} (f : x ⟶ y) :
    ((functorTo A fibObj fibMap map_id map_comp).map f).fiber = fibMap f :=
  rfl

variable {A} {fibObj} {fibMap} {map_id} {map_comp}
@[simp] theorem functorTo_forget :
    functorTo _ _ _ map_id map_comp ⋙ Functor.Grothendieck.forget _ = A :=
  rfl

end

end

theorem congr {X Y : PGrpd} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

end
end PGrpd

end CategoryTheory

end
