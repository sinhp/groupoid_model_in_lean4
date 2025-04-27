import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.ForMathlib

/-!
Here we define pointed categories and pointed groupoids as well as prove some basic lemmas.
-/

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

noncomputable section PointedCategories

/-- A typeclass for pointed categories. -/
class PointedCategory (C : Type u) extends Category.{v} C where
  pt : C

/-- A constructor that makes a pointed category from a category and a point. -/
def PointedCategory.of (C : Type*) (pt : C) [Category C] : PointedCategory C where
  pt := pt

/-- The structure of a functor from C to D
along with a morphism from the image of the point of C to the point of D. -/
structure PointedFunctor (C D : Type*) [cp : PointedCategory C] [dp : PointedCategory D]
    extends C ⥤ D where
  point : obj (cp.pt) ⟶ (dp.pt)

namespace PointedFunctor

/-- The identity `PointedFunctor` whose underlying functor is the identity functor-/
@[simps!]
def id (C : Type*) [PointedCategory C] : PointedFunctor C C where
  toFunctor := Functor.id C
  point := 𝟙 PointedCategory.pt

variable {C D E : Type*} [cp : PointedCategory C] [PointedCategory D] [PointedCategory E]

/-- Composition of `PointedFunctor` composes the underlying functors and the point morphisms. -/
@[simps!]
def comp (F : PointedFunctor C D) (G : PointedFunctor D E) : PointedFunctor C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  point := (G.map F.point) ≫ (G.point)

theorem congr_func {F G: PointedFunctor C D} (eq : F = G) : F.toFunctor = G.toFunctor :=
  congrArg toFunctor eq

theorem congr_point {F G: PointedFunctor C D} (eq : F = G) :
      F.point = (eqToHom (Functor.congr_obj (congr_func eq) cp.pt)) ≫ G.point := by
    have h :=
      (conj_eqToHom_iff_heq
        F.point G.point (Functor.congr_obj (congr_func eq) cp.pt) rfl).mpr
    simp at h
    apply h
    rw [eq]

/-- The extensionality principle for pointed functors-/
@[ext (iff := false)]
theorem ext (F G: PointedFunctor C D) (h_func : F.toFunctor = G.toFunctor)
    (h_point : F.point = (eqToHom (Functor.congr_obj h_func cp.pt)) ≫ G.point) : F = G := by
  rcases F with ⟨F.func,F.point⟩
  rcases G with ⟨G.func,G.point⟩
  congr
  simp at h_point
  have temp : G.point = G.point ≫ (eqToHom rfl) := by simp
  rw [temp] at h_point
  exact
    (conj_eqToHom_iff_heq F.point G.point
          (congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor h_func))
            PointedCategory.pt)
          rfl).mp
      h_point

end PointedFunctor

/-- The category of pointed categorys and pointed functors-/
def PCat :=
  Bundled PointedCategory.{v, u}

namespace PCat

instance : CoeSort PCat.{v,u} (Type u) :=
  ⟨Bundled.α⟩

instance str (C : PCat.{v, u}) : PointedCategory.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `PCat` from the underlying type and the typeclass. -/
def of (C : Type u) [PointedCategory C] : PCat.{v, u} :=
  Bundled.of C

instance category : LargeCategory.{max v u} PCat.{v, u} where
  Hom C D := PointedFunctor C D
  id C := PointedFunctor.id C
  comp f g := PointedFunctor.comp f g
  comp_id f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.comp_id]
  id_comp f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.id_comp]
  assoc f g h := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.comp,Functor.assoc]

/-- The functor that takes PCat to Cat by forgetting the points-/
@[simps] def forgetToCat : PCat.{v,u} ⥤ Cat.{v,u} where
  obj x := Cat.of x
  map f := f.toFunctor

@[simp]
theorem id_obj {C : PCat} (X : C) : (𝟙 C : PointedFunctor C C).obj X = X :=
  rfl

@[simp]
theorem id_map {C : PCat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : PointedFunctor C C).map f = f :=
  rfl

@[simp]
lemma id_toFunctor {C : PCat} : (𝟙 C : PointedFunctor C C).toFunctor = 𝟭 C :=
  rfl

@[simp]
lemma id_point {C : PCat} : (𝟙 C : PointedFunctor C C).point = 𝟙 PointedCategory.pt :=
  rfl

@[simp]
theorem comp_obj {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  rfl

@[simp]
lemma comp_toFunctor {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp]
lemma comp_point {C D E : PCat} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).point = G.map (F.point) ≫ G.point := rfl


/-- This is the proof of equality used in the eqToHom in `PCat.eqToHom_hom` -/
theorem eqToHom_hom_aux {C1 C2 : PCat.{v,u}} (x y: C1) (eq : C1 = C2) :
    (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem eqToHom_hom {C1 C2 : PCat.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (PCat.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

@[simp] theorem map_id_point {C : Type u} [Category.{v} C] {F : C ⥤ PCat} {x : C} :
    (F.map (CategoryStruct.id x)).point =
    eqToHom (by simp : (F.map (CategoryStruct.id x)).obj (F.obj x).str.pt = (F.obj x).str.pt) := by
  have : (CategoryStruct.id (F.obj x)).point = _ := PCat.id_point
  convert this
  · simp
  · simp
  · refine HEq.symm (heq_of_eqRec_eq ?_ rfl)
    · symm; assumption

@[simp] theorem map_comp_point {C : Type u} [Category.{v} C] {F : C ⥤ PCat} {x y z: C} (f : x ⟶ y) (g : y ⟶ z) :
    (F.map (f ≫ g)).point =
    eqToHom (by simp) ≫ (F.map g).map (F.map f).point ≫ (F.map g).point := by
  have : F.map (f ≫ g) = F.map f ≫ F.map g := by simp
  simp [PointedFunctor.congr_point this]

theorem eqToHom_toFunctor {P1 P2 : PCat.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).toFunctor = (eqToHom (congrArg PCat.forgetToCat.obj eq)) := by
  cases eq
  simp[ PointedFunctor.id, CategoryStruct.id, PCat.forgetToCat,Cat.of,Bundled.of]

-- TODO this should be renamed to PCat.eqToHom_point_aux
-- because PCat and PGrpd both use pointed functors
/-- This is the proof of equality used in the eqToHom in `PointedFunctor.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PCat.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).obj PointedCategory.pt = PointedCategory.pt := by
  cases eq
  simp [CategoryStruct.id]

-- TODO this should be renamed to PCat.eqToHom_point
-- because PCat and PGrpd both use pointed functors
/-- This shows that the point of an eqToHom in PCat is an eqToHom-/
theorem eqToHom_point {P1 P2 : PCat.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).point = (eqToHom (PCat.eqToHom_point_aux eq)) := by
  cases eq
  simp[PointedFunctor.id, CategoryStruct.id, PCat.forgetToCat,Cat.of,Bundled.of]

lemma hext {C D : PCat} (hα : C.α = D.α) (hstr : HEq C.str D.str) :
    C = D := by
  cases C
  cases D
  subst hα
  subst hstr
  rfl

lemma hext_iff {C D : PCat} : C.α = D.α ∧ HEq C.str D.str
    ↔ C = D := by
  constructor
  · intro ⟨ hα , hstr ⟩
    exact hext hα hstr
  · intro hCD
    subst hCD
    exact ⟨ rfl , HEq.rfl ⟩

end PCat

/-- The class of pointed groupoids. -/
class PointedGroupoid (C : Type u) extends Groupoid.{v} C, PointedCategory.{v,u} C

/-- A constructor that makes a pointed groupoid from a groupoid and a point. -/
def PointedGroupoid.of (C : Type*) (pt : C) [Groupoid C]: PointedGroupoid C where
  pt := pt

/-- The category of pointed groupoids and pointed functors-/
def PGrpd :=
  Bundled PointedGroupoid.{v,u}

namespace PGrpd

instance : CoeSort PGrpd.{v,u} (Type u) :=
  ⟨Bundled.α⟩

instance str (C : PGrpd.{v, u}) : PointedGroupoid.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `PGrpd` from the underlying type and the typeclass. -/
def of (C : Type u) [PointedGroupoid C] : PGrpd.{v, u} :=
  Bundled.of C

/-- Construct a bundled `PGrpd` from the underlying type and the typeclass. -/
def ofGrpd (G : Grpd.{v,u}) (pt : G) : PGrpd.{v, u} :=
  ⟨ _ , .of G pt ⟩

/-- Construct a bundled `PGrpd` from a `Grpd` and a point -/
def fromGrpd (G : Grpd.{v,u}) (g : G) : PGrpd.{v,u} := by
  have pg : PointedGroupoid (Bundled.α G) := by
    apply PointedGroupoid.of (Bundled.α G) g
  exact PGrpd.of (Bundled.α G)

instance category : LargeCategory.{max v u} PGrpd.{v, u} where
  Hom C D := PointedFunctor C D
  id C := PointedFunctor.id C
  comp f g := PointedFunctor.comp f g
  comp_id f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.comp_id]
  id_comp f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.id_comp]
  assoc f g h := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.comp,Functor.assoc]

/-- Construct a morphism in `PGrpd` from the underlying functor -/
@[simp] def homOf {C D : PGrpd.{v,u}} (F : PointedFunctor C D) :
    C ⟶ D := F

/-- The functor that takes PGrpd to Grpd by forgetting the points-/
@[simps] def forgetToGrpd : PGrpd.{v,u} ⥤ Grpd.{v,u} where
  obj x := Grpd.of x
  map f := f.toFunctor

/-- This takes PGrpd to PCat-/
@[simps] def forgetToPCat : PGrpd.{v,u} ⥤ PCat.{v,u} where
  obj x := PCat.of x
  map f := f

@[simp]
theorem id_obj {C : PGrpd} (X : C) : (𝟙 C : PointedFunctor C C).obj X = X :=
  rfl

@[simp]
theorem id_map {C : PGrpd} {X Y : C} (f : X ⟶ Y) : (𝟙 C : PointedFunctor C C).map f = f :=
  rfl

@[simp]
lemma id_toFunctor {C : PGrpd} : (𝟙 C : PointedFunctor C C).toFunctor = 𝟭 C :=
  rfl

@[simp]
lemma id_point {C : PGrpd} : (𝟙 C : PointedFunctor C C).point = 𝟙 PointedCategory.pt :=
  rfl

@[simp]
theorem comp_obj {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  rfl

@[simp]
lemma comp_toFunctor {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp]
lemma comp_point {C D E : PGrpd} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).point = G.map (F.point) ≫ G.point := rfl

@[simp] theorem map_id_point {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd} {x : C} :
    (F.map (CategoryStruct.id x)).point =
    eqToHom (by simp : (F.map (CategoryStruct.id x)).obj (F.obj x).str.pt = (F.obj x).str.pt) := by
  have : (CategoryStruct.id (F.obj x)).point = _ := PGrpd.id_point
  convert this
  · simp
  · simp
  · refine HEq.symm (heq_of_eqRec_eq ?_ rfl)
    · symm; assumption

@[simp] theorem map_comp_point {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd}
    {x y z: C} (f : x ⟶ y) (g : y ⟶ z) : (F.map (f ≫ g)).point =
    eqToHom (by simp) ≫ (F.map g).map (F.map f).point ≫ (F.map g).point := by
  have : F.map (f ≫ g) = F.map f ≫ F.map g := by simp
  simp [PointedFunctor.congr_point this]

/-- This is the proof of equality used in the eqToHom in `PGrpd.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).obj PointedCategory.pt = PointedCategory.pt := by
  cases eq
  simp [CategoryStruct.id]

/-- This shows that the point of an eqToHom in PGrpd is an eqToHom-/
theorem eqToHom_point {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).point = (eqToHom (eqToHom_point_aux eq)) := by
  cases eq
  simp[PointedFunctor.id, CategoryStruct.id, PCat.forgetToCat,Cat.of,Bundled.of]


lemma hext {C D : PGrpd} (hα : C.α = D.α) (hstr : HEq C.str D.str) :
    C = D := by
  cases C
  cases D
  subst hα
  subst hstr
  rfl

lemma hext_iff {C D : PGrpd} : C.α = D.α ∧ HEq C.str D.str
    ↔ C = D := by
  constructor
  · intro ⟨ hα , hstr ⟩
    exact hext hα hstr
  · intro hCD
    subst hCD
    exact ⟨ rfl , HEq.rfl ⟩

instance asSmall (Γ : Type u) [PointedGroupoid.{v} Γ] :
    PointedGroupoid.{max w v u, max w v u} (AsSmall.{w} Γ) := {
  CategoryTheory.Groupoid.asSmallGroupoid.{w,v,u} Γ with
  pt := AsSmall.up.obj PointedGroupoid.pt}

def asSmallFunctor : PGrpd.{v, u} ⥤ PGrpd.{max w v u, max w v u} where
  obj Γ := PGrpd.of $ AsSmall.{max w v u} Γ
  map F := {
    toFunctor := AsSmall.down ⋙ F.toFunctor ⋙ AsSmall.up
    point := AsSmall.up.map F.point}

instance : forgetToGrpd.ReflectsIsomorphisms := by
  constructor
  intro A B F hiso
  rcases hiso with ⟨ G , hFG , hGF ⟩
  use ⟨ G , G.map (Groupoid.inv F.point)
    ≫ eqToHom (Functor.congr_obj hFG A.str.pt) ⟩
  constructor
  · apply PointedFunctor.ext
    · simp
    · exact hFG
  · apply PointedFunctor.ext
    · simp
      have h := Functor.congr_hom hGF F.point
      simp [Grpd.id_eq_id, Grpd.comp_eq_comp, Functor.comp_map] at h
      simp [h, eqToHom_map]
    · exact hGF

section
variable {Γ : Type u₂} [Category.{v₂} Γ]

section
variable (α : Γ ⥤ PGrpd.{v₁,u₁})

def objPt (x : Γ) : α.obj x := (α.obj x).str.pt
def mapObjPt {x y : Γ} (f : x ⟶ y) : α.obj y :=
    (α.map f).obj (objPt α x)
def mapPoint {x y : Γ} (f : x ⟶ y) :
    mapObjPt α f ⟶ objPt α y := (α.map f).point

@[simp] theorem mapPoint_id {x} : mapPoint α (𝟙 x) = eqToHom (by simp [mapObjPt]) := by
  simp [mapPoint]

theorem mapPoint_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    mapPoint α (f ≫ g)
    = eqToHom (by simp [mapObjPt, objPt])
      ≫ (α.map g).map (mapPoint α f) ≫ mapPoint α g := by
  simp [mapPoint]

end

section
variable {A : Γ ⥤ Grpd.{v₁,u₁}} {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A)

def objPt' (x : Γ) : A.obj x :=
  (eqToHom (Functor.congr_obj h x)).obj (objPt α x)

def mapPoint' {x y : Γ} (f : x ⟶ y) :
    (A.map f).obj (objPt' h x) ⟶ objPt' h y :=
  eqToHom (by
    simp only [Functor.congr_hom h.symm f, Functor.comp_obj,
      Grpd.comp_eq_comp, objPt', Grpd.eqToHom_obj, cast_cast]
    rfl)
    ≫ (eqToHom (Functor.congr_obj h y)).map (α.map f).point

@[simp] theorem mapPoint'_id {x} :
    mapPoint' h (𝟙 x) = eqToHom (by simp) := by
  subst h
  simp only [mapPoint', map_id_point]
  apply eq_of_heq
  simp [eqToHom_comp_heq_iff]

include h in
theorem mapPoint'_comp_aux0 {z} : Grpd.of (α.obj z) = A.obj z := by
  subst h
  rfl

theorem mapPoint'_comp_aux1 {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (A.map (f ≫ g)).obj (objPt' h x) =
    (eqToHom (mapPoint'_comp_aux0 h)).obj ((α.map (f ≫ g)).obj PointedCategory.pt) := by
  subst h
  rfl

theorem mapPoint'_comp_aux2 {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((α.map (f ≫ g)).obj PointedCategory.pt ⟶ objPt α z) =
    ((eqToHom (mapPoint'_comp_aux0 h)).obj ((α.map (f ≫ g)).obj PointedCategory.pt) ⟶ objPt' h z) := by
  subst h
  rfl

theorem mapPoint'_comp_aux3 (h : α ⋙ PGrpd.forgetToGrpd = A) {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : (α.map (f ≫ g)).obj PointedCategory.pt
    = (α.map g).obj ((α.map f).obj PointedCategory.pt) := by
  subst h
  simp

theorem mapPoint'_comp {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : mapPoint' h (f ≫ g)
    = eqToHom (by rw [mapPoint'_comp_aux1 h f g]; simp)
    ≫ (eqToHom (mapPoint'_comp_aux0 h)).map ((α.map g).map (α.map f).point)
    ≫ (eqToHom (mapPoint'_comp_aux0 h)).map (α.map g).point := by
  simp [mapPoint', eqToHom_map]

end

end

end PGrpd

end PointedCategories

end CategoryTheory
