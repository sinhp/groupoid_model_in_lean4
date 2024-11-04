/-
The category Grpd of (small) groupoids, as needed for the groupoid model of HoTT.

Here is Hofmann and Streicher's original paper:
https://ncatlab.org/nlab/files/HofmannStreicherGroupoidInterpretation.pdf

Here's something from the nLab that looks useful:
Ethan Lewis, Max Bohnet, The groupoid model of type theory, seminar notes (2017)
https://staff.fnwi.uva.nl/b.vandenberg3/Onderwijs/Homotopy_Type_Theory_2017/HoTT-bohnet-lewis-handout.pdf


See the thesis of Jakob Vidmar for polynomials and W-types in groupoids:
https://etheses.whiterose.ac.uk/22517/
-/
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Category.Grpd


-- I added these import
import Mathlib.CategoryTheory.Grothendieck
import GroupoidModel.NaturalModel
import GroupoidModel.FibrationForMathlib.Displayed.Basic
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
--

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory

-- See Mathlib/CategoryTheory/Category/Grpd.lean

noncomputable section

/-!
# The category Grpd of groupoids
Need at least the following, some of which is already in MathLib:
  - the category of small groupoids and their homomorphisms
  - (discrete and split) fibrations of groupoids
  - pullbacks of (discrete and split) fibrations exist in Grpd and are again (such) fibrations
  - set- and groupoid-valued presheaves on groupoids
  - the Grothendieck construction relating the previous two
  - the equivalence between (split) fibrations and presheaves of groupoids
  - Σ and Π-types for (split) fibrations
  - path groupoids
  - the universe of (small) discrete groupoids (aka sets)
  - polynomial functors of groupoids
  - maybe some W-types
  - eventually we will want some groupoid quotients as well
  -/

@[simps?!]
def toCat {C : Type u₁} [Category.{v₁,u₁} C] (G : C ⥤ Grpd) : C ⥤ Cat := G ⋙ Grpd.forgetToCat
namespace Grothendieck

open CategoryTheory Iso

variable {C : Type u₁} [Category.{v₁,u₁} C] {G : C ⥤ Cat.{v₂,u₂}}

/-- A morphism in the Grothendieck construction is an isomorphism if the morphism in the base is an isomorphism and the fiber morphism is an isomorphism. -/
def mkIso {X Y : Grothendieck G} (s : X.base ≅ Y.base) (t : (G |>.map s.hom).obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := { base := s.hom, fiber := t.hom }
  inv.base := s.inv
  inv.fiber := (G.map (s.inv)).map (t.inv) ≫
    eqToHom (by simpa only [Functor.map_comp, Functor.map_id] using
      congr((G.map $(s.hom_inv_id)).obj X.fiber))
  hom_inv_id := by
    apply ext
    erw [comp_fiber]
    simp only [Cat.comp_obj, id_eq, map_hom_inv_id_assoc,
      eqToHom_trans, id_fiber'] at *
    erw [comp_base, id_base]
    dsimp
    rw [s.hom_inv_id]
  inv_hom_id := by
    suffices ∀ {Z g} (_ : g ≫ s.hom = Z) (_ : Z = 𝟙 _)
        {g'} (eq : g' ≫ (G.map g).map t.hom = 𝟙 _)
        (W) (eqW : G.map g ≫ G.map s.hom = W)
        (eq2 : ∃ w1 w2, W.map t.hom = eqToHom w1 ≫ t.hom ≫ eqToHom w2) h1 h2,
        { base := Z, fiber := eqToHom h1 ≫ (G.map s.hom).map (g' ≫ eqToHom h2) ≫ t.hom } =
        ({..} : Grothendieck.Hom ..) from
      this rfl s.inv_hom_id (by simp)
        (W := 𝟙 _) (eqW := by simp) (eq2 := ⟨rfl, rfl, by simp⟩) ..
    rintro _ g - rfl g' eq _ rfl ⟨w1, w2, eq2 : (G.map s.hom).map _ = _⟩ h1 h2; congr
    replace eq := congr((G.map s.hom).map $eq)
    simp only [Functor.map_comp, eq2, eqToHom_map, Category.assoc] at eq ⊢
    conv at eq => lhs; slice 1 3
    rw [(comp_eqToHom_iff ..).1 eq]; simp

end Grothendieck

section
variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

variable (F) in
/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
def GroupoidalGrothendieck := Grothendieck (toCat F)


namespace GroupoidalGrothendieck


instance : Category (GroupoidalGrothendieck F) := inferInstanceAs (Category (Grothendieck _))


instance (X : C) : Groupoid (toCat F |>.obj X) where
  inv f := ((F.obj X).str').inv f

def isoMk {X Y : GroupoidalGrothendieck F} (f : X ⟶ Y) : X ≅ Y := by
  fapply Grothendieck.mkIso
  · exact (Groupoid.isoEquivHom _ _).2 f.base
  · apply (Groupoid.isoEquivHom _ _).2 f.fiber

def inv {X Y : GroupoidalGrothendieck F} (f : X ⟶ Y) : Y ⟶ X  := isoMk f |>.inv

instance groupoid : Groupoid (GroupoidalGrothendieck F) where
  inv f :=  inv f
  inv_comp f := (isoMk f).inv_hom_id
  comp_inv f := (isoMk f).hom_inv_id


def forget : GroupoidalGrothendieck F ⥤ C :=
  Grothendieck.forget (F ⋙ Grpd.forgetToCat)
-- note: maybe come up with a better name?


def ToGrpd : GroupoidalGrothendieck F ⥤ Grpd.{v₂,u₂} := forget ⋙ F

def functorial {C D : Grpd.{v₁,u₁}} (F : C ⟶ D) (G : D ⥤ Grpd.{v₂,u₂})
  : Grothendieck (toCat (F ⋙ G)) ⥤ Grothendieck (toCat G) where
    obj X := ⟨F.obj X.base, X.fiber⟩
    map {X Y} f := ⟨F.map f.base, f.fiber⟩
    map_id X := by
      fapply Grothendieck.ext
      · exact F.map_id X.base
      · simp only [Grothendieck.id_fiber', eqToHom_trans]
    map_comp {X Y Z} f g := by
      simp only [Grothendieck.comp]
      fapply Grothendieck.ext
      · exact F.map_comp f.base g.base
      · erw [Grothendieck.comp_fiber (F:= toCat (F ⋙ G)) f g]
        simp [eqToHom_trans]
        erw [Grothendieck.comp_fiber]; rfl

end GroupoidalGrothendieck

end


section PointedCategories

/-- The class of pointed pointed categorys. -/
class PointedCategory.{w,z} (C : Type z) extends Category.{w} C where
  pt : C

/-- A constructor that makes a pointed categorys from a category and a point. -/
def PointedCategory.of (C : Type*) (pt : C)[Category C]: PointedCategory C where
  pt := pt

/-- The structure of a functor from C to D along with a morphism from the image of the point of C to the point of D -/
structure PointedFunctor (C : Type*)(D : Type*)[cp : PointedCategory C][dp : PointedCategory D] extends C ⥤ D where
  point : obj (cp.pt) ⟶ (dp.pt)

/-- The identity `PointedFunctor` whose underlying functor is the identity functor-/
@[simps!]
def PointedFunctor.id (C : Type*)[PointedCategory C] : PointedFunctor C C where
  toFunctor := Functor.id C
  point := 𝟙 PointedCategory.pt

/-- Composition of `PointedFunctor` that composes there underling functors and shows that the point is preserved-/
@[simps!]
def PointedFunctor.comp {C : Type*}[PointedCategory C]{D : Type*}[PointedCategory D]{E : Type*}[PointedCategory E]
  (F : PointedFunctor C D)(G : PointedFunctor D E)  : PointedFunctor C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  point := (G.map F.point) ≫ (G.point)

theorem PointedFunctor.congr_func {C : Type*}[PointedCategory C]{D : Type*}[PointedCategory D]
  {F G: PointedFunctor C D}(eq : F = G)  : F.toFunctor = G.toFunctor := congrArg toFunctor eq

theorem PointedFunctor.congr_point {C : Type*}[pc :PointedCategory C]{D : Type*}[PointedCategory D]
  {F G: PointedFunctor C D}(eq : F = G)  : F.point = (eqToHom (Functor.congr_obj (congr_func eq) pc.pt)) ≫ G.point := by
    have h := (Functor.conj_eqToHom_iff_heq F.point G.point (Functor.congr_obj (congr_func eq) pc.pt) rfl).mpr
    simp at h
    apply h
    rw[eq]

/-- The extensionality principle for pointed functors-/
@[ext]
theorem PointedFunctor.ext {C : Type*}[pc :PointedCategory C]{D : Type*}[PointedCategory D]
  (F G: PointedFunctor C D)(h_func : F.toFunctor = G.toFunctor)(h_point : F.point = (eqToHom (Functor.congr_obj h_func pc.pt)) ≫ G.point) : F = G := by
  rcases F with ⟨F.func,F.point⟩
  rcases G with ⟨G.func,G.point⟩
  congr
  simp at h_point
  have temp : G.point = G.point ≫ (eqToHom rfl) := by simp
  rw [temp] at h_point
  exact
    (Functor.conj_eqToHom_iff_heq F.point G.point
          (congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor h_func))
            PointedCategory.pt)
          rfl).mp
      h_point

/-- The category of pointed categorys and pointed functors-/
def PCat.{w,z} :=
  Bundled PointedCategory.{w, z}

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
def forgetPoint : PCat ⥤ Cat where
  obj x := Cat.of x
  map f := f.toFunctor

end PCat

/-- The class of pointed pointed groupoids. -/
class PointedGroupoid.{w,z} (C : Type z) extends Groupoid.{w} C, PointedCategory.{w,z} C

/-- A constructor that makes a pointed groupoid from a groupoid and a point. -/
def PointedGroupoid.of (C : Type*) (pt : C) [Groupoid C]: PointedGroupoid C where
  pt := pt

/-- The category of pointed groupoids and pointed functors-/
def PGrpd.{w,z} :=
  Bundled PointedGroupoid.{w, z}

namespace PGrpd

instance : CoeSort PGrpd.{v,u} (Type u) :=
  ⟨Bundled.α⟩

instance str (C : PGrpd.{v, u}) : PointedGroupoid.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `PGrpd` from the underlying type and the typeclass. -/
def of (C : Type u) [PointedGroupoid C] : PGrpd.{v, u} :=
  Bundled.of C

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

/-- The functor that takes PGrpd to Grpd by forgetting the points-/
def forgetPoint : PGrpd ⥤ Grpd where
  obj x := Grpd.of x
  map f := f.toFunctor

/-- This takes PGrpd to PCat-/
def forgetToCat : PGrpd ⥤ PCat where
  obj x := PCat.of x
  map f := f

end PGrpd

end PointedCategories

section Pullbacks

section Lemmas

/--theorem PointedCategory.ext {P1 P2 : PCat.{u,u}} (eq_cat : P1.α  = P2.α): P1 = P2 := by sorry -/
theorem PointedFunctor.eqToHom_toFunctor {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).toFunctor = (eqToHom (congrArg PCat.forgetPoint.obj eq)) := by
    cases eq
    simp[ PointedFunctor.id, CategoryStruct.id, PCat.forgetPoint,Cat.of,Bundled.of]

/-- This is the proof of equality used in the eqToHom in `PointedFunctor.eqToHom_point` -/
theorem PointedFunctor.eqToHom_point_help {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).obj PointedCategory.pt = PointedCategory.pt  := by
  cases eq
  simp [CategoryStruct.id]

/-- This shows that the point of an eqToHom in PCat is an eqToHom-/
theorem PointedFunctor.eqToHom_point {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).point = (eqToHom (PointedFunctor.eqToHom_point_help eq)) := by
  cases eq
  simp[PointedFunctor.id, CategoryStruct.id, PCat.forgetPoint,Cat.of,Bundled.of]

/-- This is the turns the object part of eqToHom functors into a cast-/
theorem Cat.eqToHom_obj (C1 C2 : Cat.{u,v})(x : C1)(eq : C1 = C2): (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the proof of equality used in the eqToHom in `Cat.eqToHom_hom` -/
theorem Cat.eqToHom_hom_help {C1 C2 : Cat.{u,v}}(x y: C1)(eq : C1 = C2): (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem Cat.eqToHom_hom {C1 C2 : Cat.{u,v}}{x y: C1}(f : x ⟶ y)(eq : C1 = C2): (eqToHom eq).map f = (cast (Cat.eqToHom_hom_help x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the proof of equality used in the eqToHom in `PCat.eqToHom_hom` -/
theorem PCat.eqToHom_hom_help {C1 C2 : PCat.{u,v}}(x y: C1)(eq : C1 = C2): (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom pointed functors into a cast-/
theorem PCat.eqToHom_hom {C1 C2 : PCat.{u,v}}{x y: C1}(f : x ⟶ y)(eq : C1 = C2): (eqToHom eq).map f = (cast (PCat.eqToHom_hom_help x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This shows that two objects are equal in Grothendieck A if they have equal bases and fibers that are equal after being cast-/
theorem Grothendieck.ext' {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}(g1 g2 : Grothendieck A)(eq_base : g1.base = g2.base)
  (eq_fiber : g1.fiber = (A.map (eqToHom eq_base.symm)).obj g2.fiber ) : (g1 = g2) := by
    rcases g1 with ⟨g1.base,g1.fiber⟩
    rcases g2 with ⟨g2.base,g2.fiber⟩
    simp at eq_fiber eq_base
    cases eq_base
    simp
    rw[eq_fiber]
    simp [eqToHom_map, CategoryStruct.id]

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem Grothendieck.eqToHom_base {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}(g1 g2 : Grothendieck A)
  (eq : g1 = g2) : (eqToHom eq).base = (eqToHom (congrArg (Grothendieck.forget A).obj eq)) := by
    cases eq
    simp[CategoryStruct.id]

/-- This is the proof of equality used in the eqToHom in `Grothendieck.eqToHom_fiber` -/
theorem Grothendieck.eqToHom_fiber_help {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}{g1 g2 : Grothendieck A}
  (eq : g1 = g2) : (A.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
    cases eq
    simp [Hom.base,A.map_id,CategoryStruct.id]

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem Grothendieck.eqToHom_fiber {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}{g1 g2 : Grothendieck A}
  (eq : g1 = g2) : (eqToHom eq).fiber = eqToHom (Grothendieck.eqToHom_fiber_help eq) := by
    cases eq
    simp[CategoryStruct.id]

/-- This eliminates an eqToHom on the right side of an equality-/
theorem RightSidedEqToHom {C : Type v} [Category C] {x y z : C} (eq : y = z) {f : x ⟶ y} {g : x ⟶ z}
  (heq : HEq f g) : f ≫ eqToHom eq = g := by
    cases eq
    simp
    simp at heq
    exact heq

/-- This theorem is used to eliminate eqToHom form both sides of an equation-/
theorem CastEqToHomSolve {C : Type v} [Category C] {x x1 x2 y y1 y2: C} (eqx1 : x = x1)(eqx2 : x = x2)
  (eqy1 : y1 = y)(eqy2 : y2 = y){f : x1 ⟶ y1}{g : x2 ⟶ y2}(heq : HEq f g) : eqToHom eqx1 ≫ f ≫ eqToHom eqy1 = eqToHom eqx2 ≫ g ≫ eqToHom eqy2:= by
    cases eqx1
    cases eqx2
    cases eqy1
    cases eqy2
    simp
    simp at heq
    exact heq

end Lemmas

section GrothendieckPullBack
/-
In this section we prove that the following square is a PullBack

  Grothendieck A ---- CatVar' ----> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetPoint
        |                           |
        v                           v
        Γ--------------A----------->Cat
-/

-- This takes in two equal functors F and G from C in to Cat and an x:C and returns (F.obj x) ≅ (G.obj x).
def CastFunc {C : Cat.{u,u+1}}{F1 : C ⥤ Cat.{u,u}}{F2 : C ⥤ Cat.{u,u}}(Comm : F1 = F2 )(x : C) :
  Equivalence (F1.obj x) (F2.obj x) := Cat.equivOfIso (eqToIso (Functor.congr_obj  Comm  x))

-- This turns the cast functor in an eqToHom
theorem CastFuncIsEqToHom {C : Cat.{u,u+1}} {F1 : C ⥤ Cat.{u,u}} {F2 : C ⥤ Cat.{u,u}} (Comm : F1 = F2 )(x : C):
  (CastFunc Comm x).functor = (eqToHom (Functor.congr_obj Comm x)) := by
    simp[CastFunc,Cat.equivOfIso]

-- This is a functor that takes a category up a universe level
def Up_uni (Δ : Type u)[Category.{u} Δ] :  Δ ⥤ (ULift.{u+1,u} Δ) where
  obj x := {down := x}
  map f := f

-- This is a functor that takes a category down a universe level
def Down_uni (Δ : Type u)[Category.{u} Δ]: (ULift.{u+1,u} Δ) ⥤ Δ where
  obj x := x.down
  map f := f

-- This is a helper theorem for eliminating Up_uni and Down_uni functors
theorem Up_Down {C : Type (u+1)}[Category.{u} C]{Δ : Type u}[Category.{u} Δ] (F : C ⥤ Δ)
  (G : C ⥤ (ULift.{u+1,u} Δ)): ((F ⋙ (Up_uni Δ)) = G) ↔ (F = (G ⋙ (Down_uni Δ))) := by
    unfold Up_uni
    unfold Down_uni
    simp [Functor.comp]
    refine Iff.intro ?_ ?_ <;> intro h
    · rw[<- h]
    · rw[h]

-- This is the functor from the Grothendieck to Pointed Categorys
def CatVar' (Γ : Cat)(A : Γ ⥤ Cat) : (Grothendieck A) ⥤ PCat where
  obj x := ⟨(A.obj x.base), PointedCategory.of (A.obj x.base) x.fiber⟩
  map f := ⟨A.map f.base, f.fiber⟩
  map_id x := by
    dsimp
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    apply PointedFunctor.ext
    · simp[CategoryStruct.id]
    · simp[CategoryStruct.id,PointedFunctor.id]
  map_comp {x y z} f g := by
    dsimp [CategoryStruct.comp,PointedFunctor.comp]
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    let _ := (PointedCategory.of (A.obj z.base) z.fiber)
    apply PointedFunctor.ext
    · simp
    · simp [A.map_comp,CategoryStruct.comp]

-- This is the proof that the square commutes
theorem Comm {Γ : Cat}(A : Γ ⥤ Cat) : (Down_uni (Grothendieck A) ⋙ CatVar' Γ A) ⋙ PCat.forgetPoint =
  ((Down_uni (Grothendieck A)) ⋙ Grothendieck.forget A ⋙ (Up_uni Γ)) ⋙ Down_uni ↑Γ ⋙ A := by
    apply Functor.ext
    · intros X Y f
      simp [PCat.forgetPoint,Down_uni,Up_uni,CatVar']
    · intro X
      simp [PCat.forgetPoint,Down_uni,Up_uni,CatVar']
      exact rfl

-- This is a helper functor from from a pointed category to itself without a point
def ForgetPointFunctor (P : PCat.{u,u}) : P ⥤ (PCat.forgetPoint.obj P) := by
  simp[PCat.forgetPoint]
  exact Functor.id P

-- This is the construction of universal map of th limit
def Grothendieck.UnivesalMap {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A) : C ⥤ Grothendieck A where
  obj x := {base := (F2.obj x), fiber := ((ForgetPointFunctor (F1.obj x)) ⋙ (CastFunc Comm x).functor).obj ((F1.obj x).str.pt)}
  map f := by
    rename_i X Y
    refine {base := F2.map f, fiber := (eqToHom ?_) ≫ (((CastFunc Comm Y).functor).map (F1.map f).point)}
    dsimp
    have h1 := Functor.congr_hom Comm.symm f
    dsimp at h1
    have h2 : (eqToHom (Functor.congr_obj (Eq.symm Comm) X)).obj
     ((eqToHom (CastFunc.proof_1 Comm X )).obj (@PointedCategory.pt (↑(F1.obj X)) (F1.obj X).str)) =
      ((eqToHom (CastFunc.proof_1 Comm X)) ≫ (eqToHom (Functor.congr_obj (Eq.symm Comm) X))).obj
       (@PointedCategory.pt (↑(F1.obj X)) (F1.obj X).str) := by rfl
    simp[h1,CastFunc,Cat.equivOfIso,ForgetPointFunctor,h2,eqToHom_trans,eqToHom_refl,CategoryStruct.id,PCat.forgetPoint]
  map_id x := by
    dsimp [CategoryStruct.id,Grothendieck.id]
    apply Grothendieck.ext
    simp[Grothendieck.Hom.fiber,(dcongr_arg PointedFunctor.point (F1.map_id x)),eqToHom_map,CategoryStruct.id]
    exact F2.map_id x
  map_comp f g := by
    rename_i X Y Z
    dsimp [CategoryStruct.comp,comp]
    fapply Grothendieck.ext
    · simp
    · dsimp [Hom.fiber]
      have h1 := PointedFunctor.congr_point (F1.map_comp f g)
      dsimp [CategoryStruct.comp] at h1
      simp [h1,(CastFunc Comm Z).functor.map_comp,(CastFunc Comm Z).functor.map_comp,<- Category.assoc,eqToHom_map]
      refine congrArg (fun(F) => F ≫ ((CastFunc Comm Z).functor.map (F1.map g).point)) ?_
      simp [Category.assoc]
      have comm1 := Functor.congr_hom Comm (g)
      simp [Functor.Comp,PCat.forgetPoint] at comm1
      have comm2 := Functor.congr_hom comm1 (F1.map f).point
      rw [comm2]
      simp [Functor.map_comp,eqToHom_map]
      have rwh1 : (CastFunc Comm Z).functor.map ((eqToHom (Eq.symm (Functor.congr_obj Comm Z))).map ((A.map (F2.map g)).map ((eqToHom (Functor.congr_obj Comm Y)).map (F1.map f).point))) =
        ((eqToHom (Functor.congr_obj Comm Y)) ≫ (A.map (F2.map g)) ≫ ((eqToHom (Eq.symm (Functor.congr_obj Comm Z)))) ≫ ((CastFunc Comm Z).functor)).map ((F1.map f).point) := rfl
      have rwh2 : ((eqToHom (Functor.congr_obj Comm Y)) ≫ (A.map (F2.map g)) ≫ ((eqToHom (Eq.symm (Functor.congr_obj Comm Z)))) ≫ ((CastFunc Comm Z).functor)) =
        (CastFunc Comm Y).functor ≫ A.map (F2.map g) := by
        rw[CastFuncIsEqToHom,eqToHom_trans,<- CastFuncIsEqToHom Comm]
        simp
      have rwh3 := Functor.congr_hom rwh2 (F1.map f).point
      rw [rwh1,rwh3]
      simp

--This is the proof that the universal map composed with CatVar' is the the map F1
theorem Grothendieck.UnivesalMap_CatVar'_Comm {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A) : (Grothendieck.UnivesalMap A C F1 F2 Comm) ⋙ (CatVar' Γ A) = F1 := by
    fapply Functor.ext
    intro x
    have Comm' := Functor.congr_obj Comm x
    simp [PCat.forgetPoint] at Comm'
    simp [UnivesalMap,CatVar']
    congr 1
    · simp [<- Comm',Cat.of,Bundled.of]
    · simp [PointedCategory.of,ForgetPointFunctor,CastFunc,Cat.equivOfIso]
      congr 1
      · rw [<- Comm']
        simp [Cat.of,Bundled.of]
      · rw [<- Comm']
        simp [Cat.of,Bundled.of,Cat.str]
      · refine heq_of_cast_eq ?h_obj.h.e_3.e_3.e ?h_obj.h.e_3.e_3.x
        · rw [<- Comm']
          simp [Cat.of,Bundled.of]
        · simp [Cat.eqToHom_obj]
    · intros X Y f
      simp[UnivesalMap,CatVar']
      let _ : PointedCategory (A.obj (F2.obj X)) := by
        apply PointedCategory.mk
        exact (CastFunc Comm X).functor.obj ((ForgetPointFunctor (F1.obj X)).obj ((F1.obj X).str.pt))
      let _ : PointedCategory ↑(A.obj (F2.obj Y)) := by
        apply PointedCategory.mk
        exact (CastFunc Comm Y).functor.obj ((ForgetPointFunctor (F1.obj Y)).obj ((F1.obj Y).str.pt))
      apply PointedFunctor.ext
      · simp [CastFunc,Cat.equivOfIso,CategoryStruct.comp,PointedFunctor.eqToHom_point,eqToHom_map]
        congr <;> try simp [PointedFunctor.eqToHom_toFunctor]
        have rwHelp1 : ((eqToHom (CastFunc.proof_1 Comm Y)).map (F1.map f).point) = ((eqToHom (CastFunc.proof_1 Comm Y)).map (F1.map f).point) ≫ eqToHom rfl  := by
          simp
        rw [rwHelp1]
        refine heq_of_cast_eq ?_ ?_
        · congr 1
          simp [PointedFunctor.eqToHom_toFunctor]
        · simp [Cat.eqToHom_hom,PCat.eqToHom_hom]
          refine (RightSidedEqToHom ?_ ?_).symm
          refine (@HEq.trans _ _ _ _ ((F1.map f).point) _ ?_ ?_)
          · apply cast_heq
          · apply HEq.symm
            apply cast_heq
      · have r := Functor.congr_hom Comm.symm f
        simp
        simp [PCat.forgetPoint] at r
        rw [r]
        simp [CategoryStruct.comp,PointedFunctor.comp,PointedFunctor.eqToHom_toFunctor]

-- This is the proof that the universal map is unique
theorem Grothendieck.UnivesalMap_Uniq {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A)(F : C ⥤ Grothendieck A)
  (F1comm :F ⋙ (CatVar' Γ A) = F1)(F2comm : F ⋙ (Grothendieck.forget A) = F2) :
  F = (Grothendieck.UnivesalMap A C F1 F2 Comm) := by
    fapply Functor.ext
    · intro X
      dsimp [UnivesalMap]
      have eq_base : (F.obj X).base = F2.obj X := by
        rw [<- (Functor.congr_obj F2comm X)]
        simp
      have abstract : F.obj X = Grothendieck.mk ((F.obj X).base) ((F.obj X).fiber) := rfl
      rw [abstract]
      fapply Grothendieck.ext'
      · simpa
      · simp[eqToHom_map,CastFunc,Cat.equivOfIso,ForgetPointFunctor,PointedCategory.pt]
        aesop_cat
    . intros X Y f
      fapply Grothendieck.ext
      . dsimp[UnivesalMap,CategoryStruct.comp]
        dsimp [forget,Functor.comp] at F2comm
        have h := Functor.congr_hom F2comm f
        simp at h
        rw [h,Grothendieck.eqToHom_base,Grothendieck.eqToHom_base]
      . dsimp[UnivesalMap,CategoryStruct.comp]
        dsimp [CatVar',Functor.comp] at F1comm
        have h := (PointedFunctor.congr_point ((Functor.congr_hom F1comm f)))
        simp at h
        rw [h]
        simp [eqToHom_map,CategoryStruct.comp,PointedFunctor.eqToHom_point,Grothendieck.eqToHom_fiber,CastFunc,Cat.equivOfIso]
        have hh : ∀{G1 G2 : Grothendieck A}(eq : G1 = G2), A.map (eqToHom eq).base = eqToHom ?_ := by
          simp[Grothendieck.eqToHom_base,eqToHom_map]
        · congr
        simp [Functor.congr_hom (hh ?_),Cat.eqToHom_hom,PCat.eqToHom_hom]
        refine CastEqToHomSolve _ _ _ _ ?_
        apply @HEq.trans _ _ _ _ (F1.map f).point
        · apply cast_heq
        · apply HEq.symm
          apply cast_heq

-- This is the type of cones
abbrev GrothendieckCones {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} PCat.{u,u})
  (Cat.of.{u,u+1} (ULift.{u+1,u} Γ))
  (Cat.of.{u,u+1} Cat.{u,u})
  PCat.forgetPoint.{u,u}
  ((Down_uni Γ) ⋙ A)

-- This is the cone we will prove is the limit
abbrev GrothendieckLim {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}): (GrothendieckCones A) :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of PCat.{u,u})
    (Cat.of (ULift.{u + 1, u} Γ))
    (Cat.of Cat.{u,u})
    (PCat.forgetPoint.{u,u})
    ((Down_uni Γ) ⋙ A)
    (Cat.of (ULift.{u+1,u} (Grothendieck A)))
    ((Down_uni (Grothendieck A)) ⋙ CatVar' Γ A)
    (Down_uni (Grothendieck A) ⋙ Grothendieck.forget A ⋙ Up_uni Γ)
    (Comm A)

-- This is the proof that the limit cone is a limit
def GrothendieckLimisLim {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) : Limits.IsLimit (GrothendieckLim A) := by
  refine Limits.PullbackCone.isLimitAux' (GrothendieckLim A) ?_
  intro s
  let FL := (s.π).app (Option.some Limits.WalkingPair.left)
  let FR := (s.π).app (Option.some Limits.WalkingPair.right)
  let Comm := (((s.π).naturality (Limits.WalkingCospan.Hom.inl)).symm).trans ((s.π).naturality (Limits.WalkingCospan.Hom.inr))
  dsimp [Quiver.Hom] at FL FR Comm
  fconstructor
  · dsimp [GrothendieckLim,Quiver.Hom,Cat.of,Bundled.of]
    refine (Grothendieck.UnivesalMap A s.pt FL (FR ⋙ (Down_uni Γ)) ?_) ⋙ (Up_uni (Grothendieck A))
    exact (((s.π).naturality (Limits.WalkingCospan.Hom.inl)).symm).trans ((s.π).naturality (Limits.WalkingCospan.Hom.inr))
  · refine ⟨?_,?_,?_⟩
    · exact Grothendieck.UnivesalMap_CatVar'_Comm A s.pt FL (FR ⋙ (Down_uni Γ)) Comm
    · exact rfl
    · dsimp
      intros m h1 h2
      have r := Grothendieck.UnivesalMap_Uniq A s.pt FL (FR ⋙ (Down_uni Γ)) Comm (m ⋙ (Down_uni (Grothendieck A))) h1 ?C
      · exact ((Up_Down (Grothendieck.UnivesalMap A s.pt FL (FR ⋙ Down_uni ↑Γ) Comm) m).mpr r.symm).symm
      · dsimp [CategoryStruct.comp] at h2
        rw [<- Functor.assoc,<- Functor.assoc] at h2
        exact ((Up_Down (((m ⋙ Down_uni (Grothendieck A)) ⋙ Grothendieck.forget A)) s.snd).mp h2)

-- This converts the proof of the limit to the proof of a pull back
theorem GrothendieckLimisPullBack {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) :
  @IsPullback (Cat.{u,u+1}) _
  (Cat.of (ULift.{u+1,u} (Grothendieck A)))
  (Cat.of PCat.{u,u}) (Cat.of (ULift.{u+1,u} Γ))
  (Cat.of Cat.{u,u})
  ((Down_uni (Grothendieck A)) ⋙ (CatVar' Γ A))
  ((Down_uni (Grothendieck A)) ⋙ (Grothendieck.forget A) ⋙ (Up_uni Γ))
  (PCat.forgetPoint)
  ((Down_uni Γ) ⋙ A) := by
    fconstructor
    · constructor
      exact Comm A
    · constructor
      exact GrothendieckLimisLim A

end GrothendieckPullBack
section PointedPullBack
/-
In this section we prove that the following square is a PullBack

      PGrpd---PGrpd.forgetToCat--->PCat
        |                           |
        |                           |
 PGrpd.forgetPoint           PCat.forgetPoint
        |                           |
        v                           v
      Grpd----Grpd.forgetToCat---->Cat
-/

/-This is the proof that the diagram commutes-/
theorem PComm : PGrpd.forgetToCat.{u,u} ⋙ PCat.forgetPoint.{u,u} = PGrpd.forgetPoint.{u,u} ⋙ Grpd.forgetToCat.{u,u} := by
  simp[PGrpd.forgetToCat,PCat.forgetPoint,PGrpd.forgetPoint,Grpd.forgetToCat,Functor.comp]
  congr

-- This is the type of cones
abbrev PointedCones := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} Grpd.{u,u})
  (Cat.of.{u,u+1} PCat.{u,u})
  (Cat.of.{u,u+1} Cat.{u,u})
  (Grpd.forgetToCat)
  PCat.forgetPoint.{u,u}

-- This is the cone we will show to be the limit
abbrev PointedLim : PointedCones :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of.{u,u+1} Grpd.{u,u})
    (Cat.of.{u,u+1} PCat.{u,u})
    (Cat.of.{u,u+1} Cat.{u,u})
    (Grpd.forgetToCat)
    PCat.forgetPoint.{u,u}
    (Cat.of PGrpd)
    PGrpd.forgetPoint
    PGrpd.forgetToCat
    PComm

/-- This is the construction of the universal map for the limit-/
def Pointed.UnivesalMap (C : Cat.{u,u+1}) (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Grpd.{u,u})(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ Grpd.forgetToCat) : C ⥤ PGrpd where
  obj x := by
    fapply PGrpd.fromGrpd
    · exact F2.obj x
    · have eq := Functor.congr_obj Comm x
      simp [PCat.forgetPoint, Grpd.forgetToCat,Cat.of,Bundled.of] at eq
      have eq' := congrArg Bundled.α eq
      simp at eq'
      rw [<- eq']
      exact (F1.obj x).str.pt
  map f := by
    simp [Quiver.Hom]
    fconstructor
    · exact F2.map f
    · rename_i X Y
      have r1 := (ForgetPointFunctor (F1.obj Y)).map ((F1.map f).point)
      have r2 := (CastFunc Comm Y).functor.map r1
      refine eqToHom ?A ≫ r2 ≫ eqToHom ?B
      · sorry
      · sorry

/- The proof of uniquness of the universal map-/
def Pointed.UnivesalMap_Uniq (s : PointedCones) : s ⟶ PointedLim := by
  refine { hom := ?hom, w := ?w }
  · sorry
  · sorry

/- The proof that PointedLim is a limit-/
def PointedLimisLim : Limits.IsLimit PointedLim := by
  refine Limits.PullbackCone.isLimitAux' PointedLim ?_
  intros s
  fconstructor
  · sorry
  · refine ⟨?_,?_,?_⟩
    · sorry
    · sorry
    · sorry

end PointedPullBack
end Pullbacks

section NaturalModelBase

def CatLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
    obj x := Cat.of (ULift.{u + 1, u} ↑x)
    map {x y} f := (Down_uni x) ⋙ f ⋙ (Up_uni y)

def CatLift_BackDown (C : Cat.{u,u}) : CatLift.obj C ⥤ C where
    obj x := x.down
    map f := f

def CatLift_BackUp (C : Cat.{u,u}) : C ⥤ CatLift.obj C where
    obj x := {down := x}
    map f := f

def PshGrpd : Cat.{u,u+1} ⥤ (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) := by
  refine yoneda ⋙ ?_
  refine (whiskeringLeft (Grpd.{u,u}ᵒᵖ) (Cat.{u,u+1}ᵒᵖ) (Type (u + 1))).obj ?_
  refine Grpd.forgetToCat.op ⋙ CatLift.op

instance PshGrpdPreservesLim : Limits.PreservesLimits PshGrpd := by
  dsimp [PshGrpd,Limits.PreservesLimits]
  refine @Limits.compPreservesLimits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact yonedaFunctorPreservesLimits
  · refine @Adjunction.rightAdjointPreservesLimits ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · refine @Functor.lan ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact (Grpd.forgetToCat.op ⋙ CatLift.op)
      · intro F
        exact Functor.instHasLeftKanExtension (Grpd.forgetToCat.op ⋙ CatLift.op) F
    · exact (Grpd.forgetToCat.op ⋙ CatLift.op).lanAdjunction (Type (u + 1))

-- This is a Covariant Functor that takes a Groupoid Γ to Γ ⥤ Grpd
def Ty_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := x.unop ⥤ Grpd.{u,u}
  map f A := f.unop ⋙ A

def Ty_functor_iso_PshGrpd_Grpd : Ty_functor ≅ PshGrpd.obj (Cat.of Grpd.{u,u}) where
  hom := by
    fconstructor
    · unfold Ty_functor
      unfold PshGrpd
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackDown (Grpd.forgetToCat.obj X)
      · exact 𝟭 Grpd
    · simp [Ty_functor,PshGrpd]
      intros X Y f
      exact rfl
  inv := by
    fconstructor
    · unfold Ty_functor
      unfold PshGrpd
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackUp (Grpd.forgetToCat.obj X)
      · exact 𝟭 Grpd
    · simp [Ty_functor,PshGrpd]
      intros X Y f
      exact rfl

-- This is a Covariant Functor that takes a Groupoid Γ to Γ ⥤ PointedGroupoid
def Tm_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := x.unop ⥤ PGrpd.{u,u}
  map f A := f.unop ⋙ A

-- I am not sure if this iso will be helpfull but it works as a sanity check to make sure Tm is defined correctly
def Tm_functor_iso_PshGrpd_PGrpd : Tm_functor ≅ PshGrpd.obj (Cat.of PGrpd.{u,u}) where
  hom := by
    fconstructor
    · unfold Tm_functor
      unfold PshGrpd
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackDown (Grpd.forgetToCat.obj X)
      · exact 𝟭 PGrpd
    · simp [Ty_functor,PshGrpd]
      intros X Y f
      exact rfl
  inv := by
    fconstructor
    · unfold Tm_functor
      unfold PshGrpd
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackUp (Grpd.forgetToCat.obj X)
      · exact 𝟭 PGrpd
    · simp [Ty_functor,PshGrpd]
      intros X Y f
      exact rfl

-- This is the typing natural transformation
def tp_NatTrans : Tm_functor ⟶ Ty_functor where
  app x := by
    intro a
    exact a ⋙ PGrpd.forgetPoint

-- This is the var construction of var before applying yoneda
def var' (Γ : Grpd)(A : Γ ⥤ Grpd) : (GroupoidalGrothendieck A) ⥤ PGrpd where
  obj x := ⟨(A.obj x.base), (PointedGroupoid.of (A.obj x.base) x.fiber)⟩
  map f := ⟨A.map f.base, f.fiber⟩
  map_id x := by
    dsimp
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    apply PointedFunctor.ext
    simp[CategoryStruct.id]
    simp[CategoryStruct.id,PointedFunctor.id]
  map_comp {x y z} f g := by
    dsimp [CategoryStruct.comp,PointedFunctor.comp]
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    let _ := (PointedCategory.of (A.obj z.base) z.fiber)
    apply PointedFunctor.ext
    simp [Grpd.forgetToCat]
    simp[A.map_comp,CategoryStruct.comp]

/-

GGrothendieck A -----var'--------> PGrpd---PGrpd.forgetToCat--->PCat
        |                             |                           |
        |                             |                           |
GGrothendieck.forget           PGrpd.forgetPoint         PCat.forgetPoint
        |                             |                           |
        v                             v                           v
        Γ--------------A-----------> Grpd----Grpd.forgetToCat---->Cat
-/

theorem LeftSquareComutes {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : (Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A) ⋙ PGrpd.forgetPoint
 = ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ)) ⋙ (Down_uni Γ) ⋙ A := by sorry

-- This is the type of cones
abbrev GroupoidCones {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} (ULift.{u+1,u} Γ))
  (Cat.of.{u,u+1} PGrpd.{u,u})
  (Cat.of.{u,u+1} Grpd.{u,u})
  ((Down_uni Γ) ⋙ A)
  PGrpd.forgetPoint.{u,u}

-- This is the cone we will prove is the limit
abbrev GroupoidLim {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}): (GroupoidCones A) :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of (ULift.{u + 1, u} Γ))
    (Cat.of PGrpd.{u,u})
    (Cat.of Grpd.{u,u})
    ((Down_uni Γ) ⋙ A)
    (PGrpd.forgetPoint.{u,u})
    (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A)))
    (Down_uni (GroupoidalGrothendieck A) ⋙ GroupoidalGrothendieck.forget ⋙ Up_uni Γ)
    ((Down_uni (GroupoidalGrothendieck A)) ⋙ var' Γ A)
    (LeftSquareComutes A)

def PBasLim {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : Limits.IsLimit (GroupoidLim A) := by
  dsimp [GroupoidLim]
  refine @Limits.leftSquareIsPullback (Cat.{u,u+1}) _
    (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A)))
    (Cat.of PGrpd.{u,u})
    (Cat.of PCat.{u,u})
    (Cat.of (ULift.{u+1,u} Γ))
    (Cat.of Grpd.{u,u})
    (Cat.of Cat.{u,u})
    ((Down_uni (GroupoidalGrothendieck A)) ⋙ var' Γ A)
    (PGrpd.forgetToCat)
    ((Down_uni Γ) ⋙ A)
    (Grpd.forgetToCat)
    ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ))
    (PGrpd.forgetPoint)
    (PCat.forgetPoint)
    ?_
    PComm
    PointedLimisLim
    ?H'
  sorry

def PBasPB {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : @IsPullback (Cat.{u,u+1}) _
  (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A)))
  (Cat.of PGrpd.{u,u})
  (Cat.of (ULift.{u+1,u} Γ))
  (Cat.of Grpd.{u,u})
  ((Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A))
  ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ))
  (PGrpd.forgetPoint)
  ((Down_uni Γ) ⋙ A) := by
    refine IsPullback.flip ?_ -- This filips the pullback, There is on that is done sidways further up that should be fixed
    fconstructor
    · constructor
      exact LeftSquareComutes A
    · constructor
      exact PBasLim A

def PshGrpdPB {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : @IsPullback (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) _
  (PshGrpd.obj (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A))))
  (PshGrpd.obj (Cat.of PGrpd.{u,u}))
  (PshGrpd.obj (Cat.of (ULift.{u+1,u} Γ)))
  (PshGrpd.obj (Cat.of Grpd.{u,u}))
  (PshGrpd.map ((Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A)))
  (PshGrpd.map ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ)))
  (PshGrpd.map (PGrpd.forgetPoint))
  (PshGrpd.map ((Down_uni Γ) ⋙ A)) := Functor.map_isPullback PshGrpd (PBasPB A)


open GroupoidalGrothendieck

-- Here I am using sGrpd to be a small category version of Grpd. There is likely a better way to do this.
def sGrpd := ULiftHom.{u+1} Grpd.{u,u}
  deriving SmallCategory

def sGrpd.of (C : Type u) [Groupoid.{u} C] : sGrpd.{u} := Grpd.of C

def SmallGrpd.forget : sGrpd.{u} ⥤ Grpd.{u,u} where
  obj x := Grpd.of x.α
  map f := f.down

def PshsGrpd : (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) ⥤ (sGrpd.{u}ᵒᵖ ⥤ Type (u + 1)) := (whiskeringLeft _ _ _).obj SmallGrpd.forget.op


instance PshsGrpdPreservesLim : Limits.PreservesLimits PshsGrpd := by
  dsimp [PshsGrpd,Limits.PreservesLimits]
  exact whiskeringLeftPreservesLimits SmallGrpd.forget.op

#check GroupoidalGrothendieck

#check IsPullback

instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
  Ty := PshsGrpd.obj (PshGrpd.obj (Cat.of Grpd.{u,u}))
  Tm := PshsGrpd.obj (PshGrpd.obj (Cat.of PGrpd.{u,u}))
  tp := PshsGrpd.map (PshGrpd.map (PGrpd.forgetPoint))
  ext Γ A := by
    let Γ' : Grpd.{u,u} := SmallGrpd.forget.obj Γ
    let A' : Γ' ⥤ Grpd.{u,u} := by
      have h1 := yonedaEquiv.toFun A
      dsimp [PshsGrpd,PshGrpd,CatLift,Quiver.Hom,Cat.of,Bundled.of,Grpd.forgetToCat] at h1
      refine ?_ ⋙ h1
      exact Up_uni ↑Γ'
    exact sGrpd.of (Grpd.of (GroupoidalGrothendieck A'))
  disp Γ A := by
    constructor
    simp[ULiftHom.objDown,Quiver.Hom]
    refine Grothendieck.forget _ ⋙ ?_
    exact 𝟭 ↑(SmallGrpd.forget.obj Γ)
  var Γ A := by
    refine yonedaEquiv.invFun ?_
    simp[PshGrpd,CatLift,Cat.of,Bundled.of,Quiver.Hom,Grpd.forgetToCat,SmallGrpd.forget]
    have v' := var' _ (Up_uni (@Bundled.α Groupoid Γ) ⋙ yonedaEquiv A)
    refine ?_ ⋙ v'
    exact Down_uni (GroupoidalGrothendieck (Up_uni (@Bundled.α Groupoid Γ) ⋙ yonedaEquiv A))
  disp_pullback A := by
    rename_i Γ
    let Γ' : Grpd.{u,u} := SmallGrpd.forget.obj Γ
    let A' : Γ' ⥤ Grpd.{u,u} := by
      have h1 := yonedaEquiv.toFun A
      dsimp [PshsGrpd,PshGrpd,CatLift,Quiver.Hom,Cat.of,Bundled.of,Grpd.forgetToCat] at h1
      refine ?_ ⋙ h1
      exact Up_uni ↑Γ'
    have pb := Functor.map_isPullback PshsGrpd (PshGrpdPB A')
    dsimp [PshGrpd]
    dsimp [PshGrpd] at pb
    sorry


/-
This is the Natural Model on sGrpd. I am not sure this belongs in this file but I keep it here so that I can
get an idea of what needs to be done.
-/
-- instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
--   Ty := SmallGrpd.forget.op ⋙ Ty_functor
--   Tm := SmallGrpd.forget.op ⋙ Tm_functor
--   tp := NatTrans.hcomp (NatTrans.id SmallGrpd.forget.op) (tp_NatTrans)
--   ext Γ f := sGrpd.of (GroupoidalGrothendieck ((@yonedaEquiv _ _ Γ (SmallGrpd.forget.op ⋙ Ty_functor)).toFun f))
--   disp Γ A := by
--     constructor
--     exact Grothendieck.forget (yonedaEquiv A ⋙ Grpd.forgetToCat)
--   var Γ A := yonedaEquiv.invFun (var' (SmallGrpd.forget.obj Γ) (yonedaEquiv A))
--   disp_pullback A := by
--     rename_i Γ
--     sorry

end NaturalModelBase

instance groupoidULift.{u'} {α : Type u} [Groupoid.{v} α] : Groupoid (ULift.{u'} α) where
  inv f := Groupoid.inv f
  inv_comp _ := Groupoid.inv_comp ..
  comp_inv _ := Groupoid.comp_inv ..

instance groupoidULiftHom.{u'} {α : Type u} [Groupoid.{v} α] : Groupoid (ULiftHom.{u'} α) where
  inv f := .up (Groupoid.inv f.down)
  inv_comp _ := ULift.ext _ _ <| Groupoid.inv_comp ..
  comp_inv _ := ULift.ext _ _ <| Groupoid.comp_inv ..

inductive Groupoid2 : Type (u+2) where
  | small (_ : sGrpd.{u})
  | large (_ : sGrpd.{u+1})

def Groupoid2.toLarge : Groupoid2.{u} → sGrpd.{u+1}
  | .small A => .mk (ULiftHom.{u+1} (ULift.{u+1} A.α))
  | .large A => A

/-- A model of Grpd with an internal universe, with the property that the small universe
injects into the large one. -/
def Grpd2 : Type (u+2) := InducedCategory sGrpd.{u+1} Groupoid2.toLarge
  deriving SmallCategory

section NaturalModelPi

def PolyDataGet (Γ : sGrpdᵒᵖ) (Q : ((NaturalModel.P NaturalModel.tp).obj NaturalModel.Ty).obj Γ) : yoneda.obj (Opposite.unop Γ) ⟶ ((NaturalModel.P NaturalModel.tp).obj NaturalModel.Ty) := by
  apply yonedaEquiv.invFun
  exact Q


instance GroupoidNMSigma : NaturalModel.NaturalModelSigma sGrpd.{u} where
  Sig := by
    fconstructor
    . dsimp [Quiver.Hom]
      intro Γ Q
      have φ' := PolyDataGet Γ Q
      have pp := UvPoly.polyPair (NaturalModel.uvPoly NaturalModel.tp) (yoneda.obj Γ.unop) (NaturalModel.Ty) φ'
      rcases pp with ⟨A,pb⟩
      let dp := NaturalModel.disp_pullback A
      let help : yoneda.obj (NaturalModel.ext (Opposite.unop Γ) A) ≅ (Limits.pullback A NaturalModel.tp) := by
        exact CategoryTheory.IsPullback.isoPullback (CategoryTheory.IsPullback.flip dp)
      let h' := (help.hom.app Γ)
      let pb' := pb.app Γ
      dsimp [NaturalModel.uvPoly] at pb'
      let diag := h' ≫ pb'
      dsimp[NaturalModel.ext,Quiver.Hom,ULiftHom.objDown,sGrpd.of] at diag


      constructor


      sorry
    . intros Γ1 Γ2 f
      simp
      aesop_cat
  pair := by
    sorry
  Sig_pullback := by
    sorry




instance GroupoidNMPi : NaturalModel.NaturalModelPi sGrpd.{u} where
  Pi := by
    sorry
  lam := by
    sorry
  Pi_pullback := by
    apply?



  pair := by
    sorry
  Sig_pullback := by
    sorry



end NaturalModelPi

end GroupoidModelPi
end GroupoidModel
end NaturalModelPi
end NaturalModel
end CategoryTheory
end Lean


end NaturalModelPi
