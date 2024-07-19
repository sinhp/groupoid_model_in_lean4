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
import Mathlib.CategoryTheory.Category.Pointed
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

section PointedCategorys

structure PointedCategory.{w,z} extends Pointed.{z} where
  cat : Category.{w} X

namespace PointedCategory

instance : CoeSort PointedCategory Type* := CoeSort.mk (fun(x) => x.X)

instance (P : PointedCategory) : Category P.X := P.cat

def of.{w,z} {X : Type z} (point : X)[cat : Category.{w} X]: PointedCategory :=
  ⟨⟨X,point⟩,cat⟩

@[ext]
protected structure Hom.{w,z} (P Q : PointedCategory.{w,z}) : Type (max w z) where
  toFunc : P.X ⥤ Q.X
  obj_point : toFunc.obj P.point = Q.point

namespace Hom

@[simps]
def id.{w,z} (P : PointedCategory.{w,z}) : PointedCategory.Hom.{w,z} P P where
  toFunc := Functor.id P.X
  obj_point := rfl

@[simps]
def comp.{w,z} {P Q R: PointedCategory.{w,z}} (f : PointedCategory.Hom.{w,z} P Q) (g : PointedCategory.Hom.{w,z} Q R) : PointedCategory.Hom.{w,z} P R :=
  ⟨f.toFunc ⋙ g.toFunc, by rw [Functor.comp_obj, f.obj_point, g.obj_point]⟩

end Hom

instance largeCategory : LargeCategory PointedCategory where
  Hom := PointedCategory.Hom
  id := Hom.id
  comp := @Hom.comp

end PointedCategory

structure PointedGroupoid.{w,z} extends Pointed.{z} where
  grpd : Groupoid.{w} X

namespace PointedGroupoid

instance : CoeSort PointedGroupoid Type* := CoeSort.mk (fun(x) => x.X)

instance toPointedCategory : CoeSort PointedGroupoid PointedCategory := CoeSort.mk (fun(x) => ⟨⟨x.X,x.point⟩,x.grpd.toCategory⟩)

def of.{w,z} {X : Type z} (point : X)[grpd : Groupoid.{w} X]: PointedGroupoid :=
  ⟨⟨X,point⟩,grpd⟩

instance largeCategory : LargeCategory PointedGroupoid where
  Hom P Q := PointedCategory.Hom P Q
  id P := PointedCategory.Hom.id P
  comp f g := PointedCategory.Hom.comp f g

end PointedGroupoid



end PointedCategorys

section NaturalModelBase

def TySub {Δ Γ : Grpd.{u,u}} (f : Δ ⥤ Γ) : (Γ ⥤ Grpd.{u,u}) ⥤ (Δ ⥤ Grpd.{u,u}):= (whiskeringLeft Δ Γ Grpd.{u,u}).obj f

-- This is a Covariant Functor that takes a Groupoid Γ to Ty Γ
def Ty_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := x.unop ⥤ Grpd.{u,u}
  map f A := f.unop ⋙ A --(TySub f.unop).obj A

-- These are the terms of type A. They are Sections Γ ⥤ Ty A
structure Tm {Γ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) :=
  obj (g : Γ) : A.obj g
  map {g h : Γ} (p : g ⟶ h) : (A.map p).obj (obj g) ⟶ obj h
  map_id (g : Γ) : (map (𝟙 g)) = eqToHom (by simp; rfl) ≫ 𝟙 (obj g)
  map_comp {g h i : Γ} (p : g ⟶ h) (p' : h ⟶ i) : map (p ≫ p') =
    eqToHom (by simp; rfl) ≫ (A.map p').map (map p) ≫ map p'

theorem Ty_hom_congr_obj {Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (a : Tm A) {g h : Γ} {p p' : g ⟶ h}
    (eq : p = p') : (A.map p).obj (a.obj g) = (A.map p').obj (a.obj g) := by
  rw [eq]

theorem Tm_hom_congr {Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (a : Tm A) {g h : Γ} {p p': g ⟶ h}
    (eq : p = p') : a.map p = eqToHom (Ty_hom_congr_obj a eq) ≫ a.map p' := by
  have h : HEq (a.map p) (a.map p') := by
    rw [eq]
  rw [(Functor.conj_eqToHom_iff_heq (a.map p) (a.map p') (Ty_hom_congr_obj a eq) (rfl)).mpr h]
  simp

-- This should be made functorial. Tm is given a category structure farther down
def TmSub {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (a : Tm A) (f : Δ ⥤ Γ) : Tm ((TySub f).obj A) where
  obj g := a.obj (f.obj g)
  map p := a.map (f.map p)
  map_id g := by
    have h' := (eqToHom_comp_iff ?_ (𝟙 (a.obj (f.obj g))) (a.map (𝟙 (f.obj g)))).mpr (a.map_id (f.obj g))
    case refine_1; simp [CategoryStruct.id]
    rw [<- h']
    simp
    have eq : f.map (𝟙 g) = 𝟙 (f.obj g) := f.map_id g
    rw [Tm_hom_congr a eq]
  map_comp p p':= by
    dsimp [TySub]
    have h := (a.map_comp (f.map p) (f.map p'))
    have eq : (f.map p ≫ f.map p') = f.map (p ≫ p') := (f.map_comp p p').symm
    have h' := Tm_hom_congr a eq
    rw [h'] at h
    have h'' := (eqToHom_comp_iff _ _ (a.map (f.map (p ≫ p')))).mp h
    rw [h'']
    simp

-- This is a Covariant Functor that takes a Groupoid Γ to dependent pairs of (A ∈ Ty Γ) and (t ∈ Tm A)
def Tm_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := by
    rcases x with ⟨x'⟩
    exact Σ(t : x' ⥤ Grpd.{u,u}), Tm t
  map f := by
    intro input
    exact ⟨_,TmSub input.snd f.unop⟩

-- This is the typing natral transformation
def tp_NatTrans : NatTrans Tm_functor Ty_functor where
  app x := by
    dsimp [Tm_functor,Ty_functor,Quiver.Hom]
    intro a
    exact a.fst

def TmSubToGrothendieckFunc {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (f : Δ ⟶ Γ) (M : Tm ((TySub f).obj A)) :
    Δ ⥤ GroupoidalGrothendieck A where
  obj x := {base := f.obj x, fiber := M.obj x}
  map p := {base := f.map p, fiber := M.map p}
  map_id x := by
    simp
    congr
    simp
    simp [M.map_id,CategoryStruct.id]
    dsimp [eqToHom,cast]
    simp
  map_comp p p' := by
    simp [CategoryStruct.comp,Grothendieck.comp]
    apply Grothendieck.ext <;> simp
    rw [M.map_comp]
    simp [TySub,Grpd.forgetToCat]

def TmSubToGrothendieckFuncWrapper {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}}
    (S : Σ f : Δ ⟶ Γ, Tm ((TySub f).obj A)) : Δ ⥤ GroupoidalGrothendieck A :=
  TmSubToGrothendieckFunc S.fst S.snd

def GrothendieckFuncToTmSub {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (F : Δ ⥤ GroupoidalGrothendieck A) :
    Σ f : Δ ⥤ Γ, Tm ((TySub f).obj A) where
  fst := F ⋙ Grothendieck.forget (A ⋙ Grpd.forgetToCat)
  snd := by
    dsimp [TySub, Grothendieck.forget]
    constructor
    case obj => intro g; exact (F.obj g).fiber
    case map => intro _ _ p; dsimp; exact (F.map p).fiber
    case map_id => intro g; rw [Grothendieck.congr (F.map_id g)]; simp [CategoryStruct.id]
    case map_comp =>
      intro g h i p p'; simp
      rw [Grothendieck.congr (F.map_comp p p')]
      simp [CategoryStruct.comp,Grpd.forgetToCat]

theorem Left_Inv {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (S : Σ f: Δ ⟶ Γ, Tm ((TySub f).obj A)) :
    GrothendieckFuncToTmSub (TmSubToGrothendieckFuncWrapper S) = S := by congr

theorem Right_Inv {Δ Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (F : Δ ⥤ GroupoidalGrothendieck A) :
    TmSubToGrothendieckFuncWrapper (GrothendieckFuncToTmSub F) = F := by
  congr

structure GrothendieckSection (Γ : Grpd.{u,u}) (A : Γ ⥤ Grpd.{u,u}) where
  func : Γ ⥤ GroupoidalGrothendieck A
  s : func ⋙ GroupoidalGrothendieck.forget = 𝟙 Γ

def TmToGrothendieckFunc {Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (M : Tm A) : Γ ⥤ GroupoidalGrothendieck A where
  obj g := {base := g, fiber := M.obj g}
  map p := {base := p, fiber := M.map p}
  map_id g := by
    simp
    rw [(M.map_id g)]
    simp [CategoryStruct.id,Grothendieck.id]
  map_comp p p' := by
    simp
    rw [M.map_comp p p']
    simp [CategoryStruct.comp,Grothendieck.comp, Grpd.forgetToCat]

/-
This is a bijection but it is quite dificult to show in lean. I have worked on it for a bit by the inverse
function requires so strange type casting that I can't seem to get to work
-/
def TmToGrothendieckSection {Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} (M : Tm A) : GrothendieckSection Γ A where
  func := TmToGrothendieckFunc M
  s := rfl

-- This can be expanded to a Groupoid
instance TmCategory {Γ : Grpd.{u,u}} {A : Γ ⥤ Grpd.{u,u}} : Category (Tm A) where
  Hom x y := (TmToGrothendieckFunc x) ⟶ (TmToGrothendieckFunc y)
  id x := 𝟙 (TmToGrothendieckFunc x)
  comp f g := NatTrans.vcomp f g


open GroupoidalGrothendieck

-- Here I am useing sGrpd to be a small category version of Grpd. There is likely a better way to do this.
def sGrpd := ULiftHom.{u+1} Grpd.{u,u}
  deriving SmallCategory

def sGrpd.of (C : Type u) [Groupoid.{u} C] : sGrpd.{u} := Grpd.of C

def SmallGrpd.forget : sGrpd.{u} ⥤ Grpd.{u,u} where
  obj x := Grpd.of x.α
  map f := f.down

/-
This is the Natural Model on sGrpd. I am not sure this belongs in this file but I keep it here so that I can
get an idea of what needs to be done.
-/
instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
  Ty := SmallGrpd.forget.op ⋙ Ty_functor
  Tm := SmallGrpd.forget.op ⋙ Tm_functor
  tp := NatTrans.hcomp (NatTrans.id SmallGrpd.forget.op) (tp_NatTrans)
  ext Γ f := sGrpd.of (GroupoidalGrothendieck ((@yonedaEquiv _ _ Γ (SmallGrpd.forget.op ⋙ Ty_functor)).toFun f))
  disp Γ A := by
    constructor
    exact Grothendieck.forget (yonedaEquiv A ⋙ Grpd.forgetToCat)
  var Γ A := by
    sorry
  disp_pullback A := by
    dsimp
    sorry

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
