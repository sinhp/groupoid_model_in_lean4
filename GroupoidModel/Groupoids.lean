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
--

universe u v

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



section GroupoidGrothendieck

variable {G : Type u} [Groupoid G] (F : G ⥤ Grpd.{u,u})

/-
  In Mathlib.CategoryTheory.Grothendieck the Grothendieck construction is done but into Cat.
  By composing a functor into Grpd with Grpd.forgetToCat we can use this construction. Then
  we show that what we get is a Groupoid.
-/

def GroupoidGrothendieck := Grothendieck (F ⋙ Grpd.forgetToCat)

instance : Category (GroupoidGrothendieck F) := inferInstanceAs (Category (Grothendieck _))

instance (g : G) : Groupoid ((F ⋙ Grpd.forgetToCat).obj g) where
  inv f := ((F.obj g).str').inv f

instance mapsToIso {X Y : GroupoidGrothendieck F} (f : Grothendieck.Hom X Y) :
    Iso (F.obj X.base) (F.obj Y.base) where
  hom := F.map f.base
  inv := F.map (Groupoid.inv f.base)

def Grothendieck.inv {X Y : GroupoidGrothendieck F}
    (f : X ⟶ Y) : Y ⟶ X where
  base := Groupoid.inv f.base
  fiber := Groupoid.inv ((F.map (Groupoid.inv f.base)).map f.fiber) ≫
    eqToHom (by simpa only [Functor.map_comp, Functor.map_id] using
      congr((F.map $(Groupoid.comp_inv f.base)).obj X.fiber))

instance : Groupoid (GroupoidGrothendieck F) where
  inv f := Grothendieck.inv F f
  inv_comp f := by
    suffices ∀ {Z g} (_ : g ≫ f.base = Z) (_ : Z = 𝟙 _)
        {g'} (eq : g' ≫ (F.map g).map f.fiber = 𝟙 _)
        (W) (eqW : F.map g ≫ F.map f.base = W)
        (eq2 : ∃ w1 w2, W.map f.fiber = eqToHom w1 ≫ f.fiber ≫ eqToHom w2) h1 h2,
        { base := Z, fiber := eqToHom h1 ≫ (F.map f.base).map (g' ≫ eqToHom h2) ≫ f.fiber } =
        ({..} : Grothendieck.Hom ..) from
      this rfl (Groupoid.inv_comp _) (Groupoid.inv_comp _)
        (W := 𝟙 _) (eqW := by simp) (eq2 := ⟨rfl, rfl, by simp; rfl⟩) ..
    rintro _ g - rfl g' eq _ rfl ⟨w1, w2, eq2 : (F.map f.base).map _ = _⟩ h1 h2; congr
    replace eq := congr((F.map f.base).map $eq)
    simp only [Functor.map_comp, eq2, eqToHom_map, Category.assoc] at eq ⊢
    conv at eq => lhs; slice 1 3
    rw [(comp_eqToHom_iff ..).1 eq]; simp
  comp_inv {X Y} f := by
    suffices ∀ {Z g} (_ : f.base ≫ g = Z) (_ : Z = 𝟙 _)
        {g'} (eq : (F.map g).map f.fiber ≫ g' = 𝟙 _) h1 h2,
        { base := Z, fiber := eqToHom h1 ≫ (F.map g).map f.fiber ≫ g' ≫ eqToHom h2 } =
        ({..} : Grothendieck.Hom ..) by
      exact this rfl (Groupoid.comp_inv _) (Groupoid.comp_inv _) ..
    rintro _ g - rfl g' eq _ _; congr
    slice_lhs 2 3 => apply eq
    erw [Category.id_comp, eqToHom_trans]

def GroupoidGrothendieck.forget : GroupoidGrothendieck F ⥤ G :=
  Grothendieck.forget (F ⋙ Grpd.forgetToCat)

def GroupoidGrothendieck.forget' : GroupoidGrothendieck F ⥤ Grpd.{u,u} where
  obj x := F.obj x.base
  map p := F.map p.base
  map_id _ := F.map_id _
  map_comp _ _ := F.map_comp ..

def GroupoidGrothendieck.functorial {C D : Grpd.{u,u}} (F : C ⥤ D) (G : D ⥤ Grpd.{u,u}) :
    GroupoidGrothendieck (F ⋙ G) ⥤ GroupoidGrothendieck G where
  obj x := by
    constructor
    case base;
    exact (F.obj x.base)
    exact x.fiber
  map f := by
    constructor
    case base;
    exact (F.map f.base)
    exact f.fiber
  map_id x := by
    dsimp [CategoryStruct.id,Grothendieck.id]
    congr
    exact (F.map_id x.base)
    exact (F.map_id x.base)
    simp
  map_comp f g := by
    dsimp [CategoryStruct.comp,Grothendieck.comp]
    congr
    exact (F.map_comp f.base g.base)
    exact (F.map_comp f.base g.base)
    exact (F.map_comp f.base g.base)
    simp

end GroupoidGrothendieck

section HSexp

/-
In this section we go through section 4 of Hofmann and Streicher's original paper
-/

-- Ty of Γ is the type of familiys of groupoids indexed by Γ
abbrev Ty (Γ : Grpd.{u,u}) := Γ ⥤ Grpd.{u,u}

def TySub {Δ Γ : Grpd.{u,u}} (f : Δ ⥤ Γ) : Ty Γ ⥤ Ty Δ := (whiskeringLeft Δ Γ Grpd.{u,u}).obj f

-- This is a Covariant Functor that takes a Groupoid Γ to Ty Γ
def Ty_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := by
    rcases x with ⟨x'⟩
    exact (Ty x')
  map f := by
    intro A
    exact (TySub f.unop).obj A

-- These are the terms of type A. They are Sections Γ ⥤ Ty A
structure Tm {Γ : Grpd.{u,u}} (A : Ty Γ) :=
  obj (g : Γ) : A.obj g
  map {g h : Γ} (p : g ⟶ h) : (A.map p).obj (obj g) ⟶ obj h
  map_id (g : Γ) : (map (𝟙 g)) = eqToHom (by simp; rfl) ≫ 𝟙 (obj g)
  map_comp {g h i : Γ} (p : g ⟶ h) (p' : h ⟶ i) : map (p ≫ p') =
    eqToHom (by simp; rfl) ≫ (A.map p').map (map p) ≫ map p'

theorem Ty_hom_congr_obj {Γ : Grpd.{u,u}} {A : Ty Γ} (a : Tm A) {g h : Γ} {p p' : g ⟶ h}
    (eq : p = p') : (A.map p).obj (a.obj g) = (A.map p').obj (a.obj g) := by
  rw [eq]

theorem Tm_hom_congr {Γ : Grpd.{u,u}} {A : Ty Γ} (a : Tm A) {g h : Γ} {p p': g ⟶ h}
    (eq : p = p') : a.map p = eqToHom (Ty_hom_congr_obj a eq) ≫ a.map p' := by
  have h : HEq (a.map p) (a.map p') := by
    rw [eq]
  rw [(Functor.conj_eqToHom_iff_heq (a.map p) (a.map p') (Ty_hom_congr_obj a eq) (rfl)).mpr h]
  simp

-- This should be made functorial. Tm is given a category structure farther down
def TmSub {Δ Γ : Grpd.{u,u}} {A : Ty Γ} (a : Tm A) (f : Δ ⥤ Γ) : Tm ((TySub f).obj A) where
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
    exact Σ(t : Ty x'), Tm t
  map f := by
    intro input
    exact ⟨_,TmSub input.snd f.unop⟩

-- This is the typing natral transformation
def tp_NatTrans : NatTrans Tm_functor Ty_functor where
  app x := by
    dsimp [Tm_functor,Ty_functor,Quiver.Hom]
    intro a
    exact a.fst

def TmSubToGrothendieckFunc {Δ Γ : Grpd.{u,u}} {A : Ty Γ} (f : Δ ⟶ Γ) (M : Tm ((TySub f).obj A)) :
    Δ ⥤ GroupoidGrothendieck A where
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

def TmSubToGrothendieckFuncWrapper {Δ Γ : Grpd.{u,u}} {A : Ty Γ}
    (S : Σ f : Δ ⟶ Γ, Tm ((TySub f).obj A)) : Δ ⥤ GroupoidGrothendieck A :=
  TmSubToGrothendieckFunc S.fst S.snd

def GrothendieckFuncToTmSub {Δ Γ : Grpd.{u,u}} {A : Ty Γ} (F : Δ ⥤ GroupoidGrothendieck A) :
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

theorem Left_Inv {Δ Γ : Grpd.{u,u}} {A : Ty Γ} (S : Σ f: Δ ⟶ Γ, Tm ((TySub f).obj A)) :
    GrothendieckFuncToTmSub (TmSubToGrothendieckFuncWrapper S) = S := by congr

theorem Right_Inv {Δ Γ : Grpd.{u,u}} {A : Ty Γ} (F : Δ ⥤ GroupoidGrothendieck A) :
    TmSubToGrothendieckFuncWrapper (GrothendieckFuncToTmSub F) = F := by
  congr

structure GrothendieckSection (Γ : Grpd.{u,u}) (A : Ty Γ) where
  func : Γ ⥤ GroupoidGrothendieck A
  s : func ⋙ GroupoidGrothendieck.forget A = 𝟙 Γ

def TmToGrothendieckFunc {Γ : Grpd.{u,u}} {A : Ty Γ} (M : Tm A) : Γ ⥤ GroupoidGrothendieck A where
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
def TmToGrothendieckSection {Γ : Grpd.{u,u}} {A : Ty Γ} (M : Tm A) : GrothendieckSection Γ A where
  func := TmToGrothendieckFunc M
  s := rfl

-- This can be expanded to a Groupoid
instance TmCategory {Γ : Grpd.{u,u}} {A : Ty Γ} : Category (Tm A) where
  Hom x y := (TmToGrothendieckFunc x) ⟶ (TmToGrothendieckFunc y)
  id x := 𝟙 (TmToGrothendieckFunc x)
  comp f g := NatTrans.vcomp f g

end HSexp


section NM
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
  ext Γ f := sGrpd.of (GroupoidGrothendieck ((@yonedaEquiv _ _ Γ (SmallGrpd.forget.op ⋙ Ty_functor)).toFun f))
  disp Γ A := by
    constructor
    exact Grothendieck.forget (yonedaEquiv A ⋙ Grpd.forgetToCat)
  var Γ A := by
    sorry
  disp_pullback A := by
    dsimp
    sorry

end NM

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
