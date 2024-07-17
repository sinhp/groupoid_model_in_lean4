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

variable {G : Grpd.{u,u}}(F : G ⥤ Grpd.{u,u})

/-
  In Mathlib.CategoryTheory.Grothendieck the Grothendieck construction is done but into Cat.
  By composing a functor into Grpd with Grpd.forgetToCat we can use this construction. Then
  we show that what we get is a Groupoid.
-/

def GroupoidGrothendieck := Grothendieck (F ⋙ Grpd.forgetToCat)

instance (g : G) : Groupoid ((F ⋙ Grpd.forgetToCat).obj g) where
  inv f := ((F.obj g).str').inv f

instance mapsToIso {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X Y) : Iso (F.obj X.base) (F.obj Y.base) where
  hom := F.map f.base
  inv := F.map (Groupoid.inv f.base)

def Grothendieck.inv {X Y : GroupoidGrothendieck F} (f : Grothendieck.Hom X Y) : Grothendieck.Hom Y X where
  base := Groupoid.inv (f.base)
  fiber := by
    have l_eq :  ((F ⋙ Grpd.forgetToCat).map (Groupoid.inv f.base)).obj Y.fiber = (CategoryTheory.inv (F.map f.base)).obj Y.fiber := by
      dsimp[Grpd.forgetToCat]
      rw [Groupoid.inv_eq_inv,Functor.map_inv]
    have r_eq : (CategoryTheory.inv (F.map f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber) = X.fiber := by
      dsimp[Grpd.forgetToCat]
      have h : (CategoryTheory.inv (F.map f.base)).obj ((F.map f.base).obj X.fiber) = ((F.map f.base) ≫ (CategoryTheory.inv (F.map f.base))).obj X.fiber := rfl
      rw [h]
      simp [CategoryStruct.id]
    exact (eqToHom l_eq) ≫ Groupoid.inv ((CategoryTheory.inv (F.map f.base)).map f.fiber) ≫ (eqToHom r_eq)

theorem Grothendieck.Hom_congr_fiber_help {C : Type u}[Category C](F : C ⥤ Cat) {X Y : Grothendieck F} {f f' : X ⟶ Y}(eq : f = f')
  : (F.map f.base).obj X.fiber = (F.map f'.base).obj X.fiber := by
    refine (Functor.congr_obj (congrArg F.map (?_)) X.fiber)
    exact congrArg Hom.base eq

theorem Grothendieck.Hom_congr_fiber {C : Type u}[Category C](F : C ⥤ Cat){X Y : Grothendieck F}{f f' : X ⟶ Y}(eq : f = f')
  : f.fiber = (eqToHom (Grothendieck.Hom_congr_fiber_help F eq)) ≫ f'.fiber := by
    have h : HEq (f.fiber) (f'.fiber) := by
      rw[eq]
    have h' := (Functor.conj_eqToHom_iff_heq (f.fiber) (f'.fiber) (Grothendieck.Hom_congr_fiber_help F eq) (rfl)).mpr h
    rw [h']
    simp

--These are some lemmas I needed to help show that inv works. They should be neamed more clearly
lemma help1_eql {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : (F.map f.base).obj ((inv (F.map f.base)).obj Y.fiber) = Y.fiber := by
  have h : (F.map f.base).obj ((inv (F.map f.base)).obj Y.fiber) = ((inv (F.map f.base)) ≫ (F.map f.base)).obj Y.fiber := rfl
  rw [h]
  simp [CategoryStruct.id]

lemma help1_eqr {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : ((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber = (F.map f.base).obj ((inv (F.map f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber)) := by
  have h : (F.map f.base).obj ((inv (F.map f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber)) = ((inv (F.map f.base)) ≫ (F.map f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber) := rfl
  rw [h]
  simp [CategoryStruct.id]

lemma help1 {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : inv ((F.map f.base).map ((inv (F.map f.base)).map f.fiber)) = (eqToHom (help1_eql F f)) ≫ (inv f.fiber) ≫ (eqToHom (help1_eqr F f)) := by
  have h : inv ((F.map f.base).map ((inv (F.map f.base)).map f.fiber)) = inv (((inv (F.map f.base)) ≫ (F.map f.base)).map f.fiber) := by
    congr
  rw [h]
  apply symm
  apply (hom_comp_eq_id (((inv (F.map f.base) ≫ F.map f.base).map f.fiber))).mp
  simp[Grpd.forgetToCat,CategoryStruct.id]
  have temp := Functor.congr_hom ((@inv_comp_eq_id _ _ _ _ (F.map f.base) _ (F.map f.base)).mpr rfl) f.fiber
  simp[temp,CategoryStruct.id]

lemma help2_eql {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : (F.map (Groupoid.inv f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber) = (inv (F.map f.base)).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber) := by simp

lemma help2_eqr {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : (inv (F.map f.base)).obj Y.fiber = (F.map (Groupoid.inv f.base)).obj Y.fiber := by simp

lemma help2 {X Y : GroupoidGrothendieck F}(f : Grothendieck.Hom X  Y) : (F.map (Groupoid.inv f.base)).map f.fiber = (eqToHom (help2_eql F f)) ≫ (inv (F.map f.base)).map f.fiber ≫ (eqToHom (help2_eqr F f)) := by
  have h : F.map (Groupoid.inv f.base) = inv (F.map f.base) := by
    simp[Groupoid.inv_eq_inv]
  rw[Functor.congr_hom h f.fiber]

/-
Because instances to not get lifted to new definitions we have to redefine the category structure of
GroupoidGrothendieck as well as show that it is a Groupoid. There may be a better way to do this.
-/
attribute [local simp] eqToHom_map

instance : Groupoid (GroupoidGrothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp := @fun X Y Z f g => Grothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext
    · simp
    · dsimp [Grpd.forgetToCat] ; rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber] ; simp[CategoryStruct.id]
  id_comp := @fun X Y f => by dsimp; ext <;> simp
  assoc := @fun W X Y Z f g h => by
    dsimp; ext
    · simp
    · dsimp [Grpd.forgetToCat] ; rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber] ; simp[CategoryStruct.id,CategoryStruct.comp]
  inv f := Grothendieck.inv F f
  inv_comp := by
    intros X Y f
    simp
    apply Grothendieck.ext
    simp[Grothendieck.comp,Grothendieck.inv,Grpd.forgetToCat]
    rw[help1 F f]
    simp[CategoryStruct.id]
    simp[Grothendieck.comp,Grothendieck.inv]
  comp_inv := by
    intros X Y f
    simp
    apply Grothendieck.ext
    simp[Grothendieck.comp,Grothendieck.inv,Grpd.forgetToCat]
    rw[help2 F f]
    simp[CategoryStruct.id]
    simp[Grothendieck.comp,Grothendieck.inv]

def GroupoidGrothendieck.forget : GroupoidGrothendieck F ⥤ G := Grothendieck.forget (F ⋙ Grpd.forgetToCat)

def GroupoidGrothendieck.forget' : GroupoidGrothendieck F ⥤ Grpd.{u,u} where
  obj x := F.obj x.base
  map p := F.map p.base
  map_id x := by
    dsimp[CategoryStruct.id]
    rw [F.map_id]
    dsimp[CategoryStruct.id]
  map_comp p p' := by
    dsimp[CategoryStruct.comp]
    rw[F.map_comp]
    dsimp[CategoryStruct.comp]

def GroupoidGrothendieck.functorial {C D :Grpd.{u,u}}(F : C ⥤ D)(G : D ⥤ Grpd.{u,u})
  : GroupoidGrothendieck (F ⋙ G) ⥤ GroupoidGrothendieck G  where
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
      dsimp[CategoryStruct.id,Grothendieck.id]
      congr
      exact (F.map_id x.base)
      exact (F.map_id x.base)
      simp
    map_comp f g := by
      dsimp[CategoryStruct.comp,Grothendieck.comp]
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

def TySub {Δ Γ: Grpd.{u,u}}(f : Δ ⥤ Γ) : (Ty Γ) ⥤ (Ty Δ) := (whiskeringLeft Δ Γ Grpd.{u,u}).obj f

-- This is a Covariant Functor that takes a Groupoid Γ to Ty Γ
def Ty_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := by
    rcases x with ⟨x'⟩
    exact (Ty x')
  map f := by
    intro A
    exact (TySub f.unop).obj A

-- These are the terms of type A. They are Sections Γ ⥤ (Ty A)
structure Tm {Γ : Grpd.{u,u}}(A : Ty Γ) :=
  obj (g : Γ) : A.obj g
  map {g h : Γ}(p : g ⟶ h) : ((A.map p).obj (obj g)) ⟶ (obj h)
  map_id (g : Γ): (map (𝟙 g)) = eqToHom ( Eq.trans (Functor.congr_obj (A.map_id g) (obj g)) rfl) ≫ (𝟙 (obj g))
  map_comp {g h i : Γ}(p : g ⟶ h)(p' : h ⟶ i) : map (p ≫ p') =
    (eqToHom (Eq.mpr (id (congrArg (fun _a ↦ _a.obj (obj g) = (A.map p').obj ((A.map p).obj (obj g))) (A.map_comp p p')))
    (of_eq_true (eq_self ((A.map p').obj ((A.map p).obj (obj g))))))) ≫ ((A.map p').map (map p)) ≫ (map p')

theorem Ty_hom_congr_obj {Γ : Grpd.{u,u}}{A : Ty Γ}(a : Tm A){g h : Γ}{p p': g ⟶ h}(eq : p = p') : (A.map p).obj (a.obj g) = (A.map p').obj (a.obj g) := by
  refine Functor.congr_obj (?_) (a.obj g)
  rw [eq]

theorem Tm_hom_congr{Γ : Grpd.{u,u}}{A : Ty Γ}(a : Tm A){g h : Γ}{p p': g ⟶ h}(eq : p = p') : a.map p = eqToHom (Ty_hom_congr_obj a eq) ≫ a.map p' := by
  have h : HEq (a.map p) (a.map p') := by
    rw[eq]
  have h' := (Functor.conj_eqToHom_iff_heq (a.map p) (a.map p') (Ty_hom_congr_obj a eq) (rfl)).mpr h
  rw[h']
  simp

-- This should be made functorial. Tm is given a category structure farther down
def TmSub {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(a : Tm A)(f : Δ ⥤ Γ) : Tm ((TySub f).obj A) where
  obj g := a.obj (f.obj g)
  map p := a.map (f.map p)
  map_id g := by
    have h' := (eqToHom_comp_iff ?_ (𝟙 (a.obj (f.obj g))) (a.map (𝟙 (f.obj g)))).mpr (a.map_id (f.obj g))
    case refine_1; simp[CategoryStruct.id]
    rw [<- h']
    simp
    have eq : f.map (𝟙 g) = 𝟙 (f.obj g) := f.map_id g
    rw [Tm_hom_congr a eq]
  map_comp p p':= by
    dsimp[TySub]
    have h := (a.map_comp (f.map p) (f.map p'))
    have eq : (f.map p ≫ f.map p') = f.map (p ≫ p') := (f.map_comp p p').symm
    have h' := Tm_hom_congr a eq
    rw[h'] at h
    have h'' := (eqToHom_comp_iff _ _ (a.map (f.map (p ≫ p')))).mp h
    rw[h'']
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

def TmSubToGrothendieckFunc {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(f : Δ ⟶ Γ)(M : Tm ((TySub f).obj A)) : Δ ⥤ (GroupoidGrothendieck A) where
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
    simp[CategoryStruct.comp,Grothendieck.comp]
    apply Grothendieck.ext <;> simp
    rw [M.map_comp]
    simp[TySub,Grpd.forgetToCat]

def TmSubToGrothendieckFuncWraper {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(S : Σ( f: Δ ⟶ Γ),Tm ((TySub f).obj A)) : Δ ⥤ (GroupoidGrothendieck A) := TmSubToGrothendieckFunc S.fst S.snd

def GrothendieckFuncToTmSub {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(F : Δ ⥤ (GroupoidGrothendieck A)) : Σ(f : Δ ⥤  Γ),Tm ((TySub f).obj A)where
  fst := (F ⋙ (Grothendieck.forget (A ⋙ Grpd.forgetToCat)))
  snd := by
    dsimp [TySub,Grothendieck.forget]
    constructor
    case obj; intro g; exact (F.obj g).fiber
    case map; intro _ _ p; dsimp; exact (F.map p).fiber
    case map_id; intro g; rw[Grothendieck.Hom_congr_fiber (A ⋙ Grpd.forgetToCat) (F.map_id g)];simp[CategoryStruct.id]
    case map_comp; intro g h i p p'; simp ; rw[Grothendieck.Hom_congr_fiber (A ⋙ Grpd.forgetToCat) (F.map_comp p p')];simp[CategoryStruct.comp,Grpd.forgetToCat]

theorem Left_Inv {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(S : Σ( f: Δ ⟶ Γ),Tm ((TySub f).obj A)):  (GrothendieckFuncToTmSub (TmSubToGrothendieckFuncWraper S)) = S := by
  congr

theorem  Right_Inv {Δ Γ: Grpd.{u,u}}{A : Ty Γ}(F : Δ ⥤ (GroupoidGrothendieck A)):  (TmSubToGrothendieckFuncWraper (GrothendieckFuncToTmSub F))= F := by
  congr

structure GrothendieckSection (Γ : Grpd.{u,u}) (A : Ty Γ) where
  func : Γ ⥤ (GroupoidGrothendieck A)
  s : func ⋙ (GroupoidGrothendieck.forget A) = 𝟙 Γ

def TmToGrothendieckFunc {Γ : Grpd.{u,u}}{A : Ty Γ}(M : Tm A) : Γ ⥤ (GroupoidGrothendieck A) where
  obj g := {base := g, fiber := M.obj g}
  map p := {base := p, fiber := M.map p}
  map_id g := by
    simp
    rw [(M.map_id g)]
    simp[CategoryStruct.id,Grothendieck.id]
  map_comp p p' := by
    simp
    rw [M.map_comp p p']
    simp[CategoryStruct.comp,Grothendieck.comp, Grpd.forgetToCat]

/-
This is a bijection but it is quite dificult to show in lean. I have worked on it for a bit by the inverse
function requiers so strange type casing that I cant seem to get to work
-/
def TmToGrothendieckSection {Γ : Grpd.{u,u}}{A : Ty Γ}(M : Tm A) : GrothendieckSection Γ A where
  func := TmToGrothendieckFunc M
  s := rfl

-- This can be expanded to a Groupoid
instance TmCategory {Γ : Grpd.{u,u}}{A : Ty Γ} : Category (Tm A) where
  Hom x y := (TmToGrothendieckFunc x) ⟶ (TmToGrothendieckFunc y)
  id x := 𝟙 (TmToGrothendieckFunc x)
  comp f g := NatTrans.vcomp f g

end HSexp


section NM
-- Here I am useing sGrpd to be a small category version of Grpd. There is likely a better way to do this.
def sGrpd := Grpd.{u,u}
def toGrpd (x : sGrpd.{u}) : Grpd.{u,u} := x
def tosGrpd (x : Grpd.{u,u}) : sGrpd.{u} := x

instance SmallGrpd : SmallCategory sGrpd.{u} where
  Hom x y := ULift.{u+1, u} (toGrpd x ⟶ toGrpd y)
  id x := {down := 𝟙 (toGrpd x)}
  comp f g := {down := f.down ≫ g.down}

def SmallGrpd.forget : sGrpd.{u} ⥤ Grpd.{u,u} where
  obj x := toGrpd x
  map f := f.down

def SmallGrpd.forget_op : sGrpd.{u}ᵒᵖ ⥤ Grpd.{u,u}ᵒᵖ where
  obj x := by
    rcases x with ⟨x⟩
    constructor
    exact (toGrpd x)
  map f := by
    constructor
    rcases f with ⟨f⟩
    exact f.down

/-
This is the Natral Modle on sGrpd. I am not sure this belongs in this file but I keep it here so that I can
get an idea of what needs to be done.
-/
instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
  Ty := SmallGrpd.forget_op ⋙ Ty_functor
  Tm := SmallGrpd.forget_op ⋙ Tm_functor
  tp := NatTrans.hcomp (NatTrans.id SmallGrpd.forget_op) (tp_NatTrans)
  ext Γ f := tosGrpd (Grpd.of (@GroupoidGrothendieck Γ ((@yonedaEquiv _ _ Γ (SmallGrpd.forget_op ⋙ Ty_functor)).toFun f)))
  disp Γ A := by
    constructor
    exact Grothendieck.forget (yonedaEquiv A ⋙ Grpd.forgetToCat)
  var Γ A := by
    sorry
  disp_pullback A := by
    dsimp
    sorry

end NM
