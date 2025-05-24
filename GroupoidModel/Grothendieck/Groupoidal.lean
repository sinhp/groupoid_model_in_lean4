import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.Pointed.IsPullback

import SEq.Tactic.DepRewrite

/-!
# The Groupidal Grothendieck construction

  ↑Grothendieck (toCat A) -- toPGrpd --> PGrpd
        |                                 |
        |                                 |
↑ Grothendieck.forget        PGrpd.forgetToGrpd
        |                                 |
        v                                 v
        ↑Γ--------------A---------------> Grpd

## Main definitions
* `CategoryTheory.Grothendieck.Groupoidal`
  takes a functor from a groupoid into `Grpd` the category of groupoids,
  composes it with the forgetful functor into `Cat` the category of categories,
  then applies `CategoryTheory.Grothendieck`.
  This is a groupoid.

## Main statements

* `CategoryTheory.Grothendieck.Groupoidal.groupoid`
  is an instance of a groupoid structure on the groupidal
  Grothendieck construction.
* `CategoryTheory.Grothendieck.Groupoidal.isPullback`
  shows that `Grothendieck.forget A` is classified by `PGrpd.forgetToGrpd`
  as the pullback of `A`.
  This uses the proof of the similar fact
  `CategoryTheory.Grothendieck.isPullback`,
  as well as the proof `CategoryTheory.isPullback_forgetToGrpd_forgetToCat`
  that `PGrpd` is the pullback of `PCat`.

- TODO Probably the proof of `Groupoidal.IsPullback` can be shortened
  significantly by providing a direct proof of pullback
  using the `IsMegaPullback` defintions
- NOTE Design: `Groupoidal.ι`, `Groupoidal.pre` and so on should *not* be
  reduced by `simp`. Instead we should add `simp` lemmas by hand.
  This avoids `Grpd.forgetToCat` cluttering the user's context
-/

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace Grothendieck

/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
def Groupoidal {C : Type u₁} [Category.{v₁,u₁} C] (F : C ⥤ Grpd.{v₂,u₂}) :=
  Grothendieck (F ⋙ Grpd.forgetToCat)

notation:max "∫(" A ")" => Grothendieck.Groupoidal A

namespace Groupoidal

section

variable {C : Type u₁} [Category.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance : Category (Groupoidal F) :=
  inferInstanceAs (Category (Grothendieck _))

def forget : ∫(F) ⥤ C := Grothendieck.forget _

/--
  We should use this to introduce objects,
  rather than the API for `Grothendieck`.
  This might seem redundant, but it simplifies the goal when
  making a point so that it does not show the composition with `Grpd.forgetToCat`
-/
def objMk (c : C) (x : F.obj c) : ∫(F) where
  base := c
  fiber := x

-- FIXME should this be done by adding @[simps] to objMk?
@[simp] theorem objMk_base (c : C) (x : F.obj c) : (objMk c x).base = c :=
  rfl

-- FIXME should this be done by adding @[simps] to objMk?
@[simp] theorem objMk_fiber (c : C) (x : F.obj c) : (objMk c x).fiber = x :=
  rfl

/--
  We should use this to introduce morphisms,
  rather than the API for `Grothendieck`.
  This might seem redundant, but it simplifies the goal when
  making a path in the fiber so that it does not show the
  composition with `Grpd.forgetToCat`
-/
def homMk {X Y : ∫(F)} (fb : X.base ⟶ Y.base) (ff : (F.map fb).obj X.fiber ⟶ Y.fiber)
    : X ⟶ Y where
  base := fb
  fiber := ff

-- FIXME should this be done by adding @[simps] to homMk?
@[simp] theorem homMk_base {X Y : ∫(F)} (fb : X.base ⟶ Y.base)
    (ff : (F.map fb).obj X.fiber ⟶ Y.fiber) : (homMk fb ff).base = fb :=
  rfl

-- FIXME should this be done by adding @[simps] to homMk?
@[simp] theorem homMk_fiber {X Y : ∫(F)} (fb : X.base ⟶ Y.base)
    (ff : (F.map fb).obj X.fiber ⟶ Y.fiber) : (homMk fb ff).fiber = ff :=
  rfl

end

section


variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance
    (X : C) : Groupoid (F ⋙ Grpd.forgetToCat |>.obj X) where
  inv f := ((F.obj X).str').inv f

/--
If `F : C ⥤ Grpd` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `∫(F)` to a `d`-based element.
-/
def transport (x : ∫(F)) {c : C} (t : x.base ⟶ c) : ∫(F) :=
  Grothendieck.transport x t

@[simp] theorem transport_base (x : ∫(F)) {c : C} (t : x.base ⟶ c) :
    (x.transport t).base = c :=
  Grothendieck.transport_base x t

@[simp] theorem transport_fiber (x : ∫(F)) {c : C} (t : x.base ⟶ c) :
    (x.transport t).fiber = (F.map t).obj x.fiber :=
  Grothendieck.transport_fiber x t

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
def toTransport (x : ∫(F)) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  Grothendieck.toTransport x t

@[simp] theorem toTransport_base (x : ∫(F)) {c : C} (t : x.base ⟶ c) :
    (x.toTransport t).base = t :=
  Grothendieck.toTransport_base _ _

@[simp] theorem toTransport_fiber (x : ∫(F)) {c : C} (t : x.base ⟶ c) :
    (x.toTransport t).fiber = 𝟙 ((F.map t).obj x.fiber) :=
  Grothendieck.toTransport_fiber _ _


def isoMk {X Y : ∫(F)} (f : X ⟶ Y) : X ≅ Y := by
  fapply Grothendieck.mkIso
  · exact (Groupoid.isoEquivHom _ _).2 f.base
  · apply (Groupoid.isoEquivHom _ _).2 f.fiber

def inv {X Y : ∫(F)} (f : X ⟶ Y) : Y ⟶ X  :=
  isoMk f |>.inv

instance groupoid : Groupoid ∫(F) where
  inv f :=  inv f
  inv_comp f := (isoMk f).inv_hom_id
  comp_inv f := (isoMk f).hom_inv_id

end

section FunctorFrom

variable {C : Type u} [Category.{v} C]
    (F : C ⥤ Grpd.{v₁,u₁})

/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its
groupoidal Grothendieck construction.-/
def ι (c : C) : F.obj c ⥤ Groupoidal F :=
  Grothendieck.ι (F ⋙ Grpd.forgetToCat) c

theorem ι_obj (c : C) (d : ↑(F.obj c)) :
    (ι F c).obj d = { base := c, fiber := d } :=
  Grothendieck.ι_obj _ _ _

@[simp] theorem ι_obj_base (c : C) (d : ↑(F.obj c)) :
    ((ι F c).obj d).base = c := by
  simp [ι_obj]

@[simp] theorem ι_obj_fiber (c : C) (d : ↑(F.obj c)) :
    ((ι F c).obj d).fiber = d := by
  simp [ι_obj]

-- NOTE when `f = eqToHom` this is not the rewrite I want.
-- Instead I want to do `eqToHom_map`
theorem ι_map (c : C) {X Y : ↑(F.obj c)} (f : X ⟶ Y) :
    (ι F c).map f = ⟨𝟙 _, eqToHom (by simp [ι_obj, Grpd.forgetToCat]) ≫ f⟩ :=
  Grothendieck.ι_map _ _ _

theorem ι_map_base (c : C) {X Y : ↑(F.obj c)} (f : X ⟶ Y) :
    ((ι F c).map f).base = 𝟙 _ := by
  simp[ι_map]

theorem ι_map_fiber (c : C) {X Y : ↑(F.obj c)} (f : X ⟶ Y) :
    ((ι F c).map f).fiber = eqToHom (by simp [ι_obj, Grpd.forgetToCat, ι_map]) ≫ f := by
  simp[ι_map]

variable {F}

@[ext (iff := false)]
theorem ext {X Y : ∫(F)} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g w_base w_fiber

theorem ext_homMk {X Y : ∫(F)} (fb gb : X.base ⟶ Y.base)
  (ff: (F.map fb).obj X.fiber ⟶ Y.fiber)
  (gf: (F.map gb).obj X.fiber ⟶ Y.fiber)
  (w_base : fb = gb)
    (w_fiber : eqToHom (by rw [w_base]) ≫ ff = gf) :
    homMk fb ff = homMk gb gf := by
  apply ext (homMk fb ff) (homMk gb gf) w_base w_fiber

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y :=
  Grothendieck.ιNatTrans _

@[simp] theorem ιNatTrans_id_app {X : C} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (𝟙 X)).app a =
    eqToHom (by simp) := Grothendieck.ιNatTrans_id_app

@[simp] theorem ιNatTrans_comp_app {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) := Grothendieck.ιNatTrans_comp_app

@[simp] theorem ιNatTrans_app_base {X Y : C} (f : X ⟶ Y) (d : ↑(F.obj X)) :
    ((ιNatTrans f).app d).base = f :=
  Grothendieck.ιNatTrans_app_base _ _

@[simp] theorem ιNatTrans_app_fiber {X Y : C} (f : X ⟶ Y) (d : F.obj X) :
    ((ιNatTrans f).app d).fiber
    = 𝟙 ((F.map f).obj ((Groupoidal.ι F X).obj d).fiber) :=
  Grothendieck.ιNatTrans_app_fiber _ _

variable {E : Type*} [Category E]
variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

/-- Construct a functor from `Groupoidal F` to another category `E` by providing a family of
functors on the fibers of `Groupoidal F`, a family of natural transformations on morphisms in the
base of `Groupoidal F` and coherence data for this family of natural transformations. -/
def functorFrom : ∫(F) ⥤ E :=
  Grothendieck.functorFrom fib hom hom_id hom_comp

@[simp] theorem functorFrom_obj (X : ∫(F)) : (functorFrom fib hom hom_id hom_comp).obj X = (fib X.base).obj X.fiber := by apply Grothendieck.functorFrom_obj

@[simp] theorem functorFrom_map {X Y : ∫(F)} (f : X ⟶ Y) :
  (functorFrom fib hom hom_id hom_comp).map f
  = (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber := by apply Grothendieck.functorFrom_map

/-- `Groupoidal.ι F c` composed with `Groupoidal.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Groupoidal.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  Grothendieck.ιCompFunctorFrom _ _ _ _ _

end FunctorFrom

section
variable {C : Type u} [Category.{v} C]
    {F G : C ⥤ Grpd.{v₂,u₂}}
/-- The groupoidal Grothendieck construction is functorial:
a natural transformation `α : F ⟶ G` induces
a functor `Groupoidal.map : Groupoidal F ⥤ Groupoidal G`.
-/
def map (α : F ⟶ G) : Groupoidal F ⥤ Groupoidal G :=
  Grothendieck.map (whiskerRight α _)

theorem map_obj_objMk {α : F ⟶ G} (xb : C) (xf : F.obj xb) :
    (Groupoidal.map α).obj (objMk xb xf) = objMk xb ((α.app xb).obj xf) :=
  rfl

-- lemma h' {α : F ⟶ G} {X Y : C} (f : X ⟶ Y) :
--   (F ⋙ Grpd.forgetToCat).map f ≫ (whiskerRight α Grpd.forgetToCat).app Y =
--   (whiskerRight α Grpd.forgetToCat).app X ≫ (G ⋙ Grpd.forgetToCat).map f := by
--     simp
--     rw [← Grpd.forgetToCat.map_comp]; rw [← Grpd.forgetToCat.map_comp]
--     simp

--lemma h2 {α : F ⟶ G} {X : C} : (whiskerRight α Grpd.forgetToCat).app X = Grpd.forgetToCat.map (α.app X) := rfl



-- TODO move to ForMathlib
theorem Grothendieck.map_eqToHom_obj_base {F G : C ⥤ Cat.{v,u}} (h : F = G)
  (x) : ((Grothendieck.map (eqToHom h)).obj x).base = x.base := rfl

theorem map_id_eq : map (𝟙 F) = Functor.id (Cat.of <| Groupoidal <| F) :=
  Grothendieck.map_id_eq

end

section

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ Grpd.{v₂,u₂})

/-- Applying a functor `G : D ⥤ C` to the base of the groupoidal Grothendieck
  construction induces a functor `∫(G ⋙ F) ⥤ ∫(F)`. -/
def pre (G : D ⥤ C) : ∫(G ⋙ F) ⥤ ∫(F) :=
  Grothendieck.pre (F ⋙ Grpd.forgetToCat) G

@[simp]
theorem pre_id : pre F (Functor.id C) = Functor.id _ := rfl

/--
An natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`∫(G ⋙ F) ⥤ ∫(H ⋙ F)`.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  Grothendieck.preNatIso _ _

/--
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of the `pre _ G.functor`.
-/
def preInv (G : D ≌ C) : ∫(F) ⥤ ∫(G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ pre (G.functor ⋙ F) G.inverse

variable {F} in
lemma pre_comp_map (G: D ⥤ C) {H : C ⥤ Grpd} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

variable {F} in
lemma pre_comp_map_assoc (G: D ⥤ C) {H : C ⥤ Grpd} (α : F ⟶ H) {E : Type*} [Category E]
    (K : ∫(H) ⥤ E) : pre F G ⋙ map α ⋙ K= map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

variable {E : Type*} [Category E] in
@[simp]
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

end

section

variable {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{v₁, u₁})
instance toPCatObjGroupoid (x : ∫(A)) : Groupoid x.toPCatObj := by
  dsimp [Grpd.forgetToCat]
  infer_instance

instance toPCatObjPointed (x : ∫(A)) : PointedGroupoid x.toPCatObj :=
  PointedGroupoid.of x.toPCatObj PointedCategory.pt

def toPGrpd : ∫(A) ⥤ PGrpd.{v₁,u₁} where
  obj x := PGrpd.of x.toPCatObj
  map := Grothendieck.toPCatMap
  map_id := (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)).map_id
  map_comp := (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)).map_comp

theorem toPGrpd_comp_forgetToPCat :
    toPGrpd A ⋙ PGrpd.forgetToPCat = toPCat (A ⋙ Grpd.forgetToCat) :=
  rfl

section

variable {F : Γ ⥤ Grpd.{v₁,u₁}}

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
@[simp] theorem eqToHom_base {x y : ∫(F)} (eq : x = y) :
    (eqToHom eq).base = eqToHom (by simp [eq]) :=
  Grothendieck.eqToHom_base _

/-- This is the proof of equality used in the eqToHom in `Groupoidal.eqToHom_fiber` -/
theorem eqToHom_fiber_aux {g1 g2 : ∫(F)}
    (eq : g1 = g2) : (F.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
  unfold Groupoidal
  cases eq
  simp

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
@[simp] theorem eqToHom_fiber {g1 g2 : ∫(F)} (eq : g1 = g2) :
    (eqToHom eq).fiber = eqToHom (eqToHom_fiber_aux eq) := by
  unfold Groupoidal
  cases eq
  simp

@[simp] theorem base_eqToHom {X Y : ∫(F)} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg base h) :=
  Grothendieck.base_eqToHom _

@[simp]
theorem id_base (X : ∫(F)) :
    Hom.base (𝟙 X) = 𝟙 X.base := by
  rfl

@[simp]
theorem id_fiber (X : ∫(F)) :
    Hom.fiber (𝟙 X) = eqToHom (by simp [Grpd.forgetToCat]) :=
  rfl

@[simp]
theorem comp_base {X Y Z : ∫(F)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : ∫(F)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
      eqToHom (by simp [Grpd.forgetToCat]) ≫ (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl


@[simp] theorem _root_.CategoryTheory.Grpd.eqToHom_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F G : C ⥤ D) (h : F = G) (X : C) :
    (eqToHom h).app X = eqToHom (by subst h; rfl) := by
  subst h
  simp

section
variable {C : Type u} [Category.{v, u} C] {D : Type u₁}
  [Category.{v₁, u₁} D] (F : C ⥤ Grpd) (G : D ⥤ C)
  (X : Groupoidal (G ⋙ F))

@[simp] theorem pre_obj_base : ((pre F G).obj X).base = G.obj X.base :=
  Grothendieck.pre_obj_base _ _ _

@[simp] theorem pre_obj_fiber : ((pre F G).obj X).fiber = X.fiber :=
  Grothendieck.pre_obj_fiber _ _ _

variable {X Y : Groupoidal (G ⋙ F)} (f : X ⟶ Y)

@[simp] theorem pre_map_base : ((pre F G).map f).base = G.map f.base :=
  Grothendieck.pre_map_base _ _ _

@[simp] theorem pre_map_fiber : ((pre F G).map f).fiber = f.fiber :=
  Grothendieck.pre_map_fiber _ _ _

end
section

variable {G : Γ ⥤ Grpd}

-- theorem eta (p : ∫(F)) : ⟨p.base, p.fiber⟩ = p := rfl

theorem obj_ext_hEq {p1 p2 : ∫(F)} (hbase : p1.base = p2.base)
    (hfib : HEq p1.fiber p2.fiber) : p1 = p2 :=
  Grothendieck.obj_ext_hEq hbase hfib


variable (α : F ⟶ G) (X : ∫(F))

@[simp] theorem map_obj_base : ((map α).obj X).base = X.base :=
  Grothendieck.map_obj_base _ _

@[simp] theorem map_obj_fiber :
    ((map α).obj X).fiber = (α.app X.base).obj X.fiber :=
  Grothendieck.map_obj_fiber _ _

variable {X} {Y : ∫(F)} (f : X ⟶ Y)

@[simp] theorem map_map_base : ((Groupoidal.map α).map f).base = f.base
    := Grothendieck.map_map_base _ _

@[simp] theorem map_map_fiber :
  ((Groupoidal.map α).map f).fiber =
    eqToHom (Functor.congr_obj (map.proof_1 (whiskerRight α _) f) X.fiber)
    ≫ (α.app Y.base).map f.fiber := Grothendieck.map_map_fiber _ _

lemma comp_forget_naturality  {α : F ⟶ G} {X Y : Γ} (f : X ⟶ Y) : (F ⋙ Grpd.forgetToCat).map f ≫ Grpd.forgetToCat.map (α.app Y)=
  Grpd.forgetToCat.map (α.app X) ≫ (G ⋙ Grpd.forgetToCat).map f := by
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [← Grpd.forgetToCat.map_comp]; rw [← Grpd.forgetToCat.map_comp]
  simp

lemma map_map_eqToHom {α : F ⟶ G} {X Y : ∫(F)} (f : X ⟶ Y) :
    ((G ⋙ Grpd.forgetToCat).map f.base).obj ((map α).obj X).fiber =
  (α.app Y.base).obj (((F ⋙ Grpd.forgetToCat).map f.base).obj X.fiber) := by
    apply Eq.symm
    have equ1 :
      (α.app Y.base).obj ((Grpd.forgetToCat.map (F.map f.base)).obj X.fiber) =
      ((Grpd.forgetToCat.map (F.map f.base)) ⋙ (α.app Y.base)).obj X.fiber := by simp
    have equ2 :
      (Grpd.forgetToCat.map (G.map f.base)).obj ((α.app X.base).obj X.fiber) =
      ((α.app X.base) ⋙ (Grpd.forgetToCat.map (G.map f.base))).obj X.fiber := by simp
    simp only [Functor.comp_obj, Functor.comp_map, map_obj_fiber]
    rw[equ1, equ2]
    refine Functor.congr_obj ?_ X.fiber
    apply comp_forget_naturality

theorem map_map {α : F ⟶ G} {X Y : ∫(F)} (f : X ⟶ Y) :
    (map α).map f =
    ⟨f.base, eqToHom (map_map_eqToHom f) ≫ (α.app Y.base).map f.fiber⟩ := by
    simp[map, Grothendieck.map_map]; exact rfl

@[simp] theorem fiber_eqToHom (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by unfold Groupoidal; subst h; simp [Grpd.forgetToCat]) :=
  Grothendieck.fiber_eqToHom _

@[simp] theorem eqToHom_comp_fiber {C : Type u} [Category.{v} C] {A : C ⥤ Grpd.{v₁, u₁}}
    {p q r : ∫(A)} (h : p = q) {f : q ⟶ r} :
    (eqToHom h ≫ f).fiber = eqToHom (by subst h; simp) ≫ f.fiber := by
  simp [eqToHom_map]

end
end


namespace IsMegaPullback

theorem comm_sq : Groupoidal.toPGrpd A ⋙ PGrpd.forgetToGrpd = Groupoidal.forget ⋙ A := rfl

variable {A} {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PGrpd.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ A)

theorem toPGrpd_eq_lift :
    toPGrpd A =
    PGrpd.IsMegaPullback.lift
      (toPCat (A ⋙ Grpd.forgetToCat))
      (Groupoidal.forget ⋙ A) rfl :=
  PGrpd.IsMegaPullback.lift_uniq
    (toPCat (A ⋙ Grpd.forgetToCat))
    (Groupoidal.forget ⋙ A)
    rfl _ rfl rfl

def lift : C ⥤ Groupoidal A :=
  Grothendieck.IsMegaPullback.lift
    (fst ⋙ PGrpd.forgetToPCat) snd (by
      simp only [← Functor.assoc, ← w]
      rfl)

theorem fac_left' : (lift fst snd w ⋙ toPGrpd A) ⋙ PGrpd.forgetToPCat
    = fst ⋙ PGrpd.forgetToPCat := by
  rw [toPGrpd_eq_lift, Functor.assoc,
    PGrpd.IsMegaPullback.fac_left,
    ← PGrpd.IsMegaPullback.fac_left
      (fst ⋙ PGrpd.forgetToPCat) (snd ⋙ A) (by rw [← w]; rfl)]
  rfl

@[simp] theorem fac_left : lift fst snd w ⋙ Groupoidal.toPGrpd _ = fst :=
   calc lift fst snd w ⋙ Groupoidal.toPGrpd _
    _ = PGrpd.IsMegaPullback.lift
      (fst ⋙ PGrpd.forgetToPCat)
      (snd ⋙ A)
      (by rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq, ← w]; rfl) :=
    PGrpd.IsMegaPullback.lift_uniq
      (fst ⋙ PGrpd.forgetToPCat)
      (snd ⋙ A) _ _
      (fac_left' _ _ _)
      (by rw [Functor.assoc, comm_sq]; rfl)
    _ = fst :=
    symm $ PGrpd.IsMegaPullback.lift_uniq _ _ _ _ rfl w

@[simp] theorem fac_right :
    lift fst snd w ⋙ Groupoidal.forget
    = snd :=
  Grothendieck.IsMegaPullback.fac_right
    (fst ⋙ PGrpd.forgetToPCat) snd (by
    rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq,
      ← Functor.assoc, w, Functor.assoc])

theorem lift_uniq (m : C ⥤ Groupoidal A)
    (hl : m ⋙ toPGrpd _ = fst)
    (hr : m ⋙ Groupoidal.forget = snd) :
    m = lift _ _ w := by
  apply Grothendieck.IsMegaPullback.lift_uniq
  · rw [← toPGrpd_comp_forgetToPCat, ← hl, Functor.assoc]
  · exact hr

theorem hom_ext {m n : C ⥤ Groupoidal A}
    (hl : m ⋙ toPGrpd _ = n ⋙ toPGrpd _)
    (hr : m ⋙ Groupoidal.forget = n ⋙ Groupoidal.forget) :
    m = n := by
  rw [lift_uniq (m ⋙ toPGrpd _) (m ⋙ forget) rfl m rfl rfl,
    lift_uniq (n ⋙ toPGrpd _) (n ⋙ forget) rfl n rfl rfl]
  rw! [hl, hr]

end IsMegaPullback

namespace IsPullback

open Grothendieck.IsPullback ULift

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

abbrev uLiftGrpd : Cat.{u, max u (u+1)} :=
  Cat.ofULift.{max u (u+1)} Grpd.{u}

abbrev uLiftA : Cat.ofULift.{u+1} Γ ⟶ uLiftGrpd.{u} :=
  downFunctor ⋙ A ⋙ upFunctor

abbrev uLiftPGrpd : Cat.{u, max u (u+1)} :=
  Cat.ofULift.{max u (u+1)} PGrpd.{u,u}

abbrev uLiftPGrpdForgetToGrpd : uLiftPGrpd.{u} ⟶ uLiftGrpd.{u} :=
  downFunctor ⋙ PGrpd.forgetToGrpd ⋙ upFunctor

/--
The universal lift
`var' : ∫(A) ⟶ Grothendieck(Grpd.forgetToCat)`
given by pullback pasting in the following pasting diagram.

      ∫(A)  .-.-.-.-.-.-.-> ↑GrothendieckForgetToCat -----> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
noncomputable def var' :
    IsPullback.uLiftGrothendieck (A ⋙ Grpd.forgetToCat)
    ⟶ IsPullback.uLiftGrothendieck Grpd.forgetToCat.{u,u} :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat))
    ((IsPullback.uLiftGrothendieckForget
      (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
      (Grothendieck.isPullback
        (A ⋙ Grpd.forgetToCat)).cone.condition_one

theorem var'_uLiftToPCat :
    var' A ≫ (uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = uLiftToPCat (A ⋙ Grpd.forgetToCat) :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_fst
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat))
    ((IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat)).cone.condition_one

theorem var'_forget :
    var' A ≫ (uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    = uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat) ≫ uLiftA A :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_snd
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat)) ((IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat)).cone.condition_one


/--
The following square is a pullback
  ↑Grothendieck (Groupoid.compForgetToCat A) ------- var' -------> ↑Grothendieck Grpd.forgetToCat
        |                                                    |
        |                                                    |
↑ Grothendieck.forget                           ↑Grothendieck.forget
        |                                                    |
        v                                                    v
        ↑Γ--------------↑A----------------------------> ↑Grpd.{u,u}

by pullback pasting

  ↑Grothendieck (Groupoid.compForgetToCat A) --> ↑Grothendieck Grpd.forgetToCat ---> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
theorem
  isPullback_uLiftGrothendieckForget_Groupoid.compForgetToCat_uLiftGrothendieckForget_grpdForgetToCat :
    IsPullback
    (Cat.homOf (var' A))
    (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
    (IsPullback.uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    (uLiftA A) :=
  IsPullback.of_right'
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat))
    (Grothendieck.isPullback (Grpd.forgetToCat.{u,u}))

theorem isPullback_aux:
    IsPullback
      (Cat.homOf (var' A)
        ≫ (Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
      (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (uLiftA A ≫ Cat.ULift_iso_self.hom) :=
  IsPullback.paste_horiz
    (isPullback_uLiftGrothendieckForget_Groupoid.compForgetToCat_uLiftGrothendieckForget_grpdForgetToCat.{u} A)
    (PGrpd.IsPullback.isPullback_uLiftGrothendieckForget_forgetToGrpd.{u})

open ULift

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

theorem toPGrpd_comp_forgetToPCat_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToPCat :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToPCat
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv ⋙ PGrpd.forgetToPCat := by
  have h : var' A ⋙ (IsPullback.uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat) := var'_uLiftToPCat A
  dsimp only [IsPullback.uLiftToPCat] at h
  simp only [Cat.ofULift, Cat.of_α, ← Functor.assoc,
    ← toPGrpd_comp_forgetToPCat, comp_upFunctor_inj] at h
  simp only [Functor.assoc] at h
  rw [← h]
  rfl

theorem toPGrpd_comp_forgetToGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToGrpd :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToGrpd
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv ⋙ PGrpd.forgetToGrpd := by
  have h : (downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv.{u,u})
      ⋙ PGrpd.forgetToGrpd.{u,u} =
      IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u,u} ⋙ downFunctor :=
    PGrpd.IsPullback.isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq.horiz_inv.{u,u}.w
  simp only [← toPGrpd_comp_forgetToPCat, Functor.assoc] at h
  have h1 : var' A ⋙ IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u}
      = IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat) ⋙ uLiftA A :=
    var'_forget A
  simp only [Cat.of_α, IsPullback.uLiftGrothendieckForget, ← Functor.assoc,
    uLiftA] at h1
  rw [comp_upFunctor_inj] at h1
  simp only [h, ← Functor.assoc, h1]
  rfl

theorem toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv' :
    Cat.homOf (downFunctor ⋙ toPGrpd A)
      = Cat.homOf (var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv)
      :=
  PGrpd.isPullback_forgetToGrpd_forgetToCat.{u}.hom_ext
    (toPGrpd_comp_forgetToPCat_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToPCat _)
    (toPGrpd_comp_forgetToGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToGrpd _)

theorem toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv :
    downFunctor ⋙ toPGrpd A
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv :=
  toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv' _

end IsPullback

open Grothendieck
open IsPullback

/-
The following square is a pullback

       ∫(A)               -- toPGrpd -->                    PGrpd
        |                                                     |
        |                                                     |
↑ Grothendieck.forget                                PGrpd.forgetToGrpd
        |                                                     |
        |                                                     |
        v                                                     v
        ↑Γ-----------------------A-----------------------> Grpd
in the appropriately sized category `Grpd.{v, max u (v+1)}`;
where `(Γ : Type u) [Grpdegory.{v} Γ] (A : Γ ⥤ Grpd.{v,v})`.
-/
theorem isPullback {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u}) :
    IsPullback
      (Cat.homOf (ULift.downFunctor ⋙ toPGrpd A))
      (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf (ULift.downFunctor.{u,u} ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {Δ : Type u₃} [Category.{v₃} Δ]
    (σ : Δ ⥤ Γ)

@[simp] theorem ιCompPre (A : Γ ⥤ Grpd.{v₁,u₁}) (x : Δ)
    : ι (σ ⋙ A) x ⋙ Groupoidal.pre A σ = ι A (σ.obj x) :=
  Grothendieck.ιCompPre _ (A ⋙ Grpd.forgetToCat) _

end

section

variable {Γ : Type u} [Category.{v} Γ]
variable (A : Γ ⥤ Grpd.{v₁,u₁}) (α : Γ ⥤ PGrpd.{v₁,u₁}) (h : α ⋙ PGrpd.forgetToGrpd = A)

/-- `sec` is the universal lift in the following diagram,
  which is a section of `Groupoidal.forget`
             α
  ===== Γ -------α--------------¬
 ‖      ↓ sec                   V
 ‖   M.ext A ⋯ -------------> PGrpd
 ‖      |                        |
 ‖      |                        |
 ‖   forget                  forgetToGrpd
 ‖      |                        |
 ‖      V                        V
  ===== Γ --α ≫ forgetToGrpd--> Grpd
-/
def sec : Γ ⥤ ∫(A) :=
  IsMegaPullback.lift α (𝟭 _) (by simp [h, Functor.id_comp])

@[simp] def sec_toPGrpd : sec A α h ⋙ toPGrpd _ = α := by
  simp [sec]

@[simp] def sec_forget : sec A α h ⋙ forget = 𝟭 _ :=
  rfl

section naturality
variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

@[simp]
theorem pre_toPGrpd (A : Γ ⥤ Grpd) : pre A σ ⋙ toPGrpd _ = toPGrpd _ := by
  rfl

theorem pre_forget (A : Γ ⥤ Grpd) : pre A σ ⋙ forget = forget ⋙ σ := by
  rfl

theorem sec_naturality : σ ⋙ sec A α h = sec (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) ⋙ pre A σ := by
  apply Groupoidal.IsMegaPullback.hom_ext
  . simp [Functor.assoc, Functor.comp_id]
  . conv_rhs => rw [Functor.assoc, pre_forget, ← Functor.assoc, sec_forget]
    simp [Functor.assoc, Functor.comp_id, Functor.id_comp]

end naturality

@[simp] lemma sec_map_base {x y} {f : x ⟶ y} :
    ((sec A α h).map f).base = f := by
  simp [sec, IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift]

-- TODO likely will also need the non-trivially forded case, in which case rename this
-- to `sec_map_fiber_rfl`
@[simp] lemma sec_map_fiber {x y} {f : x ⟶ y} :
    ((sec (α ⋙ PGrpd.forgetToGrpd) α rfl).map f).fiber = (α.map f).point := by
  simp [sec, IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift,
    Grothendieck.IsMegaPullback.lift_map, Grothendieck.IsMegaPullback.point]

end

theorem congr {C : Type u} [Category.{v, u} C] {F : C ⥤ Grpd}
    {X Y : Groupoidal F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

section
variable {Γ : Type u} [Groupoid.{v} Γ] (A : Γ ⥤ Grpd.{v₁,u₁})

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
def ιNatIso {X Y : Γ} (f : X ⟶ Y) : ι A X ≅ A.map f ⋙ ι A Y where
  hom := (ιNatTrans f)
  inv := whiskerLeft (A.map f) (ιNatTrans (Groupoid.inv f)) ≫ eqToHom (by
    convert_to A.map (f ≫ Groupoid.inv f) ⋙ ι A X = ι A X
    · simp only [Functor.map_comp, Grpd.comp_eq_comp, Functor.assoc]
    · simp [Functor.id_comp])
  hom_inv_id := by
   ext a
   apply Grothendieck.Groupoidal.ext
   · simp only [NatTrans.id_app, NatTrans.comp_app]
     rw! [Grpd.eqToHom_app]
     simp [Grpd.forgetToCat]
   · simp
  inv_hom_id := by
    ext a
    apply Grothendieck.Groupoidal.ext
    · simp only [NatTrans.id_app, NatTrans.comp_app]
      rw! [eqToHom_app]
      simp [eqToHom_map, Grpd.forgetToCat]
    · simp

theorem ιNatIso_hom {x y : Γ} (f : x ⟶ y) :
    (ιNatIso A f).hom = ιNatTrans f := by
  simp [ιNatIso]

@[simp] theorem ιNatIso_id (x : Γ) :
    ιNatIso A (𝟙 x) = eqToIso (by simp [Functor.id_comp]) := by
  ext
  simp [ιNatIso]

theorem ιNatIso_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    ιNatIso A (f ≫ g) = ιNatIso A f ≪≫ isoWhiskerLeft (A.map f) (ιNatIso A g)
    ≪≫ eqToIso (by simp [Functor.assoc]) := by
  ext
  simp [ιNatIso]

end

section
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ Grpd.{v₂,u₂})

theorem map_comp_eq {G H : C ⥤ Grpd.{v₂,u₂}} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  simp [map, Grothendieck.map_comp_eq]

theorem preNatIso_congr {G H : D ⥤ C} {α β : G ≅ H} (h : α = β) :
    preNatIso F α = preNatIso F β ≪≫ eqToIso (by subst h; simp) :=
  Grothendieck.preNatIso_congr _ h

@[simp] theorem preNatIso_eqToIso {G H : D ⥤ C} {h : G = H} :
    preNatIso F (eqToIso h) = eqToIso (by
      subst h
      simp [Groupoidal.map_id_eq, Functor.id_comp]) :=
  Grothendieck.preNatIso_eqToIso _

theorem preNatIso_comp {G1 G2 G3 : D ⥤ C} (α : G1 ≅ G2) (β : G2 ≅ G3) :
    preNatIso F (α ≪≫ β) = preNatIso F α ≪≫ isoWhiskerLeft _ (preNatIso F β) ≪≫
    eqToIso (by simp [map_comp_eq, Functor.assoc]) :=
  Grothendieck.preNatIso_comp _ _ _

end

end Groupoidal
end Grothendieck
end CategoryTheory
