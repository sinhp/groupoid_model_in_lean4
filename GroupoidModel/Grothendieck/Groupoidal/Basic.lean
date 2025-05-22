import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.ForMathlib

/-!
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

def base (p : ∫(F)) : C := Grothendieck.base p

def fiber (p : ∫(F)) := Grothendieck.fiber p

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
  fapply Grothendieck.isoMk
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

-- NOTE when `f = eqToHom` this is not the rewrite I want.
-- Instead I want to do `eqToHom_map`
theorem ι_map (c : C) {X Y : ↑(F.obj c)} (f : X ⟶ Y) :
    (ι F c).map f = ⟨𝟙 _, eqToHom (by simp [ι_obj, Grpd.forgetToCat]) ≫ f⟩ :=
  Grothendieck.ι_map _ _ _

variable {F}

@[ext (iff := false)]
theorem ext {X Y : ∫(F)} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g w_base w_fiber

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

@[simp] theorem map_obj {α : F ⟶ G} (X : Groupoidal F) :
    (Groupoidal.map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl


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

theorem pre_forget (α : D ⥤ C) (A : C ⥤ Grpd) :
    pre A α ⋙ forget = forget ⋙ α := by
  rfl

end

section

variable {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{v₁, u₁})
  {F : Γ ⥤ Grpd.{v₁,u₁}}

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
    Hom.fiber (𝟙 X) = eqToHom (by rw! [Functor.map_id]; simp) :=
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

variable {G : Γ ⥤ Grpd}

-- theorem eta (p : ∫(F)) : ⟨p.base, p.fiber⟩ = p := rfl

theorem obj_hext {p1 p2 : ∫(F)} (hbase : p1.base = p2.base)
    (hfib : HEq p1.fiber p2.fiber) : p1 = p2 :=
  Grothendieck.obj_hext hbase hfib


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

@[simp] theorem fiber_eqToHom (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by unfold Groupoidal; subst h; simp [Grpd.forgetToCat]) :=
  Grothendieck.fiber_eqToHom _

@[simp] theorem eqToHom_comp_fiber {C : Type u} [Category.{v} C] {A : C ⥤ Grpd.{v₁, u₁}}
    {p q r : ∫(A)} (h : p = q) {f : q ⟶ r} :
    (eqToHom h ≫ f).fiber = eqToHom (by subst h; simp) ≫ f.fiber := by
  simp [eqToHom_map]

end

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

@[simp] theorem ι_pre {Γ : Type u₂} [Category.{v₂} Γ] {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)(A : Γ ⥤ Grpd.{v₁,u₁}) (x : Δ)
    : ι (σ ⋙ A) x ⋙ Groupoidal.pre A σ = ι A (σ.obj x) :=
  Grothendieck.ι_pre _ (A ⋙ Grpd.forgetToCat) _

theorem congr {C : Type u} [Category.{v, u} C] {F : C ⥤ Grpd}
    {X Y : Groupoidal F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

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

section
variable {Γ : Type u} [Groupoid.{v} Γ] (A : Γ ⥤ Grpd.{v₁,u₁})

-- NOTE something broke between versions of mathlib?
-- seems like issue is some definitional equalities can no longer be
-- closed by simp
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
     simp only [Grpd.forgetToCat, Functor.comp_obj, Cat.of_α, id_base, Functor.comp_map, id_eq, whiskerLeft_app,
  Grpd.comp_eq_comp, Grpd.id_eq_id, eq_mpr_eq_cast, comp_base, ιNatTrans_app_base, comp_fiber, ιNatTrans_app_fiber,
  Grpd.map_comp_map, eqToHom_fiber, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, id_fiber,
  eqToHom_comp_iff, eqToHom_trans]
     generalize_proofs p1
     erw [Functor.map_id (A.map (Groupoid.inv f)),
       Functor.map_id (A.map (eqToHom p1).base),
       Category.id_comp, Category.id_comp]
   · simp only [NatTrans.comp_app, Functor.comp_obj, whiskerLeft_app, eqToHom_app, comp_base, ιNatTrans_app_base,
  Groupoid.inv_eq_inv, eqToHom_base, eqToHom_refl, Category.comp_id, IsIso.hom_inv_id, NatTrans.id_app, id_base]
     rfl
  inv_hom_id := by
    ext a
    apply Grothendieck.Groupoidal.ext
    · simp only [NatTrans.id_app, NatTrans.comp_app]
      rw! [eqToHom_app]
      simp only [Grpd.forgetToCat, Functor.comp_obj, Cat.of_α, id_base, Functor.comp_map, id_eq, whiskerLeft_app,
  Grpd.comp_eq_comp, Grpd.id_eq_id, eq_mpr_eq_cast, comp_base, ιNatTrans_app_base, comp_fiber, ιNatTrans_app_fiber,
  eqToHom_fiber, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, id_fiber]
      generalize_proofs p1
      erw [Category.comp_id, Functor.map_id (A.map (eqToHom p1).base),
        Functor.map_id (A.map f)]
      simp
    · simp
      rfl

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

end Groupoidal
end Grothendieck
