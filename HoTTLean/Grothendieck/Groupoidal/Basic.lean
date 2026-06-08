import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.Grpd
import HoTTLean.ForMathlib.CategoryTheory.Bicategory.Grothendieck

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

## Implementation notes
* To avoid `Grpd.forgetToCat` cluttering the user's context,
  although we use `Grothendieck` to define `Grothendieck.Groupoidal`,
  all definitions and lemmas are restated.
  This _probably_ also means that Lean has an easier time when type checking,
  as long as the user does not unfold down
  to `Grothendieck` definitions.
-/

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
def Groupoidal {C : Type u₁} [Category.{v₁,u₁} C] (F : C ⥤ Grpd.{v₂,u₂}) :=
  Grothendieck (F ⋙ Grpd.forgetToCat)

namespace Groupoidal

attribute [local simp] Grpd.id_eq_id Grpd.comp_eq_comp Functor.assoc

-- FIXME: maybe move the dsimprocs up into an earlier module so that more files can use them.
/-- A `dsimp` rule that reduces `𝟭 _ ⋙ F` to `F`
even if the domain categories are not syntactically equal. -/
dsimproc Functor.simpIdComp (@Functor.comp _ _ _ _ _ _ (@Functor.id _ _) _) := fun e => do
  let_expr Functor.comp _ _ _ _ _ _ _ F ← e | return .continue
  return .done F

/-- A `dsimp` rule that reduces `F ⋙ 𝟭 _` to `F`
even if the codomain categories are not syntactically equal. -/
dsimproc Functor.simpCompId (@Functor.comp _ _ _ _ _ _ _ (@Functor.id _ _)) := fun e => do
  let_expr Functor.comp _ _ _ _ _ _ F _ ← e | return .continue
  return .done F

scoped prefix:75 "∫ " => Functor.Groupoidal

section

variable {C : Type u₁} [Category.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

/-- A morphism in the groupoidal Grothendieck category `F : C ⥤ Grpd`
is a morphism in the upstream Grothendieck category `F ⋙ Grpd.forgetToCat`.
-/
abbrev Hom (x y : ∫(F)) := CategoryTheory.Grothendieck.Hom x y

abbrev id (x : ∫(F)) : Hom x x := CategoryTheory.Grothendieck.id x

abbrev comp {x y z : ∫(F)} (f : Hom x y) (g : Hom y z) : Hom x z :=
  CategoryTheory.Grothendieck.comp f g

attribute [local simp] eqToHom_map

instance : Category (∫ F) :=
  inferInstanceAs (Category (CategoryTheory.Grothendieck (F ⋙ Grpd.forgetToCat)))

def base (p : ∫(F)) : C := Grothendieck.base p

def fiber (p : ∫(F)) : F.obj p.base := Grothendieck.fiber p

namespace Hom

variable {x y : ∫(F)} (f : Hom x y)

/-- The morphism between base objects. -/
def base : x.base ⟶ y.base := Grothendieck.Hom.base f

/-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
def fiber : (F.map f.base).obj x.fiber ⟶ y.fiber := Grothendieck.Hom.fiber f

end Hom

def forget : ∫(F) ⥤ C := Grothendieck.forget _

@[simp] theorem forget_obj (x : ∫(F)) : forget.obj x = x.base :=
  rfl

@[simp] theorem forget_map {x y : ∫(F)} (f : x ⟶ y) : forget.map f = f.base :=
  rfl

/--
  We should use this to introduce objects,
  rather than the API for `Grothendieck`.
  This might seem redundant, but it simplifies the goal when
  making a point so that it does not show the composition with `Grpd.forgetToCat`
-/
def objMk (c : C) (x : F.obj c) : ∫(F) where
  base := c
  fiber := x

@[simp] theorem objMk_base (c : C) (x : F.obj c) : (objMk c x).base = c :=
  rfl

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

@[simp]
theorem id_base (X : ∫(F)) :
    Hom.base (𝟙 X) = 𝟙 X.base := rfl

@[simp]
theorem id_fiber (X : ∫(F)) :
    Hom.fiber (𝟙 X) = eqToHom (by
      rw [id_base]
      exact Functor.congr_obj (F.map_id X.base) X.fiber) :=
  rfl

@[simp]
theorem comp_base {X Y Z : ∫(F)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : ∫(F)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      eqToHom (by
        rw [comp_base]
        exact Functor.congr_obj (F.map_comp f.base g.base) X.fiber) ≫
        (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl

@[simp]
lemma base_eqToHom {X Y : ∫ F} (h : X = Y) :
    (eqToHom h).base = eqToHom (by simp [h]) := by
  subst h; rfl

@[simp]
lemma fiber_eqToHom {X Y : ∫ F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by
      subst h
      change (F.map (Hom.base (𝟙 X))).obj X.fiber = X.fiber
      rw [id_base]
      exact Functor.congr_obj (F.map_id X.base) X.fiber) := by
  subst h
  rfl

variable {F' : C ⥤ Grpd}

theorem Hom.hext' (h : F = F') {X Y : ∫ F} {X' Y' : ∫ F'} (hX : HEq X X') (hY : HEq Y Y')
    (f : Hom X Y) (g : Hom X' Y') (w_base : HEq f.base g.base) (w_fiber : HEq f.fiber g.fiber) :
    HEq f g := by
  cases f; cases g
  congr

end

@[simp] lemma Grothendieck.Groupoidal.eta {Γ : Type*} [Category Γ]
  {A : Γ ⥤ Grpd} (x : ∫(A)) : objMk x.base x.fiber = x :=
  rfl

@[simp] lemma Grothendieck.Groupoidal.Hom.eta {Γ : Type*} [Category Γ]
  {A : Γ ⥤ Grpd} {x y : ∫(A)} (f : x ⟶ y) : homMk f.base f.fiber = f :=
  rfl

section

variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance (X : C) : Groupoid ((F ⋙ Grpd.forgetToCat).obj X) :=
  inferInstanceAs (Groupoid (F.obj X : Type u₂))

/--
If `F : C ⥤ Grpd` is a functor and `t : c ⟶ d` is a morphism in `C`,
then `transport` maps each `c`-based element of `∫(F)` to a `d`-based element.
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

lemma transport_congr (x x' : ∫ F) (e1 : x = x') {c : C} (t : x.base ⟶ c) (t' : x'.base ⟶ c)
    (e : t = eqToHom (by simp[e1]) ≫ t') :
  transport x t = transport x' t' := by aesop_cat

lemma transport_id {x : ∫ F} : transport x (𝟙 x.base) = x := by
  apply Grothendieck.transport_id

lemma transport_eqToHom {X: C} {X' : F.Groupoidal} (hX': X'.base = X) :
    X'.transport (eqToHom hX') = X' := by
  subst hX'
  exact transport_id

lemma toTransport_id {X : ∫ F} :
    toTransport X (𝟙 X.base) = eqToHom transport_id.symm := by
  apply Grothendieck.toTransport_id

lemma toTransport_eqToHom {X: C} {X' : ∫ F} (hX': forget.obj X' = X):
    toTransport X' (eqToHom hX') = eqToHom (by subst hX'; simp [transport_id]) := by
  subst hX'
  exact toTransport_id

lemma transport_comp (x : ∫ F) {c d : C} (t : x.base ⟶ c) (t' : c ⟶ d):
    transport x (t ≫ t') = transport (transport x t) t' := by
  exact (Grothendieck.transport_comp x t t').symm

lemma toTransport_comp (x : ∫ F) {c d: C} (t : x.base ⟶ c) (t' : c ⟶ d):
    toTransport x (t ≫ t') =
    toTransport x t ≫ toTransport (transport x t) t' ≫ eqToHom (transport_comp x t t').symm := by
  exact Grothendieck.toTransport_comp x t t'

def isoMk {X Y : ∫(F)} (f : X ⟶ Y) : X ≅ Y := by
  fapply Grothendieck.isoMk
  · exact (Groupoid.isoEquivHom _ _).2 f.base
  · apply (Groupoid.isoEquivHom _ _).2 f.fiber

def inv {X Y : ∫(F)} (f : X ⟶ Y) : Y ⟶ X  :=
  isoMk f |>.inv

instance groupoid : Groupoid (∫ F) where
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

/-
JH: `ι_obj` in my opinion is a bad lemma. However,

1. The analogous thing for Grothendieck.ι exists, and is even a simp lemma.
2. Some proofs are shorter when feeding it to simp.

So for now let's avoid using it, but maybe we can put it back if
proves to be useful
-/
-- theorem ι_obj (c : C) (d : F.obj c) :
--     (ι F c).obj d = { base := c, fiber := d } :=
--   Grothendieck.ι_obj _ _ _

@[simp] theorem ι_obj_base (c : C) (d : F.obj c) : ((ι F c).obj d).base = c :=
  rfl

@[simp] theorem ι_obj_fiber (c : C) (d : F.obj c) : ((ι F c).obj d).fiber = d :=
  rfl

/-
Similar to `ι_obj`
NOTE the `Grothendieck` version in `mathlib` should NOT be a simp lemma
NOTE when `f = eqToHom` this is not the rewrite I want.
Instead I want to do `eqToHom_map`
theorem ι_map (c : C) {X Y : F.obj c} (f : X ⟶ Y) :
    (ι F c).map f = ⟨𝟙 _, eqToHom (by simp [ι_obj, Grpd.forgetToCat]) ≫ f⟩ :=
  Grothendieck.ι_map _ _ _
-/
@[simp] theorem ι_map_base (c : C) {X Y : F.obj c} (f : X ⟶ Y) :
    ((ι F c).map f).base = 𝟙 _ :=
  rfl

-- NOTE maybe this should be an HEq?
@[simp] theorem ι_map_fiber (c : C) {X Y : F.obj c} (f : X ⟶ Y) :
    ((ι F c).map f).fiber = eqToHom (by
      rw [ι_map_base]
      exact Functor.congr_obj (F.map_id c) X) ≫ f :=
  rfl

theorem ι_comp_forget (c : C) : ι F c ⋙ forget = (const (F.obj c)).obj c :=
  rfl

variable {F}

section ext

theorem ext {x y : ∫ F} (hbase : x.base = y.base)
    (hfiber : (F.map (eqToHom hbase)).obj x.fiber = y.fiber) : x = y := by
  apply Functor.Grothendieck.ext hbase hfiber

theorem hext {x y : ∫ F} (hbase : x.base = y.base) (hfiber : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨xbase, xfiber⟩
  subst hbase
  subst hfiber
  rfl

theorem hext_iff {x y : ∫ F} : x.base = y.base ∧ HEq x.fiber y.fiber
    ↔ x = y := by
  constructor
  · intro ⟨ hα , hstr ⟩
    exact hext hα hstr
  · intro hCD
    subst hCD
    exact ⟨ rfl , HEq.rfl ⟩

theorem Hom.hext {X Y : ∫ F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : HEq f.fiber g.fiber) : f = g := by
  cases f; cases g
  congr

theorem Hom.hext_iff (x y : ∫ F) (f g : x ⟶ y) :
    f.base = g.base ∧ HEq f.fiber g.fiber ↔ f = g := by
  constructor
  · intro h
    exact Hom.hext _ _ h.1 h.2
  · aesop

theorem Hom.ext {X Y : ∫ F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber = eqToHom (by rw [w_base]) ≫ g.fiber) : f = g := by
  apply Hom.hext <;> aesop

theorem Hom.ext_iff (x y : ∫ F) (f g : x ⟶ y) :
    (∃ w_base : f.base = g.base, f.fiber = eqToHom (by rw [w_base]) ≫ g.fiber) ↔ f = g := by
  constructor
  · intro h
    exact Hom.ext _ _ h.1 h.2
  · aesop

variable {F' : C ⥤ Grpd}

theorem hext' (h : F = F') {x : ∫ F} {y : ∫ F'}
    (hbase : HEq x.base y.base) (hfiber : HEq x.fiber y.fiber) : HEq x y := by
  rcases x; rcases y
  subst hbase
  congr

variable {D : Type*} [Category D]

theorem FunctorTo.hext (G H : D ⥤ ∫ F)
    (hbase : G ⋙ forget = H ⋙ forget)
    (hfiber_obj : ∀ x : D, HEq (G.obj x).fiber (H.obj x).fiber)
    (hfiber_map : ∀ {x y : D} (f : x ⟶ y), HEq (G.map f).fiber (H.map f).fiber)
    : G = H :=
  Grothendieck.FunctorTo.hext hbase hfiber_obj hfiber_map

end ext

section
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
variable {F : C ⥤ Grpd.{v₂, u₂}} (A : D ⥤ C) (fibObj : Π (x : D), (A ⋙ F).obj x)
    (fibMap : Π {x y : D} (f : x ⟶ y),
      ((A ⋙ F).map f).obj (fibObj x) ⟶ fibObj y)

theorem functorTo_map_id_aux (x : D) : ((A ⋙ F).map (𝟙 x)).obj (fibObj x) = fibObj x := by
  simp

theorem functorTo_map_comp_aux {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    ((A ⋙ F).map (f ≫ g)).obj (fibObj x)
    = (F.map (A.map g)).obj (((A ⋙ F).map f).obj (fibObj x)) := by
  simp

variable
    (map_id : Π (x : D), fibMap (CategoryStruct.id x)
      = eqToHom (functorTo_map_id_aux A fibObj x))
    (map_comp : Π {x y z : D} (f : x ⟶ y) (g : y ⟶ z), fibMap (f ≫ g)
      = eqToHom (functorTo_map_comp_aux A fibObj f g)
      ≫ (F.map (A.map g)).map (fibMap f) ≫ fibMap g)

/-- To define a functor into `Grothendieck F` we can make use of an existing
  functor into the base. -/
def functorTo : D ⥤ ∫(F) := Grothendieck.functorTo A fibObj fibMap map_id map_comp

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
    functorTo _ _ _ map_id map_comp ⋙ Grothendieck.forget _ = A :=
  rfl

end

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
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) :=
  Grothendieck.ιNatTrans_comp_app

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
  hom f ≫ (F.map f).whiskerLeft (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

/-- Construct a functor from `Groupoidal F` to another category `E` by providing a family of
functors on the fibers of `Groupoidal F`, a family of natural transformations on morphisms in the
base of `Groupoidal F` and coherence data for this family of natural transformations. -/
def functorFrom : ∫(F) ⥤ E :=
  Grothendieck.functorFrom fib hom hom_id hom_comp

@[simp] theorem functorFrom_obj (X : ∫(F)) :
    (functorFrom fib hom hom_id hom_comp).obj X = (fib X.base).obj X.fiber :=
  CategoryTheory.Grothendieck.functorFrom_obj (F := F ⋙ Grpd.forgetToCat)
    fib hom hom_id hom_comp X

@[simp] theorem functorFrom_map {X Y : ∫(F)} (f : X ⟶ Y) :
    (functorFrom fib hom hom_id hom_comp).map f
    = (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber :=
  CategoryTheory.Grothendieck.functorFrom_map (F := F ⋙ Grpd.forgetToCat)
    fib hom hom_id hom_comp f

/-- `Groupoidal.ι F c` composed with `Groupoidal.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Groupoidal.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  CategoryTheory.Grothendieck.ιCompFunctorFrom (F := F ⋙ Grpd.forgetToCat)
    fib hom hom_id hom_comp c

def ι_comp_functorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) = fib c :=
  Functor.ext_of_iso (ιCompFunctorFrom fib hom hom_id hom_comp c) (by intro; rfl)

lemma whiskerRight_ιNatTrans_functorFrom {x y} (f : x ⟶ y) :
    Functor.whiskerRight (ιNatTrans f) (functorFrom fib hom hom_id hom_comp) =
    eqToHom (ι_comp_functorFrom ..) ≫ hom f ≫
    eqToHom (by rw [Functor.assoc, ι_comp_functorFrom]) :=
  Grothendieck.whiskerRight_ιNatTrans_functorFrom (F := F ⋙ Grpd.forgetToCat)
    fib hom hom_id hom_comp f

section

variable {D : Type*} [Category D]
variable (G : E ⥤ D)

def functorFromCompFib (c : C) : F.obj c ⥤ D := fib c ⋙ G

def functorFromCompHom {c c' : C} (f : c ⟶ c') :
    functorFromCompFib fib G c ⟶ F.map f ⋙ functorFromCompFib fib G c' :=
  Functor.whiskerRight (hom f) G

include hom_id in
lemma functorFromCompHom_id (c : C) : functorFromCompHom fib hom G (𝟙 c)
    = eqToHom (by simp) := by
  ext x
  simp [functorFromCompHom, hom_id]

include hom_comp in
lemma functorFromCompHom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃):
    functorFromCompHom fib hom G (f ≫ g)
    = functorFromCompHom fib hom G f ≫
    Functor.whiskerLeft (F.map f) (functorFromCompHom fib hom G g) ≫
    eqToHom (by simp) := by
  ext x
  simp [functorFromCompHom, hom_comp]

lemma functorFromCompHom_eq {c c' : C}  (f : c ⟶ c') :
    functorFromCompHom fib hom G f = whiskerRight (hom f) G :=
  rfl

theorem functorFrom_comp :
    functorFrom fib hom hom_id hom_comp ⋙ G =
    functorFrom (functorFromCompFib fib G) (functorFromCompHom fib hom G)
    (functorFromCompHom_id fib hom hom_id G)
    (functorFromCompHom_comp fib hom hom_comp G) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    simp [functorFromCompFib]
  · intro x y f
    simp [functorFromCompHom, functorFromCompFib]

variable (K : ∫(F) ⥤ E)

abbrev asFunctorFromFib (c : C) : F.obj c ⥤ E := ι F c ⋙ K

abbrev asFunctorFromHom {c c' : C} (f: c ⟶ c') :
    asFunctorFromFib K c ⟶ F.map f ⋙ asFunctorFromFib K c' :=
  Functor.whiskerRight (ιNatTrans f) K

-- TODO: remove?
lemma asFunctorFromFib_functorFrom :
    asFunctorFromFib (functorFrom fib hom hom_id hom_comp) = fib := by
  unfold asFunctorFromFib
  ext
  rw [ι_comp_functorFrom]

lemma asFunctorFromHom' {c c' : C} (f: c ⟶ c') :
  asFunctorFromHom K f = whiskerRight (ιNatTrans f) K := rfl

lemma asFunctorFromHom_app {c c' : C} (f: c ⟶ c') (p : F.obj c) :
    (asFunctorFromHom K f).app p = K.map ((ιNatTrans f).app p) :=
  rfl

lemma asFunctorFromHom_id (c : C) : asFunctorFromHom K (𝟙 c) =
    eqToHom (by simp) :=
  Grothendieck.asFunctorFromHom_id K c

lemma asFunctorFromHom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g: c₂ ⟶ c₃) :
    asFunctorFromHom K (f ≫ g) =
    asFunctorFromHom K f ≫ Functor.whiskerLeft (F.map f) (asFunctorFromHom K g) ≫ eqToHom
    (by simp) :=
  Grothendieck.asFunctorFromHom_comp K c₁ c₂ c₃ f g

/-- Groupoidal version of `Grothendieck.asFunctorFrom` -/
theorem asFunctorFrom : functorFrom (asFunctorFromFib K) (asFunctorFromHom K)
    (asFunctorFromHom_id K) (asFunctorFromHom_comp K) = K :=
  Grothendieck.asFunctorFrom K

theorem functorFrom_ext {K K' : ∫(F) ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), Functor.whiskerRight (ιNatTrans f) K ≫
      eqToHom (by simp [Functor.assoc, hfib])
      = eqToHom (by rw[hfib]) ≫ Functor.whiskerRight (ιNatTrans f) K')
    : K = K' :=
  Grothendieck.functorFrom_ext hfib hhom

theorem functorFrom_hext {K K' : ∫(F) ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), Functor.whiskerRight (ιNatTrans f) K ≍
      Functor.whiskerRight (ιNatTrans f) K')
    : K = K' :=
  Grothendieck.functorFrom_hext hfib hhom

section
variable (A : E ⥤ C) (fibObj : (x : E) → (A ⋙ F).obj x)
    (fibMap : {x y : E} → (f : x ⟶ y) → ((A ⋙ F).map f).obj (fibObj x) ⟶ fibObj y)
    (map_id : (x : E) → fibMap (CategoryStruct.id x)
      = eqToHom (functorTo_map_id_aux A fibObj x))
    (map_comp : {x y z : E} → (f : x ⟶ y) → (g : y ⟶ z) → fibMap (f ≫ g)
      = eqToHom (functorTo_map_comp_aux A fibObj f g)
      ≫ (F.map (A.map g)).map (fibMap f) ≫ fibMap g)

@[simps!]
def functorIsoFrom (fib_comp : ∀ c, fib c ⋙ A = ι F c ⋙ forget)
    (fibObj_fib_obj : ∀ c x, fibObj ((fib c).obj x) ≍ x)
    (fibMap_fib_map : ∀ c {x y} (f : x ⟶ y), fibMap ((fib c).map f) ≍ f)
    (fib_obj_fibObj : ∀ x, (fib (A.obj x)).obj (fibObj x) = x)
    (hom_map_app_fibObj : ∀ {x y} (f : x ⟶ y), (hom (A.map f)).app (fibObj x) ≫
      (fib (A.obj y)).map (fibMap f) ≍ f)
    (obj_fib_obj : ∀ c x, A.obj ((fib c).obj x) = c)
    (map_hom_app : ∀ {c c'} (f : c ⟶ c') x, A.map ((hom f).app x) ≍ f)
    (fibMap_hom_app : ∀ {c c'} (f : c ⟶ c') x, fibMap ((hom f).app x) ≍ 𝟙 ((F.map f).obj x)) :
    ∫ F ≅≅ E where
  hom := functorFrom fib hom hom_id hom_comp
  inv := functorTo A fibObj fibMap map_id map_comp
  hom_inv_id := by
    fapply functorFrom_ext
    · intro c
      rw [← Functor.assoc, ι_comp_functorFrom]
      apply FunctorTo.hext
      · calc
          fib c ⋙ functorTo A fibObj fibMap map_id map_comp ⋙ forget = fib c ⋙ A := rfl
          _ = ι F c ⋙ forget := fib_comp c
          _ = (ι F c ⋙ 𝟭 (∫ F)) ⋙ forget := by simp
      · apply fibObj_fib_obj
      · intro x y f
        exact HEq.trans (fibMap_fib_map c f) (HEq.symm (eqToHom_comp_heq f _))
    · intro c c' f
      apply NatTrans.ext
      ext x
      simp only [comp_obj, functorFrom_obj, ι_obj_base, ι_obj_fiber, id_obj, comp_whiskerRight,
        whiskerRight_ιNatTrans_functorFrom, whiskerRight_comp, eqToHom_whiskerRight, Category.assoc,
        eqToHom_trans, NatTrans.comp_app, eqToHom_app, eqToHom_refl, whiskerRight_app,
        Category.id_comp, id_whiskerRight, ← heq_eq_eq, heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
      apply Hom.hext' rfl
      · apply hext' rfl
        · exact heq_of_eq (obj_fib_obj c x)
        · exact fibObj_fib_obj c x
      · apply hext' rfl
        · exact heq_of_eq (obj_fib_obj c' ((F.map f).obj x))
        · exact fibObj_fib_obj c' ((F.map f).obj x)
      · exact map_hom_app f x
      · exact fibMap_hom_app f x
  inv_hom_id := by
    fapply Functor.ext
    · intro x
      simp [fib_obj_fibObj]
    · intro x y f
      simp [← heq_eq_eq, hom_map_app_fibObj]

end
end
end FunctorFrom

section
variable {C : Type u} [Category.{v} C] {F G : C ⥤ Grpd.{v₂,u₂}}

/-- The groupoidal Grothendieck construction is functorial:
a natural transformation `α : F ⟶ G` induces
a functor `Groupoidal.map : Groupoidal F ⥤ Groupoidal G`.
-/
def map (α : F ⟶ G) : Groupoidal F ⥤ Groupoidal G :=
  Grothendieck.map (whiskerRight α _)

variable {α : F ⟶ G}

theorem map_obj_objMk (xb : C) (xf : F.obj xb) :
    (Groupoidal.map α).obj (objMk xb xf) = objMk xb ((α.app xb).obj xf) :=
  rfl

theorem map_id_eq : map (𝟙 F) = Functor.id (Cat.of <| Groupoidal <| F) :=
  Grothendieck.map_id_eq

theorem map_forget (α : F ⟶ G) : map α ⋙ forget = forget :=
  rfl

@[simp] theorem map_obj_base (X) : ((map α).obj X).base = X.base :=
  Grothendieck.map_obj_base _ _

@[simp] theorem map_obj_fiber (X) :
    ((map α).obj X).fiber = (α.app X.base).obj X.fiber :=
  Grothendieck.map_obj_fiber _ _

variable {X} {Y : ∫(F)} (f : X ⟶ Y)

@[simp] theorem map_map_base : ((Groupoidal.map α).map f).base = f.base
    := Grothendieck.map_map_base _ _

@[simp] theorem map_map_fiber :
  ((Groupoidal.map α).map f).fiber =
    eqToHom (Functor.congr_obj (α.naturality f.base).symm X.fiber)
    ≫ (α.app Y.base).map f.fiber := by
  change ((CategoryTheory.Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map f).fiber =
    eqToHom (Functor.congr_obj (α.naturality f.base).symm X.fiber) ≫ (α.app Y.base).map f.fiber
  rw [CategoryTheory.Grothendieck.map_map_fiber]
  rfl

/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
def ιCompMap {F' : C ⥤ Grpd} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ α.app c ⋙ ι F' c :=
  Grothendieck.ιCompMap ..

lemma ι_comp_map {F' : C ⥤ Grpd} (α : F ⟶ F') (c : C) : ι F c ⋙ map α = α.app c ⋙ ι F' c :=
  Grothendieck.ι_comp_map ..

end

section

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ Grpd.{v₂,u₂}) (G : D ⥤ C)

/-- Applying a functor `G : D ⥤ C` to the base of the groupoidal Grothendieck
  construction induces a functor `∫(G ⋙ F) ⥤ ∫(F)`. -/
def pre : ∫(G ⋙ F) ⥤ ∫(F) :=
  Grothendieck.pre (F ⋙ Grpd.forgetToCat) G

@[simp]
lemma pre_obj_base (x) : ((pre F G).obj x).base = G.obj x.base := by
  aesop

@[simp]
lemma pre_obj_fiber (x) : ((pre F G).obj x).fiber = x.fiber := by
  aesop_cat

@[simp]
lemma pre_map_base {x y} (f : x ⟶ y) : ((pre F G).map f).base = G.map f.base := by
  aesop_cat

@[simp]
lemma pre_map_fiber {x y} (f : x ⟶ y) : ((pre F G).map f).fiber = f.fiber := by
  aesop_cat

@[simp]
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

section

variable {G H : D ⥤ C} (α : G ≅ H)

/--
An natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`∫(G ⋙ F) ⥤ ∫(H ⋙ F)`.
-/
def preNatIso :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  Grothendieck.preNatIso _ _

@[simp] theorem preNatIso_hom_app_base (x) :
    ((preNatIso F α).hom.app x).base = α.hom.app x.base :=
  Grothendieck.preNatIso_hom_app_base ..

@[simp] theorem preNatIso_hom_app_fiber (x) :
    ((preNatIso F α).hom.app x).fiber = 𝟙 _ :=
  Grothendieck.preNatIso_hom_app_fiber ..

theorem preNatIso_congr {G H : D ⥤ C} {α β : G ≅ H} (h : α = β) :
    preNatIso F α = preNatIso F β ≪≫ eqToIso (by subst h; simp) := by
  subst h
  simp

end

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

theorem pre_comp_forget (α : D ⥤ C) (A : C ⥤ Grpd) :
    pre A α ⋙ forget = forget ⋙ α := rfl

@[simp] theorem ι_comp_pre {D : Type*} [Category D] (G : D ⥤ C) (x : D)
    : ι (G ⋙ F) x ⋙ pre F G = ι F (G.obj x) := by
  apply FunctorTo.hext
  · rw [ι_comp_forget, Functor.assoc, pre_comp_forget, ← Functor.assoc, ι_comp_forget]
    apply Functor.ext <;> simp
  · intro
    simp
  · simp

noncomputable section

variable {F} {x y : ∫ F} (f : x ⟶ y) [IsIso f]

instance : IsIso f.base := by
  refine ⟨ (CategoryTheory.inv f).base , ?_, ?_ ⟩
  · change Hom.base (f ≫ CategoryTheory.inv f) = Hom.base (𝟙 x)
    rw [IsIso.hom_inv_id]
  · change Hom.base (CategoryTheory.inv f ≫ f) = Hom.base (𝟙 y)
    rw [IsIso.inv_hom_id]

instance : IsIso f.fiber := by
  infer_instance

def invFiber : y.fiber ⟶ (F.map f.base).obj x.fiber :=
  CategoryTheory.inv f.fiber

@[simp]
lemma fiber_comp_invFiber : f.fiber ≫ invFiber f = 𝟙 ((F.map f.base).obj x.fiber) := by
  change f.fiber ≫ invFiber f = 𝟙 ((Grpd.forgetToCat.map (F.map f.base)).toFunctor.obj x.fiber)
  simp [invFiber]
  rfl

@[simp]
lemma invFiber_comp_fiber : invFiber f ≫ f.fiber = 𝟙 _ := by
  simp [invFiber]

lemma inv_base : CategoryTheory.inv f.base = (CategoryTheory.inv f).base := by
  apply IsIso.inv_eq_of_hom_inv_id
  change Hom.base (f ≫ CategoryTheory.inv f) = Hom.base (𝟙 x)
  rw [IsIso.hom_inv_id]

lemma inv_fiber : CategoryTheory.inv f.fiber = invFiber f := by
  rfl

end
end

section

variable {Γ : Type*} [Category Γ] {F G : Γ ⥤ Grpd}

lemma comp_forget_naturality {α : F ⟶ G} {X Y : Γ} (f : X ⟶ Y) :
    (F ⋙ Grpd.forgetToCat).map f ≫ Grpd.forgetToCat.map (α.app Y)=
  Grpd.forgetToCat.map (α.app X) ≫ (G ⋙ Grpd.forgetToCat).map f := by
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [← Grpd.forgetToCat.map_comp, ← Grpd.forgetToCat.map_comp]
  simp

lemma map_map_eqToHom {α : F ⟶ G} {X Y : ∫(F)} (f : X ⟶ Y) :
    ((G ⋙ Grpd.forgetToCat).map f.base).toFunctor.obj ((map α).obj X).fiber =
  (α.app Y.base).obj (((F ⋙ Grpd.forgetToCat).map f.base).toFunctor.obj X.fiber) := by
    apply Eq.symm
    have equ1 :
      (α.app Y.base).obj ((Grpd.forgetToCat.map (F.map f.base)).toFunctor.obj X.fiber) =
      ((Grpd.forgetToCat.map (F.map f.base)).toFunctor ⋙ (α.app Y.base)).obj X.fiber := by simp
    have equ2 :
      (Grpd.forgetToCat.map (G.map f.base)).toFunctor.obj ((α.app X.base).obj X.fiber) =
      ((α.app X.base) ⋙ (Grpd.forgetToCat.map (G.map f.base)).toFunctor).obj X.fiber := by simp
    simp only [Functor.comp_obj, Functor.comp_map, map_obj_fiber]
    rw[equ1, equ2]
    refine Functor.congr_obj ?_ X.fiber
    exact α.naturality f.base

@[simp] theorem eqToHom_comp_fiber {C : Type u} [Category.{v} C] {A : C ⥤ Grpd.{v₁, u₁}}
    {p q r : ∫(A)} (h : p = q) {f : q ⟶ r} :
    (eqToHom h ≫ f).fiber = eqToHom (by subst h; simp) ≫ f.fiber := by
  simp [eqToHom_map]

end

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

end

section
variable {Γ : Type u} [Groupoid.{v} Γ] (A : Γ ⥤ Grpd.{v₁,u₁})

theorem map_eqToHom_base {G1 G2 : ∫(A)} (eq : G1 = G2)
    : A.map (eqToHom eq).base = eqToHom (by subst eq; simp) := by
  cases eq
  change A.map (Hom.base (𝟙 G1)) = 𝟭 (A.obj G1.base)
  rw [id_base]
  simp

open CategoryTheory.Functor in
/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
noncomputable def ιNatIso {X Y : Γ} (f : X ⟶ Y) : ι A X ≅ A.map f ⋙ ι A Y :=
  NatIso.ofComponents (fun a => asIso ((ιNatTrans f).app a)) (by
    intro a b g
    exact (ιNatTrans f).naturality g)

theorem ιNatIso_hom {x y : Γ} (f : x ⟶ y) :
    (ιNatIso A f).hom = ιNatTrans f := by
  ext a
  simp [ιNatIso]

@[simp] theorem ιNatIso_id (x : Γ) :
    ιNatIso A (𝟙 x) = eqToIso (by simp) := by
  ext
  simp [ιNatIso]

theorem ιNatIso_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    ιNatIso A (f ≫ g) = ιNatIso A f ≪≫ Functor.isoWhiskerLeft (A.map f) (ιNatIso A g)
    ≪≫ eqToIso (by simp) := by
  ext
  simp [ιNatIso]

end

section

-- TODO factor through Grothendieck
lemma eqToHom_eq_homOf_map {Γ : Type*} [Groupoid Γ] {F G : Γ ⥤ Grpd} (h : F = G) :
    eqToHom (by rw [h] : Grpd.of (∫ F) = Grpd.of (∫ G)) =
      Grpd.homOf (C := Grpd.of (∫ F)) (D := Grpd.of (∫ G)) (map (eqToHom h)) := by
  subst h
  change 𝟭 (∫ F) = map (𝟙 F)
  rw [map_id_eq]
  rfl

-- TODO factor through Grothendieck
theorem map_eqToHom_heq_id_dom {Γ : Type*} [Category Γ] {A A' : Γ ⥤ Grpd}
    (h : A = A') : HEq (map (eqToHom h)) (𝟭 (∫A)) := by
  subst h
  simp [map_id_eq]

-- TODO factor through Grothendieck
theorem map_eqToHom_heq_id_cod {Γ : Type*} [Category Γ] {A A' : Γ ⥤ Grpd}
    (h : A = A') : HEq (map (eqToHom h)) (𝟭 (∫A')) := by
  subst h
  simp [map_id_eq]

-- TODO factor through Grothendieck
theorem map_eqToHom_comp_heq {Γ D : Type*} [Category Γ] [Category D] {A A' : Γ ⥤ Grpd}
    (h : A = A') (F : ∫(A') ⥤ D) : HEq (map (eqToHom h) ⋙ F) F := by
  apply Functor.precomp_heq_of_heq_id
  · rw [h]
  · rw [h]
  · apply map_eqToHom_heq_id_cod

-- TODO factor through Grothendieck
theorem comp_map_eqToHom_heq {Γ D : Type*} [Category Γ] [Category D] {A A' : Γ ⥤ Grpd}
    (h : A = A') (F : D ⥤ ∫(A)) : HEq (F ⋙ map (eqToHom h)) F := by
  apply Functor.comp_heq_of_heq_id
  · rw [h]
  · rw [h]
  · apply map_eqToHom_heq_id_dom

-- TODO factor through Grothendieck
lemma pre_congr_functor {Γ Δ : Type*} [Category Γ] [Category Δ] (σ : Δ ⥤ Γ)
    {F G : Γ ⥤ Grpd} (h : F = G) :
  map (eqToHom (by rw[← h])) ⋙ pre F σ ⋙ map (eqToHom h) =
  pre G σ := by
  subst h
  simp only [eqToHom_refl, map_id_eq]
  exact rfl

lemma fiber_eqToHom_comp_heq {Γ : Type*} [Category Γ]
    {F : Γ ⥤ Grpd} {x' x y : ∫ F} (h : x' = x) (f : x ⟶ y) :
    (eqToHom h ≫ f).fiber ≍ f.fiber := by
  subst h
  rw! (castMode := .all) [comp_fiber, fiber_eqToHom, eqToHom_map]
  simp only [eqToHom_comp_heq_iff]
  rfl

lemma fiber_eq_eqToHom_comp_heq {Γ : Type*} [Category Γ]
    {F : Γ ⥤ Grpd} {x' x y : ∫ F} (g : x' ⟶ x) (h : x' = x) (hg : g = eqToHom h)
    (f : x ⟶ y) : (eqToHom h ≫ f).fiber ≍ f.fiber := by
  subst h
  rw! (castMode := .all) [comp_fiber, fiber_eqToHom, eqToHom_map]
  simp only [eqToHom_comp_heq_iff]
  rfl

lemma fiber_comp_eqToHom_heq {Γ : Type*} [Category Γ]
    {F : Γ ⥤ Grpd} {x y y' : ∫ F} (h : y = y') (f : x ⟶ y) :
    (f ≫ eqToHom h).fiber ≍ f.fiber := by
  subst h
  simp only [eqToHom_refl]
  rw [Category.comp_id]


end

end Groupoidal
end Functor
end CategoryTheory
