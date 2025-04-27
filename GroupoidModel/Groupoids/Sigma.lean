import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

namespace CategoryTheory

namespace Grpd


section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
theorem map_comp_map'
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map g).map ((A.map f).map φ)
    = eqToHom Grpd.map_comp_obj.symm ≫ (A.map (f ≫ g)).map φ ≫ eqToHom Grpd.map_comp_obj
    := by
  simp [Grpd.map_comp_map]
end

@[simp] theorem id_obj {C : Grpd} (X : C) :
    (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp] theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E)
    (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

variable {Γ : Type u} [Category.{v} Γ] (F : Γ ⥤ Grpd.{v₁,u₁})

@[simp] theorem map_eqToHom_obj {x y : Γ} (h : x = y) (t) :
    (F.map (eqToHom h)).obj t = cast (by rw [h]) t := by
  subst h
  simp

-- set_option pp.proofs true
@[simp] theorem map_eqToHom_map {x y : Γ} (h : x = y) {t s} (f : t ⟶ s) :
    (F.map (eqToHom h)).map f =
    eqToHom (Functor.congr_obj (eqToHom_map _ _) t)
    ≫ cast (Grpd.eqToHom_hom_aux t s (by rw [h])) f
    ≫ eqToHom (Eq.symm (Functor.congr_obj (eqToHom_map _ _) s)) := by
  have h1 : F.map (eqToHom h) = eqToHom (by rw [h]) := eqToHom_map _ _
  rw [Functor.congr_hom h1, Grpd.eqToHom_hom]

end Grpd

namespace Grothendieck

namespace Groupoidal

variable {C : Type u} [Category.{v, u} C] {F : C ⥤ Grpd} {X Y : C}

theorem congr {X Y : Groupoidal F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

@[simp] lemma sec_map_base {α : C ⥤ PGrpd.{v₁,u₁}} {x y} {f : x ⟶ y} :
    ((Grothendieck.Groupoidal.sec α).map f).base = f := by
  simp [Grothendieck.Groupoidal.sec, Grothendieck.Groupoidal.sec',
            IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift]

@[simp] lemma sec_map_fiber {α : C ⥤ PGrpd.{v₁,u₁}} {x y} {f : x ⟶ y} :
    ((Grothendieck.Groupoidal.sec α).map f).fiber = (α.map f).point := by
  simp [Grothendieck.Groupoidal.sec, Grothendieck.Groupoidal.sec',
            IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift,
            Grothendieck.IsMegaPullback.lift_map,
            Grothendieck.IsMegaPullback.point]

@[simp] theorem ιNatTrans_app_base
    (f : X ⟶ Y) (d : ↑(F.obj X)) : ((ιNatTrans f).app d).base = f :=
  Grothendieck.ιNatTrans_app_base _ _

@[simp] theorem ιNatTrans_app_fiber (f : X ⟶ Y) (d : F.obj X) :
    ((ιNatTrans f).app d).fiber
    = 𝟙 ((F.map f).obj ((Groupoidal.ι F X).obj d).fiber) :=
  Grothendieck.ιNatTrans_app_fiber _ _

end Groupoidal

end Grothendieck

end CategoryTheory

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

notation:max "@(" Γ ")" => Ctx.toGrpd.obj Γ

namespace FunctorOperation

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)
/--
For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd`
-/
@[simp, reducible] def sigmaObj := ∫(ι A x ⋙ B)

variable {x} {y : Γ} (f : x ⟶ y)
/--
For a morphism `f : x ⟶ y` in `Γ`, `(sigma A B).map y` is a
composition of functors.
The first functor `map (whiskerRight (ιNatTrans f) B)`
is an equivalence which replaces `ι A x` with the naturally
isomorphic `A.map f ⋙ ι A y`.
The second functor is the action of precomposing
`A.map f` with `ι A y ⋙ B` on the Grothendieck constructions.

            map ⋯                  pre ⋯
  ∫ ι A x ⋙ B ⥤ ∫ A.map f ⋙ ι A y ⋙ B ⥤ ∫ ι A y ⋙ B
-/
def sigmaMap : sigmaObj B x ⥤ sigmaObj B y :=
  map (whiskerRight (ιNatTrans f) B) ⋙ pre (ι A y ⋙ B) (A.map f)

variable {B}

@[simp] theorem sigmaMap_id_obj {p} : (sigmaMap B (𝟙 x)).obj p = p := by
  simp only [sigmaMap, Functor.comp_obj, map_obj, Functor.id_obj]
  apply obj_ext_hEq
  · rw [pre_obj_base, Grpd.map_id_obj]
  · simp

@[simp] theorem sigmaMap_id_map {p1 p2} (f : p1 ⟶ p2) :
    (sigmaMap B (𝟙 x)).map f =
    eqToHom (by simp) ≫ f ≫ eqToHom (by simp) := by
  let t := @ιNatTrans _ _ A _ _ (CategoryStruct.id x)
  have h (a : A.obj x) : B.map (t.app a) =
      eqToHom (by simp [Functor.map_id]) :=
    calc
      B.map (t.app a)
      _ = B.map (eqToHom (by simp [Functor.map_id])) := by
        rw [ιNatTrans_id_app]
      _ = eqToHom (by simp [Functor.map_id]) := by
        simp [eqToHom_map]
  dsimp only [sigmaMap]
  simp only [Functor.comp_map, Functor.id_map]
  apply Grothendieck.Groupoidal.ext
  · simp only [pre_map_fiber, map_map_fiber, whiskerRight_app, eqToHom_trans_assoc, comp_fiber, eqToHom_fiber, eqToHom_map]
    -- NOTE rw! much faster here for map_eqToHom_map and Functor.congr_hom
    rw! [Functor.congr_hom (h p2.base) f.fiber, eqToHom_base,
      Grpd.map_eqToHom_map, Grpd.eqToHom_hom]
    -- NOTE ι_obj, ι_map really unhelpful when there is an eqToHom
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  · simp

theorem sigmaMap_id : sigmaMap B (CategoryStruct.id x) = Functor.id _ := by
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp
    · intro p
      simp

variable {z : Γ} {f} {g : y ⟶ z}

@[simp] theorem sigmaMap_comp_obj {p} : (sigmaMap B (f ≫ g)).obj p =
    (sigmaMap B g).obj ((sigmaMap B f).obj p) := by
  dsimp only [sigmaMap]
  apply obj_ext_hEq
  · simp
  · simp

@[simp] theorem sigmaMap_comp_map {A : Γ ⥤ Grpd.{v₁,u₁}}
    {B : ∫(A) ⥤ Grpd.{v₁,u₁}} {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z}
    {p q} (hpq : p ⟶ q) {h1} {h2} :
    (sigmaMap B (f ≫ g)).map hpq =
    eqToHom h1 ≫ (sigmaMap B g).map ((sigmaMap B f).map hpq) ≫ eqToHom h2 := by
  -- let t := B.map ((ιNatTrans (f ≫ g)).app q.base)
  have h : B.map ((ιNatTrans (f ≫ g)).app q.base) =
    B.map ((ιNatTrans f).app q.base)
    ≫ B.map ((ιNatTrans g).app ((A.map f).obj q.base))
    ≫ eqToHom (by simp) := by simp [eqToHom_map]
  dsimp only [sigmaMap]
  apply Grothendieck.Groupoidal.ext
  · have h3 : (ι A z ⋙ B).map (eqToHom h2).base
        = eqToHom (by simp [sigmaMap]) := by
      rw [eqToHom_base, eqToHom_map]
    conv =>
      right
      simp only [comp_fiber, eqToHom_fiber, eqToHom_map]
      rw! [Functor.congr_hom h3]
    conv =>
      left
      -- NOTE with rw this will timeout
      rw! [map_map_fiber]
      -- simp only [eqToHom_trans_assoc]
      simp only [Functor.comp_obj, map_obj, whiskerRight_app, Functor.comp_map,
        pre_map_base, map_map_base]
      -- NOTE not sure what some of these simp lemmas are doing,
      -- but when present, rw! [h] works
      -- NOTE with rw this will timeout
      rw! [Functor.congr_hom h]
      simp only [Grpd.comp_eq_comp, Functor.comp_map, Grpd.eqToHom_hom]
    apply eq_of_heq
    simp only [Functor.comp_map, eqToHom_trans_assoc, pre_map_fiber,
      map_map_fiber, Functor.map_comp, eqToHom_map, Grpd.eqToHom_hom,
      Category.assoc, eqToHom_trans, heq_eqToHom_comp_iff,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff, cast_heq_iff_heq]
    simp only [Functor.comp_obj, id_eq, pre_obj_base, Grpd.comp_eq_comp,
      map_obj, whiskerRight_app, Functor.comp_map, heq_cast_iff_heq,
      heq_eqToHom_comp_iff, heq_eq_eq]
  · simp

theorem sigmaMap_comp : sigmaMap B (f ≫ g) = sigmaMap B f ⋙ sigmaMap B g := by
  apply CategoryTheory.Functor.ext
  · intro p q hpq
    simp
  · intro p
    simp

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.
  See `sigmaObj` and `sigmaMap` for the actions of this functor.
 -/
@[simp] def sigma (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : Γ ⥤ Grpd.{v₁,u₁} where
  -- NOTE using Grpd.of here instead of earlier speeds things up
  obj x := Grpd.of $ sigmaObj B x
  map := sigmaMap B
  map_id _ := sigmaMap_id
  map_comp _ _ := sigmaMap_comp

@[simp] theorem sigmaMap_map_base {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).base = (A.map f).map p.base := rfl

variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

theorem sigmaBeckChevalley : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . intros x
    dsimp only [Functor.comp_obj, sigma, sigmaObj]
    rw! [← ιCompPre σ A x]
    rfl
  . intros x y f
    sorry -- this goal might be improved by adding API for Groupoidal.ι and Groupoidal.pre

end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {α β : Γ ⥤ PGrpd.{v₁,u₁}}
  {B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁}}
  (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B)

def pairSectionObjFiber (x : Γ) : (sigma (α ⋙ PGrpd.forgetToGrpd) B).obj x :=
  objMk (PGrpd.objPt α x) (PGrpd.objPt' h x)

/-- `pairSection` takes `x : Γ` and returns a triple
  ⟨ x , a , b ⟩ in the Groupoidal Grothendieck construction,
  which should be thought of as `(x : Γ) × ((a : A x) × (b : B a))`.
  `PGrpd.objPt` and `PGrpd.objPt'` are both used to
  construct a point in a pointed groupoid from respectively
  a functor into `PGrpd` and a functor into `PGrpd` satisfying
  a commutativity (or typing) condition.
-/
def pairSectionObj (x : Γ) : ∫(sigma (α ⋙ PGrpd.forgetToGrpd) B) :=
  objMk x (pairSectionObjFiber h x)

section

/--
  sigma A B x  ∋ pairSectionObjFiber h x
  |
  |
  |  sigma A B f
  |
  V
  sigma A B y ∋ mapPairSectionObjFiber h f
-/
def mapPairSectionObjFiber {x y : Γ} (f : x ⟶ y) : sigmaObj B y :=
  (sigmaMap B f).obj (pairSectionObjFiber h x)

-- TODO clean up
theorem pairSectionMap_aux_aux {x y} (f : x ⟶ y) :
    (ιNatTrans f).app (pairSectionObjFiber h x).base
    ≫ (ι _ y).map (PGrpd.mapPoint α f)
    = (sec α).map f := by
  apply Grothendieck.Groupoidal.ext
  · simp [ι_map, PGrpd.mapPoint]
  · simp [ι_map]

/--
  The left hand side.
  `mapPairSectionObjFiber h f` is an object in the fiber `sigma A B y` over `y`
  The fiber itself consists of bundles, so `(mapPairSectionObjFiber h f).fiber`
  is an object in the fiber `B a` for an `a` in the fiber `A y`.
  But this `a` is isomorphic to `(pairSectionObjFiber y).base`
  and the functor `(ι _ y ⋙ B).map (PGrpd.mapPoint α f)`
  converts the data along this isomorphism.

  The right hand side is `(*)` in the diagram.
     sec α             B
  Γ -------> ∫(A) ------------> Grpd

  x                              (B ⋙ sec α).obj x     objPt' h x
  | f                     (B ⋙ sec α).map f  |              -
  V                                          V              |
  y                              (B ⋙ sec α).obj y          V
                                                           (*)
-/
theorem pairSectionMap_aux {x y} (f : x ⟶ y) :
    ((ι _ y ⋙ B).map (PGrpd.mapPoint α f)).obj (mapPairSectionObjFiber h f).fiber =
    ((sec α ⋙ B).map f).obj (PGrpd.objPt' h x) := by
      simp only [Functor.comp_obj, Grpd.forgetToCat.eq_1, sigma, sigmaObj,
        Functor.comp_map, sigmaMap, PGrpd.forgetToGrpd_map, id_eq, map_obj,
        whiskerRight_app, pre_obj_base, pre_obj_fiber,
        mapPairSectionObjFiber]
      rw [← Grpd.map_comp_obj, pairSectionMap_aux_aux]
      rfl

/--
This can be thought of as the action of parallel transport on f
or perhaps the path over f, but defined within the fiber over y

  sigma A B x     ∋ pairSectionObjFiber h x
  |                        -
  |                        |
  |  sigma A B f           |
  |                        |
  V                        V
  sigma A B y     ∋                PairSectionMapFiber
                   mapPairSectionObjFiber h f ⟶ pairSectionObjFiber h y
-/
def pairSectionMapFiber {x y : Γ} (f : x ⟶ y) :
    mapPairSectionObjFiber h f ⟶ pairSectionObjFiber h y :=
  homMk (PGrpd.mapPoint α f)
    (eqToHom (pairSectionMap_aux h f) ≫ PGrpd.mapPoint' h f)

def pairSectionMap {x y} (f : x ⟶ y) :
    pairSectionObj h x ⟶ pairSectionObj h y :=
  homMk f (pairSectionMapFiber h f)

@[simp] theorem pairSectionMap_fiber_base {x y} (f : x ⟶ y) :
    (pairSectionMap h f).fiber.base = PGrpd.mapPoint α f :=
  rfl

@[simp] theorem pairSectionMap_fiber_fiber {x y} (f : x ⟶ y) :
    (pairSectionMap h f).fiber.fiber
  = eqToHom (pairSectionMap_aux h f) ≫ PGrpd.mapPoint' h f := rfl

@[simp] theorem pairSectionMap_id_base (x) :
    (pairSectionMap h (CategoryStruct.id x)).base = CategoryStruct.id x := by
  simp [pairSectionMap]

-- NOTE these simp lemmas from mathlib should maybe be removed
-- Grpd.forgetToCat...?

@[simp] theorem pairSectionMap_id_fiber (x) :
    (pairSectionMap h (CategoryStruct.id x)).fiber
    = eqToHom (by rw! [sigmaMap_id_obj]):= by
  apply Grothendieck.Groupoidal.ext
  · simp [pairSectionMap_fiber_base]
  · simp [pairSectionMap_fiber_fiber]

theorem pairSectionMap_id (x) :
    pairSectionMap h (CategoryStruct.id x) = CategoryStruct.id _ := by
  apply Grothendieck.ext
  · simp
  · rfl

theorem pairSectionMap_comp_fiber_base {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (pairSectionMap h (f ≫ g)).fiber.base =
    (pairSectionMap h f ≫ pairSectionMap h g).fiber.base := by
  simp [pairSectionMap_fiber_base, PGrpd.mapPoint_comp,
    pairSectionMap, PGrpd.mapPoint, pairSectionMapFiber]

theorem pairSectionMap_comp_fiber_fiber_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
  (B.map ((ι _ (pairSectionObj h z).base).map (PGrpd.mapPoint α (f ≫ g)))).obj
      ((sigmaMap B (pairSectionMap h (f ≫ g)).base).obj (pairSectionObj h x).fiber).fiber =
    (B.map ((sec α).map g)).obj
      ((B.map ((sec α).map f)).obj (PGrpd.objPt' h x)) := by
  have h1 : B.map ((sec α).map f) ⋙ B.map ((sec α).map g)
    = B.map ((sec α).map (f ≫ g)) := by simp
  simp only [← Functor.comp_obj, Functor.congr_obj h1]
  rw! [← pairSectionMap_aux]
  rfl


theorem pairSectionMap_comp_fiber_fiber {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (pairSectionMap h (f ≫ g)).fiber.fiber =
    eqToHom (by simp [pairSectionMap_comp_fiber_fiber_aux])
    ≫ PGrpd.mapPoint' h (f ≫ g) := by
  rw! [homMk_fiber, homMk_fiber]

/--

                   mapPairSectionObjFiber h f ⟶ pairSectionObjFiber h y
  sigma A B y   ∋               pairSectionMapFiber
  |                                      -
  |                                      |
  |  sigma A B g                         |
  |                                      |
  V                                      V
  sigma A B z   ∋ (sigma A B g).map (pairSectionMapFiber) ⋙
                      ...-------------------> ... ---------> mapPairSectionObjFiber
                             mapPairSectionMapFiber
-/
def mapPairSectionMapFiber {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    (sigmaMap B g).obj (mapPairSectionObjFiber h f) ⟶ mapPairSectionObjFiber h g :=
  (sigmaMap B g).map (pairSectionMapFiber h f)

-- TODO rename
theorem pairSectionMap_aux_comp_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (PGrpd.mapPoint α g)).obj
    (((Groupoid.compForgetToCat (ι _ z ⋙ B)).map
    (mapPairSectionMapFiber h f g).base).obj
    ((sigmaMap B g).obj (mapPairSectionObjFiber h f)).fiber)
    = ((sec α ⋙ B).map f ≫ (sec α ⋙ B).map g).obj (PGrpd.objPt' h x) := by
  have h1 : (sec α ⋙ B).map f ≫ (sec α ⋙ B).map g = (sec α ⋙ B).map (f ≫ g) := by
    rw [← Functor.map_comp]
  rw [Functor.congr_obj h1, ← pairSectionMap_aux, PGrpd.mapPoint_comp,
    Functor.map_comp, eqToHom_map, Grpd.comp_eq_comp]
  simp only [Functor.comp_obj, mapPairSectionObjFiber, Functor.map_comp, Grpd.eqToHom_obj]
  congr 2
  have : (sigmaMap B g).obj ((sigmaMap B f).obj (pairSectionObjFiber h x))
      = (sigmaMap B (f ≫ g)).obj (pairSectionObjFiber h x) := by
    rw [sigmaMap_comp]
    rfl
  rw [eq_cast_iff_heq]
  congr

-- TODO rename
theorem pairSectionMap_aux_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (PGrpd.mapPoint α g)).map (mapPairSectionMapFiber h f g).fiber
    = eqToHom (pairSectionMap_aux_comp_aux h f g)
    ≫ ((sec α ⋙ B).map g).map (PGrpd.mapPoint' h f)
    ≫ eqToHom (by rw [pairSectionMap_aux]) := by
  simp only [Functor.comp_map, sigmaObj, sigmaMap, whiskerRight_app,
    mapPairSectionMapFiber, pre_map_fiber, map_map_fiber, Functor.map_comp,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  simp only [Grpd.map_comp_map', eqToHom_trans_assoc, eqToHom_comp_iff, comp_eqToHom_iff,
    eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
  rw! [pairSectionMap_aux_aux]
  simp [pairSectionMapFiber, eqToHom_map]

set_option maxHeartbeats 0
theorem pairSectionMap_comp_fiber {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (pairSectionMap h (f ≫ g)).fiber = (pairSectionMap h f ≫ pairSectionMap h g).fiber := by
  apply Grothendieck.ext
  · rw! [pairSectionMap_comp_fiber_fiber, comp_fiber, comp_fiber]
    rw [eqToHom_fiber, eqToHom_map]
    rw! [comp_fiber, pairSectionMap_aux_comp]
    rw [pairSectionMap_fiber_fiber, PGrpd.mapPoint'_comp,
      Functor.congr_hom (Functor.congr_hom h.symm g) (PGrpd.mapPoint' h f)]
    simp only [sigma, sigmaObj, Functor.comp_obj, PGrpd.forgetToGrpd_obj, Grpd.coe_of, Grpd.forgetToCat.eq_1,
      Cat.of_α, Functor.comp_map, id_eq, comp_base, Grpd.comp_eq_comp, sigmaMap_map_base, PGrpd.forgetToGrpd_map,
      pairSectionMap_fiber_base, eqToHom_trans_assoc, PGrpd.mapPoint', Category.assoc, eqToHom_trans,
      eqToHom_comp_iff]
    simp only [Functor.map_comp, eqToHom_map, ← Category.assoc, eqToHom_trans]
    congr 1
    simp only [Grpd.eqToHom_hom, Grpd.coe_of, cast_cast, Category.assoc]
    rw [conj_eqToHom_iff_heq]-- rw [eqToHom_ca]
    · simp only [heq_cast_iff_heq, cast_heq_iff_heq]
      congr 1
      · simp [Grpd.eqToHom_obj]
      · simp [Grpd.eqToHom_obj, PGrpd.objPt', PGrpd.objPt]
        rfl
      · simp
    · congr 2
      simp only [PGrpd.objPt', Functor.comp_obj, PGrpd.forgetToGrpd_obj,
        Grpd.coe_of, PGrpd.objPt, Grpd.eqToHom_obj, cast_cast, cast_eq]
      -- NOTE there is something bad here where
      -- on one hand it has PointedCategory.Pt
      -- and on the other it has PointedGroupoid.Pt
      rfl
  · simp [pairSectionMap_comp_fiber_base, PGrpd.mapPoint_comp, comp_fiber, pairSectionMap, PGrpd.mapPoint, pairSectionMapFiber]

end

theorem pairSectionMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    pairSectionMap _ (f ≫ g) = pairSectionMap h f ≫ pairSectionMap h g := by
  apply Grothendieck.Groupoidal.ext
  · simp [pairSectionMap_comp_fiber]
  · rfl

def pairSection : Γ ⥤ ∫(sigma (α ⋙ PGrpd.forgetToGrpd) B) where
    obj := pairSectionObj h
    map := pairSectionMap h
    map_id := pairSectionMap_id _
    map_comp := pairSectionMap_comp _

theorem pairSection_comp_forget :
    (pairSection h) ⋙ Grothendieck.forget _ = Functor.id Γ :=
  rfl

def pair : Γ ⥤ PGrpd.{v₁,u₁} := pairSection h ⋙ toPGrpd _

theorem pair_comp_forget :
    pair h ⋙ PGrpd.forgetToGrpd = sigma (α ⋙ PGrpd.forgetToGrpd) B := by
  unfold pair
  rw [Functor.assoc]
  exact rfl

end

variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)

def fstAux : sigma A B ⟶ A where
  app x := Grpd.homOf (Grothendieck.forget _)

def fst : ∫(sigma A B) ⥤ ∫(A) :=
  map (fstAux B)

-- JH: changed name from `snd` to `assoc`
-- maybe we should use `Grothendieck.functorFrom`
-- sigma A B : Γ ⥤ Grpd
-- ∫(sigma A B) = Γ.(sigma A B)
-- B : Γ.A ⥤ Grpd
-- ∫(B) = (Γ.A).B
-- Γ.(sigma A B) ≅ (Γ.A).B
def assoc : ∫(sigma A B) ⥤ ∫(B) := sorry

def snd : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ toPGrpd B

-- set_option maxHeartbeats 0 in
-- def snd {Γ : Grpd} (A : Γ ⥤ Cat.of Grpd.{v₁,u₁})
--     (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁}) :
--   Grothendieck.Groupoidal (sigma A B) ⥤  Grothendieck.Groupoidal B where
--   obj x := by
--     rcases x with ⟨base,fiber,fiberfiber⟩
--     fconstructor
--     fconstructor
--     . exact base
--     . exact fiber
--     . exact fiberfiber
--   map {x y} f := by
--     rcases f with ⟨base,fiber,fiberfiber⟩
--     fconstructor
--     fconstructor
--     . exact base
--     . exact fiber
--     . refine eqToHom ?_ ≫ fiberfiber
--       . simp[Grpd.forgetToCat,Grothendieck.Groupoidal.pre,whiskerRight,map]
--         set I := ((ι A y.base).map fiber)
--         set J := (@Grothendieck.ιNatTrans (↑Γ) Groupoid.toCategory (Groupoid.compForgetToCat A) x.base y.base base).app x.fiber.base
--         have eq1 : (B.map I).obj ((B.map J).obj x.fiber.fiber) = (B.map J ≫ B.map I).obj x.fiber.fiber := rfl
--         rw [eq1,<- B.map_comp J I]
--         simp[J,I,CategoryStruct.comp,Grothendieck.comp,ι]
--         refine Functor.congr_obj ?_ x.fiber.fiber
--         refine congrArg B.map ?_
--         apply Grothendieck.ext
--         . simp
--         . simp
--   map_id := by
--     intro x
--     simp[Grothendieck.Hom.rec,Grothendieck.Hom.rec]
--     sorry
--   map_comp := sorry

def ABToAlpha : ∫(sigma A B) ⥤ PGrpd :=
  fst B ⋙ toPGrpd A

def ABToB : ∫(ABToAlpha B ⋙ PGrpd.forgetToGrpd) ⥤ Grpd := by
  refine ?_ ⋙ fst B ⋙ B
  exact Grothendieck.forget (Groupoid.compForgetToCat (ABToAlpha B ⋙ PGrpd.forgetToGrpd))

def ABToBeta : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ (Grothendieck.Groupoidal.toPGrpd B)

end FunctorOperation

open FunctorOperation

/-- The formation rule for Σ-types for the ambient natural model `base` -/
def baseSig : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun p =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv p
    yonedaEquiv (yonedaCatEquiv.symm (sigma A B))
  naturality := sorry -- do not attempt

def basePair : base.uvPolyTp.compDom base.uvPolyTp ⟶ base.Tm where
  app Γ := fun ε =>
    let ⟨α,B,β,h⟩ := baseUvPolyTpCompDomEquiv ε
    yonedaEquiv (yonedaCatEquiv.symm (pair h))
  naturality := by sorry

def Sigma_Comm : basePair ≫ base.tp = (base.uvPolyTp.comp base.uvPolyTp).p ≫ baseSig := by sorry

def PairUP' {Γ : Ctx.{u}} (AB : yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty) :
    yoneda.obj (base.ext (AB ≫ baseSig)) ⟶ base.uvPolyTp.compDom base.uvPolyTp := by
  refine yonedaEquiv.invFun ?_
  refine baseUvPolyTpCompDomEquiv.invFun ?_
  let AB' := baseUvPolyTpEquiv (yonedaEquiv.toFun AB)
  exact ⟨ABToAlpha AB'.snd, ABToB AB'.snd, ABToBeta AB'.snd, by
    -- simp
    sorry
  ⟩

-- NOTE this has been refactored through sec'
-- def GammaToSigma {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
--     (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
--     (h : top ≫ base.tp = left ≫ baseSig) :
--     (yoneda.obj Γ) ⟶ yoneda.obj (base.ext (left ≫ baseSig)) :=
--   (base.disp_pullback (left ≫ baseSig)).lift top (𝟙 _) (by rw[Category.id_comp,h])

-- def GammaToSigmaInv_disp {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : (base.sec' top _ h) ≫ (yoneda.map (base.disp (left ≫ baseSig))) = 𝟙 (yoneda.obj Γ) := by
--   simp [sec']

def PairUP {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
    (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
    (h : top ≫ base.tp = left ≫ baseSig) :
    (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp :=
  base.sec' h ≫ (PairUP' left)

namespace SigmaPullback

def somethingEquiv' {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
  (A : (Ctx.toGrpd.obj Γ) ⥤ Grpd.{u,u})
  (B : ∫(A) ⥤ Grpd.{u,u})
  (sigAB : ↑(Ctx.toGrpd.obj Γ) ⥤ Grpd.{u,u})
  (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
  (h : ab ⋙ PGrpd.forgetToGrpd = sigAB) :
  (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u}) ×'
  (α ⋙ PGrpd.forgetToGrpd = A) := sorry

theorem yonedaCatEquiv_baseSig {Γ : Ctx} {A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}}
    {B : ∫(A) ⥤ Grpd.{u,u}} :
    yonedaCatEquiv ((baseUvPolyTpEquiv'.symm ⟨A,B⟩) ≫ baseSig) = sigma A B
    := by
  simp only [yonedaCatEquiv, Equiv.trans_apply, yonedaEquiv_comp, baseSig, Equiv.symm_trans_apply, Equiv.toFun_as_coe, baseUvPolyTpEquiv]
  rw [yonedaCatEquivAux.apply_eq_iff_eq_symm_apply,
    yonedaEquiv.apply_eq_iff_eq_symm_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  congr

def somethingEquiv {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
    {AB : y(Γ) ⟶ base.Ptp.obj base.{u}.Ty}
    (h : ab ≫ base.tp = AB ≫ baseSig)
    : (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u})
    × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : ∫(A) ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ Grothendieck.Groupoidal.map (eqToHom h) ⋙ B :=
  let AB' := baseUvPolyTpEquiv (yonedaEquiv AB)
  let A := AB'.1
  let B := AB'.2
  let h1 := baseTmEquiv ⟨AB ≫ baseSig,ab,h⟩
  let sigAB := h1.1
  let ab' := h1.2.1
  let hab := h1.2.2
  have h2 : ab' ⋙ PGrpd.forgetToGrpd = sigma AB'.fst B := by
      rw [hab, baseTmEquiv_fst, ← yonedaCatEquiv_baseSig, Sigma.eta]
      simp [AB', baseUvPolyTpEquiv]
  let α := sec ab' ⋙ map (eqToHom h2) ⋙ fst B ⋙ toPGrpd A
  ⟨ A,
    α,
    B,
    sorry,
    sorry,
    sorry ⟩

-- strategy: want to first show that cones of the diagram
-- correspond to some functor data,
-- then do the functor constructions
def lift {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
    {AB : y(Γ) ⟶ base.Ptp.obj base.{u}.Ty}
    (h : ab ≫ base.tp = AB ≫ baseSig) :
    (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp :=
  yonedaEquiv.invFun $
  baseUvPolyTpCompDomEquiv'.invFun
  (somethingEquiv h)

end SigmaPullback

theorem PairUP_Comm1' {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : PairUP' left ≫ basePair = (yoneda.map (base.disp (left ≫ baseSig))) ≫ top := by
  sorry

theorem PairUP_Comm1 {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : (PairUP top left h) ≫ basePair = top := by
  unfold PairUP
  rw[Category.assoc,PairUP_Comm1' top left h,<- Category.assoc,
    sec'_disp,Category.id_comp]

theorem PairUP_Comm2' {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : PairUP' left ≫ (base.uvPolyTp.comp base.uvPolyTp).p = (yoneda.map (base.disp (left ≫ baseSig))) ≫ left := by
  sorry

theorem PairUP_Comm2 {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
    (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
    (h : top ≫ base.tp = left ≫ baseSig) :
    (PairUP top left h) ≫ (base.uvPolyTp.comp base.uvPolyTp).p = left
    := by
  unfold PairUP
  rw[Category.assoc,PairUP_Comm2' top left h,<- Category.assoc,
    sec'_disp,Category.id_comp]

theorem PairUP_Uniqueness {Γ : Ctx}
    (f : (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp) :
    f = (PairUP (f ≫  basePair)
      (f ≫ (base.uvPolyTp.comp base.uvPolyTp).p)
      (by rw[Category.assoc,Category.assoc]; congr 1; exact Sigma_Comm))     := by
  unfold PairUP
  refine (base.uvPolyTpCompDomEquiv Γ).injective ?_
  refine Sigma.ext ?_ ?_
  . sorry
  . sorry

def is_pb : IsPullback basePair (base.uvPolyTp.comp base.uvPolyTp).p base.tp baseSig := by
  sorry

def baseSigma : NaturalModelSigma base where
  Sig := baseSig
  pair := basePair
  Sig_pullback := is_pb

def smallUSigma : NaturalModelSigma smallU := sorry

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma
  | 1 => smallUSigma
  | 2 => smallUSigma
  | 3 => baseSigma
  | (n+4) => by omega

end GroupoidModel
end
