import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModel
import GroupoidModel.RepPullbackCone
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

end ForOther

-- NOTE these simp lemmas from mathlib should maybe be removed
-- Grpd.forgetToCat...?
-- Some `AsSmall` related lemmas

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal PGrpd

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
@[simps] def sigma (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : Γ ⥤ Grpd.{v₁,u₁} where
  -- NOTE using Grpd.of here instead of earlier speeds things up
  obj x := Grpd.of $ sigmaObj B x
  map := sigmaMap B
  map_id _ := sigmaMap_id
  map_comp _ _ := sigmaMap_comp

@[simp] theorem sigmaMap_map_base {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).base = (A.map f).map p.base := rfl

variable (B) {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

-- NOTE formerly called `sigmaBeckChevalley`
theorem sigma_naturality : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
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
  {B : ∫(α ⋙ forgetToGrpd) ⥤ Grpd.{v₁,u₁}}
  (h : β ⋙ forgetToGrpd = sec _ α rfl ⋙ B)

def pairSectionObjFiber (x : Γ) : (sigma (α ⋙ forgetToGrpd) B).obj x :=
  objMk (objPt α x) (objPt' h x)

/-- `pairSection` takes `x : Γ` and returns a triple
  ⟨ x , a , b ⟩ in the Groupoidal Grothendieck construction,
  which should be thought of as `(x : Γ) × ((a : A x) × (b : B a))`.
  `objPt` and `objPt'` are both used to
  construct a point in a pointed groupoid from respectively
  a functor into `PGrpd` and a functor into `PGrpd` satisfying
  a commutativity (or typing) condition.
-/
def pairSectionObj (x : Γ) : ∫(sigma (α ⋙ forgetToGrpd) B) :=
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

-- TODO rename
theorem pairSectionMap_aux_aux {x y} (f : x ⟶ y) :
    (ιNatTrans f).app (pairSectionObjFiber h x).base
    ≫ (ι _ y).map (mapPoint α f)
    = (sec _ α rfl).map f := by
  apply Grothendieck.Groupoidal.ext
  · simp [ι_map, mapPoint, Grpd.forgetToCat]
  · simp [ι_map]

/--
  The left hand side.
  `mapPairSectionObjFiber h f` is an object in the fiber `sigma A B y` over `y`
  The fiber itself consists of bundles, so `(mapPairSectionObjFiber h f).fiber`
  is an object in the fiber `B a` for an `a` in the fiber `A y`.
  But this `a` is isomorphic to `(pairSectionObjFiber y).base`
  and the functor `(ι _ y ⋙ B).map (mapPoint α f)`
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
    ((ι _ y ⋙ B).map (mapPoint α f)).obj (mapPairSectionObjFiber h f).fiber =
    ((sec _ α rfl ⋙ B).map f).obj (objPt' h x) := by
  simp only [Functor.comp_obj, Grpd.forgetToCat.eq_1, sigma, sigmaObj,
    Functor.comp_map, sigmaMap, forgetToGrpd_map, id_eq, map_obj,
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
  homMk (mapPoint α f)
    (eqToHom (pairSectionMap_aux h f) ≫ mapPoint' h f)

def pairSectionMap {x y} (f : x ⟶ y) :
    pairSectionObj h x ⟶ pairSectionObj h y :=
  homMk f (pairSectionMapFiber h f)

@[simp] theorem pairSectionMap_fiber_base {x y} (f : x ⟶ y) :
    (pairSectionMap h f).fiber.base = mapPoint α f :=
  rfl

@[simp] theorem pairSectionMap_fiber_fiber {x y} (f : x ⟶ y) :
    (pairSectionMap h f).fiber.fiber
  = eqToHom (pairSectionMap_aux h f) ≫ mapPoint' h f := rfl

@[simp] theorem pairSectionMap_id_base (x) :
    (pairSectionMap h (CategoryStruct.id x)).base = CategoryStruct.id x := by
  simp [pairSectionMap]

@[simp] theorem pairSectionMap_id_fiber (x) :
    (pairSectionMap h (CategoryStruct.id x)).fiber
    = eqToHom (by rw! [sigmaMap_id_obj]):= by
  apply Grothendieck.Groupoidal.ext
  · simp [pairSectionMap_fiber_base, Grpd.forgetToCat]
  · simp [pairSectionMap_fiber_fiber, Grpd.forgetToCat]

theorem pairSectionMap_id (x) :
    pairSectionMap h (CategoryStruct.id x) = CategoryStruct.id _ := by
  apply Grothendieck.ext
  · simp
  · rfl

theorem pairSectionMap_comp_fiber_base {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (pairSectionMap h (f ≫ g)).fiber.base =
    (pairSectionMap h f ≫ pairSectionMap h g).fiber.base := by
  simp [pairSectionMap_fiber_base, mapPoint_comp,
    pairSectionMap, mapPoint, pairSectionMapFiber]

theorem pairSectionMap_comp_fiber_fiber_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
  (B.map ((ι _ (pairSectionObj h z).base).map (mapPoint α (f ≫ g)))).obj
      ((sigmaMap B (pairSectionMap h (f ≫ g)).base).obj (pairSectionObj h x).fiber).fiber =
    (B.map ((sec _ α rfl).map g)).obj
      ((B.map ((sec _ α rfl).map f)).obj (objPt' h x)) := by
  have h1 : B.map ((sec _ α rfl).map f) ⋙ B.map ((sec _ α rfl).map g)
    = B.map ((sec _ α rfl).map (f ≫ g)) := by simp
  simp only [← Functor.comp_obj, Functor.congr_obj h1]
  rw! [← pairSectionMap_aux]
  rfl


theorem pairSectionMap_comp_fiber_fiber {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (pairSectionMap h (f ≫ g)).fiber.fiber =
    eqToHom (by simp [pairSectionMap_comp_fiber_fiber_aux, Grpd.forgetToCat])
    ≫ mapPoint' h (f ≫ g) := by
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
    ((ι _ z ⋙ B).map (mapPoint α g)).obj
    (((ι _ z ⋙ B ⋙ Grpd.forgetToCat).map
    (mapPairSectionMapFiber h f g).base).obj
    ((sigmaMap B g).obj (mapPairSectionObjFiber h f)).fiber)
    = ((sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g).obj (objPt' h x) := by
  have h1 : (sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g = (sec _ α rfl ⋙ B).map (f ≫ g) := by
    rw [← Functor.map_comp]
  rw [Functor.congr_obj h1, ← pairSectionMap_aux, mapPoint_comp,
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
    ((ι _ z ⋙ B).map (mapPoint α g)).map (mapPairSectionMapFiber h f g).fiber
    = eqToHom (pairSectionMap_aux_comp_aux h f g)
    ≫ ((sec _ α rfl ⋙ B).map g).map (mapPoint' h f)
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
    rw [pairSectionMap_fiber_fiber, mapPoint'_comp,
      Functor.congr_hom (Functor.congr_hom h.symm g) (mapPoint' h f)]
    simp only [sigma, sigmaObj, Functor.comp_obj, forgetToGrpd_obj, Grpd.coe_of, Grpd.forgetToCat.eq_1,
      Cat.of_α, Functor.comp_map, id_eq, comp_base, Grpd.comp_eq_comp, sigmaMap_map_base, forgetToGrpd_map,
      pairSectionMap_fiber_base, eqToHom_trans_assoc, mapPoint', Category.assoc, eqToHom_trans,
      eqToHom_comp_iff]
    simp only [Functor.map_comp, eqToHom_map, ← Category.assoc, eqToHom_trans]
    congr 1
    simp only [Grpd.eqToHom_hom, Grpd.coe_of, cast_cast, Category.assoc]
    rw [conj_eqToHom_iff_heq]-- rw [eqToHom_ca]
    · simp only [heq_cast_iff_heq, cast_heq_iff_heq]
      congr 1
      · simp [Grpd.eqToHom_obj]
      · simp [Grpd.eqToHom_obj, objPt', objPt]
        rfl
      · simp
    · congr 2
      simp only [objPt', Functor.comp_obj, forgetToGrpd_obj,
        Grpd.coe_of, objPt, Grpd.eqToHom_obj, cast_cast, cast_eq]
      -- NOTE there is something bad here where
      -- on one hand it has PointedCategory.Pt
      -- and on the other it has PointedGroupoid.Pt
      rfl
  · simp [pairSectionMap_comp_fiber_base, mapPoint_comp, comp_fiber, pairSectionMap, mapPoint, pairSectionMapFiber]

end

theorem pairSectionMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    pairSectionMap _ (f ≫ g) = pairSectionMap h f ≫ pairSectionMap h g := by
  apply Grothendieck.Groupoidal.ext
  · simp [pairSectionMap_comp_fiber]
  · rfl

def pairSection : Γ ⥤ ∫(sigma (α ⋙ forgetToGrpd) B) where
    obj := pairSectionObj h
    map := pairSectionMap h
    map_id := pairSectionMap_id _
    map_comp := pairSectionMap_comp _

theorem pairSection_comp_forget :
    (pairSection h) ⋙ Grothendieck.forget _ = Functor.id Γ :=
  rfl

def pair : Γ ⥤ PGrpd.{v₁,u₁} := pairSection h ⋙ toPGrpd _

@[simp] theorem pair_comp_forgetToGrpd :
    pair h ⋙ forgetToGrpd = sigma (α ⋙ forgetToGrpd) B := rfl

section

variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

include h in
lemma pairSection_naturality_aux : (σ ⋙ β) ⋙ forgetToGrpd
    = sec _ (σ ⋙ α) rfl ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B := by
  conv => right; erw [← Functor.assoc, ← sec_naturality]
  simp only [Functor.assoc, h]

-- TODO consider changing this statement. Namely the `map (eqToHom ⋯)` part.
theorem pairSection_naturality : σ ⋙ pairSection h =
    pairSection (pairSection_naturality_aux h σ)
    ⋙ map (eqToHom (sigma_naturality B σ).symm) ⋙ pre _ _ := by
  apply CategoryTheory.Functor.ext
  · sorry
  · intro x
    apply obj_ext_hEq
    · simp [pairSection, pairSectionObj]
    · rw [heq_eq_eq]
      have : (ι ((σ ⋙ α) ⋙ forgetToGrpd) x ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B)
          ⋙ Grpd.forgetToCat =
          (ι (α ⋙ forgetToGrpd) (σ.obj x) ⋙ B) ⋙ Grpd.forgetToCat := by
        rw [← ιCompPre]
        rfl
      apply obj_ext_hEq
      -- TODO tidy this up by adding some lemmas +
      -- block simp lemmas that simplify too far
      · simp only [pairSection, Functor.comp_obj, pairSectionObj, objMk,
          pairSectionObjFiber, forgetToGrpd_obj, map_obj,
          sigma_obj, sigmaObj, pre_obj_fiber, eqToHom_app, Grpd.eqToHom_obj,
          objPt]
        rw! [Grothendieck.cast_eq this]
      · simp only [pairSection, Functor.comp_obj, pairSectionObj, objMk,
          pairSectionObjFiber, objPt, objPt', Grpd.eqToHom_obj,
          map_obj, sigma_obj, sigmaObj, pre_obj_fiber, cast_heq_iff_heq]
        rw! [eqToHom_app, Grpd.eqToHom_obj, Grothendieck.cast_eq this]
        simp [Grpd.eqToHom_obj]

-- TODO consider removal, see `pairSection_naturality`
theorem map_eqToHom_toPGrpd {F G : Γ ⥤ Grpd} (h : F = G) :
    map (eqToHom h) ⋙ toPGrpd G = toPGrpd F := by
  subst h
  simp [map_id_eq, Functor.id_comp]

theorem pair_naturality : σ ⋙ pair h =
    @pair _ _ (σ ⋙ α) (σ ⋙ β) (pre (α ⋙ forgetToGrpd) σ ⋙ B) (by
      erw [Functor.assoc, h, ← Functor.assoc, sec_naturality, Functor.assoc])
    := by
  dsimp only [pair]
  rw [← Functor.assoc, pairSection_naturality, Functor.assoc]
  congr 1
  convert_to map (eqToHom _)
  ⋙ Grothendieck.Groupoidal.pre (sigma (α ⋙ forgetToGrpd) B) σ
  ⋙ toPGrpd (sigma (α ⋙ forgetToGrpd) B)
  = toPGrpd (sigma (σ ⋙ α ⋙ forgetToGrpd) (Grothendieck.Groupoidal.pre (α ⋙ forgetToGrpd) σ ⋙ B))
  rw [pre_toPGrpd, map_eqToHom_toPGrpd]

end

end

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁})

@[simps] def fstAux : sigma A B ⟶ A where
  app x := Grpd.homOf (Grothendieck.forget _)

def fst' : ∫(sigma A B) ⥤ ∫(A) :=
  map (fstAux B)

def fst : ∫(sigma A B) ⥤ PGrpd :=
  fst' B ⋙ toPGrpd A

-- TODO move to ForMathlib and Grothendieck
section
variable {C : Type u} [Category.{v} C]
    {F G : C ⥤ Cat.{v₂,u₂}}

theorem _root_.CategoryTheory.Grothendieck.map_forget (α : F ⟶ G) :
    Grothendieck.map α ⋙ Grothendieck.forget G =
    Grothendieck.forget F := by
  rfl

variable
    {F G : C ⥤ Grpd.{v₂,u₂}}
theorem _root_.CategoryTheory.Grothendieck.Groupoidal.map_forget
    (α : F ⟶ G) : map α ⋙ forget =
    Grothendieck.Groupoidal.forget := by
  rfl

end
-- END

theorem fst_forgetToGrpd : fst B ⋙ forgetToGrpd = forget ⋙ A := by
  dsimp only [fst, fst']
  rw [Functor.assoc, Grothendieck.Groupoidal.IsMegaPullback.comm_sq,
    ← Functor.assoc, map_forget]


end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁})

@[simp] def assocFib (x : Γ) : sigmaObj B x ⥤ ∫(B) :=
  pre _ _

def assocIso {x y : Γ} (f : x ⟶ y) :
    assocFib B x ≅ sigmaMap B f ⋙ assocFib B y :=
  preNatIso B (ιNatIso A f)

@[simp] theorem assocIso_id {x} :
    assocIso B (𝟙 x) = eqToIso (by simp [sigmaMap_id, Functor.id_comp]) := by
  simp [assocIso, preNatIso_congr B (ιNatIso_id A x), preNatIso_eqToIso]

theorem assocIso_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) : assocIso B (f ≫ g) =
    assocIso B f ≪≫ isoWhiskerLeft (sigmaMap B f) (assocIso B g)
    ≪≫ eqToIso (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp [assocIso, preNatIso_congr B (ιNatIso_comp A f g), preNatIso_comp, assocIso,
    sigmaMap, isoWhiskerLeft_trans]
  rfl

def assocHom {x y : Γ} (f : x ⟶ y) :
    assocFib B x ⟶ sigmaMap B f ⋙ assocFib B y :=
  (assocIso B f).hom

@[simp] theorem assocHom_id {x : Γ} :
    assocHom B (𝟙 x) = eqToHom (by simp [sigmaMap_id, Functor.id_comp]) := by
  simp [assocHom, assocIso_id]

theorem assocHom_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    assocHom B (f ≫ g) = assocHom B f ≫ whiskerLeft (sigmaMap B f) (assocHom B g) ≫ eqToHom (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp [assocHom, assocIso_comp]

-- NOTE this used to be called `snd`, I thought maybe calling the maps
-- into PGrpd `fst` and `snd` might be a bit more consistent
def assoc : ∫(sigma A B) ⥤ ∫(B) :=
  functorFrom (assocFib B) (assocHom B) (by simp) (by simp [assocHom_comp])

def snd : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ toPGrpd B

def dependent : ∫(fst B ⋙ forgetToGrpd) ⥤ Grpd := forget ⋙ fst' B ⋙ B

@[simp] theorem forget_obj {C : Type u} [Category.{v, u} C] (F : C ⥤ Grpd)
    (X : ∫(F)) : forget.obj X = X.base :=
  Grothendieck.forget_obj _ _

@[simp] theorem forget_map {C : Type u} [Category.{v, u} C] (F : C ⥤ Grpd)
    {X Y : ∫(F)} (f : X ⟶ Y) : forget.map f = f.base :=
  Grothendieck.forget_map _ _

theorem assoc_forget : assoc B ⋙ forget = fst' B := by
  dsimp [assoc, fst']
  apply Functor.hext
  · intro p
    simp [ι_obj]
  · intro p q h
    simp only [heq_eq_eq]
    apply Grothendieck.Groupoidal.ext
    -- TODO improve API for these two goals
    · simp [ι_map, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso, Grpd.forgetToCat]
    · simp [ι_map, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso]

theorem snd_forgetToGrpd : snd B ⋙ forgetToGrpd = sec _ (fst B) rfl ⋙ dependent B :=
  calc
    _ = assoc B ⋙ forget ⋙ B := rfl
    _ = fst' B ⋙ B := by rw [← assoc_forget]; rfl
    _ = _ := rfl

end

end FunctorOperation

open FunctorOperation

def smallUSig_app {Γ : Ctx.{max u (v+1)}}
    (AB : y(Γ) ⟶ smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty) :
    y(Γ) ⟶ smallU.{v, max u (v+1)}.Ty :=
  yonedaCategoryEquiv.symm (sigma _ (smallUPTpEquiv AB).2)

theorem smallUSig_naturality {Γ Δ : Ctx} (f : Δ ⟶ Γ)
    (AB : y(Γ) ⟶ smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty) :
    smallUSig_app (ym(f) ≫ AB) = ym(f) ≫ smallUSig_app AB := by
  dsimp [yonedaCategoryEquiv, smallUSig_app]
  erw [← Functor.map_comp, ← toCoreAsSmallEquiv_symm_naturality_left,
    sigma_naturality, smallUPTpEquiv_naturality_left]
  rfl

/-- The formation rule for Σ-types for the ambient natural model `base`
  If possible, don't use NatTrans.app on this,
  instead precompose it with maps from representables.
-/

def smallUSig : smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty
  ⟶ smallU.{v, max u (v+1)}.Ty :=
  NatTrans.yonedaMk smallUSig_app smallUSig_naturality

lemma smallUSig_app_eq {Γ : Ctx} (AB : y(Γ) ⟶ _) : AB ≫ smallUSig =
    yonedaCategoryEquiv.symm (sigma _ (smallUPTpEquiv AB).2) := by
  simp only [smallUSig, smallUSig_app, NatTrans.yonedaMk_app]

def smallUPair_app {Γ : Ctx.{max u (v+1)}}
    (ab : y(Γ) ⟶ smallU.{v, max u (v+1)}.uvPolyTp.compDom
    smallU.{v, max u (v+1)}.uvPolyTp)
    : y(Γ) ⟶ smallU.{v, max u (v+1)}.Tm :=
  yonedaCategoryEquiv.symm (pair (smallUCompDomEquiv ab).2.2.2)

theorem smallUPair_naturality {Γ Δ : Ctx} (f : Δ ⟶ Γ)
    (ab : y(Γ) ⟶ smallU.{v, max u (v+1)}.uvPolyTp.compDom
    smallU.{v, max u (v+1)}.uvPolyTp) :
    smallUPair_app (ym(f) ≫ ab) = ym(f) ≫ smallUPair_app ab := by
  sorry

def smallUPair : smallU.{v, max u (v+1)}.uvPolyTp.compDom
    smallU.{v, max u (v+1)}.uvPolyTp
    ⟶ smallU.{v, max u (v+1)}.Tm :=
  NatTrans.yonedaMk smallUPair_app smallUPair_naturality

lemma smallUPair_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ _) : ab ≫ smallUPair =
    yonedaCategoryEquiv.symm (pair (smallUCompDomEquiv ab).2.2.2) := by
  simp only [smallUPair, smallUPair_app, NatTrans.yonedaMk_app]

namespace SigmaPullback

open Limits

section
open Grothendieck.Groupoidal.IsMegaPullback

-- JH: this seems kind of bad to me. See `comm_sq`
-- theorem lift_heq_id {Γ : Type*} [Category Γ] {A B : Γ ⥤ Grpd.{v,v}}
--     (h : A = B) : HEq ((lift (toPGrpd B)) forget
--     (h ▸ comm_sq A : toPGrpd B ⋙ forgetToGrpd = forget ⋙ A))
--     (Functor.id ∫(B)) := by
--   subst h
--   apply heq_of_eq
--   symm
--   apply lift_uniq
--   · rfl
--   · rfl

-- JH: this seems kind of bad to me. See `comm_sq`
theorem lift_heq_id_comp {Γ C : Type*} [Category Γ] [Category C]
    {A B : Γ ⥤ Grpd.{v,v}}
    (h : A = B) (F : ∫(A) ⥤ C) : HEq ((lift (toPGrpd B)) forget
    (h ▸ comm_sq A : toPGrpd B ⋙ forgetToGrpd = forget ⋙ A) ⋙ F)
    (Functor.id ∫(A) ⋙ F) := by
  subst h
  apply heq_of_eq
  congr 1
  symm
  apply lift_uniq
  · rfl
  · rfl
end

-- JH: there should be a better way to prove this,
-- by rewriting backwards
-- resulting in an equality of morphisms in a category (not evil) as the goal
-- rather than a morphism of functors (evil).
set_option maxHeartbeats 0
theorem comm_sq : smallUPair.{v} ≫ smallU.{v}.tp =
    (smallU.{v}.uvPolyTp.comp smallU.{v}.uvPolyTp).p ≫ smallUSig := by
  apply hom_ext_yoneda
  intros Γ ab
  simp only [← Category.assoc]
  rw [smallUPair_app_eq, smallUSig_app_eq, smallU_tp]
  rw [← yonedaCategoryEquiv_symm_naturality_right]
  rw [pair_comp_forgetToGrpd]
  congr 2
  · rw [smallUCompDomEquiv_apply_fst_forgetToGrpd]
  · rw [smallUCompDomEquiv_apply_snd_fst]
    apply lift_heq_id_comp
    · rw [smallUCompDomEquiv_apply_fst_forgetToGrpd]

def repPullbackConeEquivToFun
    (s : RepPullbackCone smallU.{v}.tp smallUSig.{v})
    : (Γ : Ctx.{max u (v+1)})
    × (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v})
    × (B : ∫(A) ⥤ Grpd.{v,v})
    × (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' ab ⋙ PGrpd.forgetToGrpd = sigma A B :=
  ⟨ s.pt,
    (smallUPTpEquiv s.snd).fst,
    (smallUPTpEquiv s.snd).snd,
    yonedaCategoryEquiv s.fst,
    by erw [← yonedaCategoryEquiv_naturality_right, s.condition,
        smallUSig_app_eq, yonedaCategoryEquiv.apply_symm_apply] ⟩

def repPullbackConeEquivInvFun
    (Γ : Ctx.{max u (v+1)})
    (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v})
    (B : ∫(A) ⥤ Grpd.{v,v})
    (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    (h : ab ⋙ PGrpd.forgetToGrpd = sigma A B) :
    RepPullbackCone smallU.{v}.tp smallUSig.{v} :=
  RepPullbackCone.mk Γ
    (yonedaCategoryEquiv.symm ab)
    (smallUPTpEquiv.symm ⟨A,B⟩)
    (by
      erw [← yonedaCategoryEquiv_symm_naturality_right, h,
        smallUSig_app_eq, smallUPTpEquiv.apply_symm_apply])

def repPullbackConeEquiv :
    RepPullbackCone smallU.{v}.tp smallUSig.{v}
    ≃ (Γ : Ctx.{max u (v+1)})
    × (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v})
    × (B : ∫(A) ⥤ Grpd.{v,v})
    × (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' ab ⋙ PGrpd.forgetToGrpd = sigma A B where
  toFun     := repPullbackConeEquivToFun
  invFun  X := repPullbackConeEquivInvFun X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2
  left_inv  := sorry
  right_inv := sorry

def anotherEquiv (Γ : Ctx.{max u (v+1)}) (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v})
    (B : ∫(A) ⥤ Grpd.{v,v}) :
    (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' ab ⋙ PGrpd.forgetToGrpd = sigma A B
    ≃ (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ map (eqToHom h) ⋙ B where
  toFun := fun ⟨ab,hab⟩ => ⟨
    Grothendieck.Groupoidal.sec (sigma A B) ab hab ⋙ fst _,
    Grothendieck.Groupoidal.sec (sigma A B) ab hab ⋙ snd _,
    by rw [Functor.assoc, fst_forgetToGrpd, ← Functor.assoc,
      sec_forget, Functor.id_comp],
    by
       -- simp 
       rw [Functor.assoc, snd_forgetToGrpd]
       sorry ⟩
  invFun := fun ⟨α,β,hα,hβ⟩ => sorry
  left_inv := by sorry
  right_inv := by sorry

def baseUvPolyTpCompDomEquiv' {Γ : Ctx.{max u (v+1)}} :
    (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    × (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ B
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v})
    × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    × (B : ∫(A) ⥤ Grpd.{v,v})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = sec _ α rfl ⋙ map (eqToHom h) ⋙ B where
  toFun := fun ⟨α,B,β,h⟩ => ⟨α ⋙ PGrpd.forgetToGrpd, α, B, β, rfl, by
    rw [h, eqToHom_refl, map_id_eq]
    rfl⟩
  invFun := fun ⟨A,α,B,β,hA,hB⟩ => ⟨α, map (eqToHom hA) ⋙ B, β, by rw [hB] ⟩
  left_inv := by
    intro ⟨α,B,β,h⟩
    dsimp
    congr!
    simp [map_id_eq, Functor.id_comp]
  right_inv := by
    intro ⟨A,α,B,β,h1,h2⟩
    subst h1
    congr!
    · simp [eqToHom_refl, map_id_eq, Functor.id_comp]

variable (s : RepPullbackCone smallU.{v}.tp smallUSig.{v})

abbrev A := (smallUPTpEquiv s.snd).fst

abbrev B := (smallUPTpEquiv s.snd).snd

def lift' : y(Ctx.ofGrpd.obj $ Grpd.of ∫(sigma (A s) (B s))) ⟶
    smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp :=
  smallUCompDomEquiv.symm
    ⟨ fst (B s), dependent (B s), snd (B s), snd_forgetToGrpd _ ⟩

def lift : y(s.pt) ⟶ smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp :=
  ym(smallU.{v}.sec (s.snd ≫ smallUSig) s.fst s.condition ≫ eqToHom (by
    dsimp only [smallU_ext, U.ext, U.classifier, A, B]
    have : yonedaCategoryEquiv (s.snd ≫ smallUSig) =
        sigma (smallUPTpEquiv s.snd).fst (smallUPTpEquiv s.snd).snd := by
      rw [smallUSig_app_eq, Equiv.apply_symm_apply]
    rw [this]))
  ≫ lift' s

set_option pp.proofs true in
theorem fac_left (s : RepPullbackCone smallU.{v}.tp smallUSig.{v}) :
    lift s ≫ smallUPair.{v} = s.fst := by
  rw [smallUPair_app_eq, yonedaCategoryEquiv.symm_apply_eq]
  dsimp only [FunctorOperation.pair]
  have w := s.condition
  -- dsimp only [lift, lift']
  -- erw [← smallUPair_naturality]

  -- simp [lift]
  sorry

theorem fac_right (s : Limits.RepPullbackCone smallU.tp smallUSig) :
    lift s ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p = s.snd :=
  sorry

theorem lift_uniq (s : Limits.RepPullbackCone smallU.tp smallUSig) (m : y(s.pt) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp) :
    m ≫ smallUPair = s.fst → m ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p
    = s.snd → m = lift s :=
  sorry

end SigmaPullback

open SigmaPullback

theorem smallU_pb : IsPullback smallUPair.{v} (smallU.{v}.uvPolyTp.comp smallU.{v}.uvPolyTp).p
    smallU.{v}.tp smallUSig.{v, max u (v+1)} := (Limits.RepPullbackCone.is_pullback
      comm_sq lift fac_left fac_right lift_uniq)

def smallUSigma : NaturalModelSigma smallU.{v, max u (v+1)} where
  Sig := smallUSig
  pair := smallUPair
  Sig_pullback := smallU_pb

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma.{0, 4}
  | 1 => smallUSigma.{1, 4}
  | 2 => smallUSigma.{2, 4}
  | 3 => smallUSigma.{3, 4}
  | (n+4) => by omega

end GroupoidModel
end
