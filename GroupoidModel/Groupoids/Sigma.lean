import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModel
import GroupoidModel.RepPullbackCone
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

-- TODO (for JH) move to Grothendieck.Groupoidal.Basic (after refactor)
namespace CategoryTheory.Grothendieck.Groupoidal
variable {Γ : Type u₃}{Δ : Type u₃} [Groupoid.{v₃} Γ][Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

lemma hom_of_map_eq_eqToHom {F G : Γ ⥤ Grpd} (h : F = G) :
    eqToHom (by rw [h]) = Grpd.homOf (map (eqToHom h)) := by
  subst h
  fapply CategoryTheory.Functor.ext
  · intro x
    apply Grothendieck.Groupoidal.obj_ext_hEq
    · simp [Grpd.eqToHom_obj]
    · simp
  · intro x y f
    rw! [Grothendieck.Groupoidal.map_id_eq]
    simp

lemma pre_congr_functor {F G : Γ ⥤ Grpd} (h : F = G) :
  map (eqToHom (by rw[← h])) ⋙ pre F σ ⋙ map (eqToHom h) =
  pre G σ := by
  subst h
  simp only [eqToHom_refl, map_id_eq]
  exact rfl

end CategoryTheory.Grothendieck.Groupoidal

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
  simp only [sigmaMap, Functor.comp_obj, Functor.id_obj]
  apply obj_ext_hEq
  · simp
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
      simp only [Functor.comp_obj, whiskerRight_app, Functor.comp_map,
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
      whiskerRight_app, Functor.comp_map, heq_cast_iff_heq,
      heq_eqToHom_comp_iff, heq_eq_eq, map_obj_base]
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




theorem sigma_naturality_aux (x) :
    ι (σ ⋙ A) x ⋙ pre A σ ⋙ B = ι A (σ.obj x) ⋙ B := by
  rw [← ιCompPre σ A x]
  rfl

lemma whiskerRight_ιNatTrans_naturality {x y : Δ} (f : x ⟶ y) :
  whiskerRight (ιNatTrans f) (pre A σ ⋙ B)
= eqToHom (sigma_naturality_aux B σ x) ≫ whiskerRight (ιNatTrans (σ.map f)) B ≫
  eqToHom (by simp[Functor.assoc, sigma_naturality_aux B σ y]) := by
  simp[whiskerRight]
  congr
  funext X
  rw [NatTrans.comp_app]
  dsimp
  dsimp[ιNatTrans, Grothendieck.ιNatTrans, Grothendieck.Groupoidal.pre, Grothendieck.pre]
  aesop

theorem sigma_naturality_obj (x) :
    (σ ⋙ sigma A B).obj x =
    (sigma (σ ⋙ A) (pre A σ ⋙ B)).obj x := by
  dsimp only [Functor.comp_obj, sigma, sigmaObj]
  rw! [sigma_naturality_aux]

-- NOTE formerly called `sigmaBeckChevalley`
theorem sigma_naturality : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . apply sigma_naturality_obj
  . intros x y f
    rw [hom_of_map_eq_eqToHom (sigma_naturality_aux B σ y)]
    rw [hom_of_map_eq_eqToHom (sigma_naturality_aux B σ x).symm]
    dsimp [Grpd.homOf, sigmaMap, ← Functor.assoc]
    erw [← Grothendieck.Groupoidal.map_comp_eq]
    rw [whiskerRight_ιNatTrans_naturality]
    simp only [Functor.comp_obj, Functor.comp_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    erw [Grothendieck.Groupoidal.map_comp_eq]
    dsimp [Functor.assoc]
    have : pre (ι A (σ.obj y) ⋙ B) (A.map (σ.map f)) = map (eqToHom (by rw[← (sigma_naturality_aux B σ y)])) ⋙ pre (ι (σ ⋙ A) y ⋙ pre A σ ⋙ B) (A.map (σ.map f)) ⋙
        map (eqToHom (sigma_naturality_aux B σ y))  := by
            apply Eq.symm
            apply pre_congr_functor
    rw [this]

end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {α β : Γ ⥤ PGrpd.{v₁,u₁}}
  {B : ∫(α ⋙ forgetToGrpd) ⥤ Grpd.{v₁,u₁}}
  (h : β ⋙ forgetToGrpd = sec _ α rfl ⋙ B)

def pairSectionObjFiber (x : Γ) : (sigma (α ⋙ forgetToGrpd) B).obj x :=
  objMk (objPt α x) (objPt' h x)

@[simp] theorem pairSectionObjFiber_base (x : Γ) :
    (pairSectionObjFiber h x).base = objPt α x :=
  rfl

@[simp] theorem pairSectionObjFiber_fiber (x : Γ) :
    (pairSectionObjFiber h x).fiber = objPt' h x :=
  rfl

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

@[simp] def pairSectionObj_base (x : Γ) : (pairSectionObj h x).base = x :=
  rfl

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
  · simp [ι_map_fiber, mapPoint, Grpd.forgetToCat]
  · simp [ι_map_base]

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
  simp only [Functor.comp_obj, Functor.comp_map,
    mapPairSectionObjFiber, sigmaObj, sigmaMap,
    pre_obj_fiber, map_obj_fiber, whiskerRight_app,
    ← Grpd.map_comp_obj, pairSectionMap_aux_aux, pairSectionObjFiber_fiber]

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

@[simp] theorem pairSectionMap_base {x y} (f : x ⟶ y) :
    (pairSectionMap h f).base = f :=
  rfl

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
  (B.map ((ι _ z).map (mapPoint α (f ≫ g)))).obj
      ((sigmaMap B (f ≫ g)).obj (pairSectionObj h x).fiber).fiber =
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

@[simps] def pairSection : Γ ⥤ ∫(sigma (α ⋙ forgetToGrpd) B) where
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

section
variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

theorem objPt_naturality (α : Γ ⥤ PGrpd) (x : Δ) :
    objPt (σ ⋙ α) x = objPt α (σ.obj x) :=
  rfl

theorem objPt'_naturality {A : Γ ⥤ Grpd.{v₁,u₁}}
    {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A) (x : Δ) :
    @objPt' _ _ (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) x = objPt' h (σ.obj x) :=
  rfl

end

variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

include h in
lemma pairSection_naturality_aux : (σ ⋙ β) ⋙ forgetToGrpd
    = sec _ (σ ⋙ α) rfl ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B := by
  conv => right; erw [← Functor.assoc, ← sec_naturality]
  simp only [Functor.assoc, h]

lemma pairSection_naturality_obj (x) : (σ ⋙ pairSection h).obj x =
    (pairSection (pairSection_naturality_aux h σ)
    ⋙ map (eqToHom (sigma_naturality B σ).symm)
    ⋙ pre (sigma (α ⋙ forgetToGrpd) B) σ).obj x := by
  simp only [pairSection, Functor.comp_obj, pairSectionObj]
  apply obj_ext_hEq
  · simp [pairSection, pairSectionObj]
  · rw [heq_eq_eq]
    have : (ι ((σ ⋙ α) ⋙ forgetToGrpd) x ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B)
        ⋙ Grpd.forgetToCat =
        (ι (α ⋙ forgetToGrpd) (σ.obj x) ⋙ B) ⋙ Grpd.forgetToCat := by
      simp only [← ιCompPre, Functor.assoc]
    apply obj_ext_hEq
    · simp [Grpd.eqToHom_obj, Grothendieck.cast_eq this, objPt_naturality]
    · simp only [pairSectionObjFiber, Functor.comp_obj,
        objMk_base, objMk_fiber,
        objPt_naturality, pre_obj_fiber, map_obj_fiber, sigma_obj,
        sigmaObj, ← objPt'_naturality]
      rw! [eqToHom_app, Grpd.eqToHom_obj, Grothendieck.cast_eq this,
        objMk_fiber, heq_eq_eq]

theorem pairSection_naturality_map_base {x y} (f : x ⟶ y) :
    ((σ ⋙ pairSection h).map f).base =
    (eqToHom (pairSection_naturality_obj h σ x)
      ≫ (pairSection (pairSection_naturality_aux h σ)
        ⋙ map (eqToHom (sigma_naturality B σ).symm)
        ⋙ pre (sigma (α ⋙ forgetToGrpd) B) σ).map f
      ≫ eqToHom (pairSection_naturality_obj h σ y).symm).base
    := by
  simp

lemma eqToHom_eqToHom_base {A : Γ ⥤ Grpd} {x' x y y' : ∫(A)}
    (hx : x' = x) (hy : y = y') (f : x ⟶ y) :
    (eqToHom hx ≫ f ≫ eqToHom hy).base =
    eqToHom (by rw [hx]) ≫ f.base ≫ eqToHom (by rw [hy]) := by
  simp

variable {A : Γ ⥤ Grpd}{x' x y y' : ∫(A)}
    (hx : x' = x) (hy : y = y') (f : x ⟶ y)

#check (eqToHom hx ≫ f ≫ eqToHom hy).fiber
#check (A.map f.base ≫ (A.map (eqToHom hy).base)).map (eqToHom hx).fiber
#check (eqToHom hy).fiber
#check (A.map (eqToHom hy).base).map f.fiber

-- lemma eqToHom_eqToHom_fiber_aux {A : Γ ⥤ Grpd} {x' x y y' : ∫(A)}
--     (hx : x' = x) (hy : y = y') (f : x ⟶ y) :
--     ((A ⋙ Grpd.forgetToCat).map (eqToHom hx ≫ f ≫ eqToHom hy).base).obj x'.fiber =
--     (A.map f.base ≫ A.map (eqToHom hy).base).obj (((A ⋙ Grpd.forgetToCat).map (eqToHom hx).base).obj x'.fiber) := by
--   simp [eqToHom_eqToHom_base, Grpd.forgetToCat]

lemma eqToHom_eqToHom_fiber {A : Γ ⥤ Grpd} {x' x y y' : ∫(A)}
    {hx : x' = x} {hy : y = y'} (f : x ⟶ y) :
    (eqToHom hx ≫ f ≫ eqToHom hy).fiber =
    eqToHom (by simp [eqToHom_eqToHom_base, Grpd.forgetToCat]) ≫ (A.map f.base ≫ (A.map (eqToHom hy).base)).map (eqToHom hx).fiber
    ≫ (A.map (eqToHom hy).base).map f.fiber ≫ (eqToHom hy).fiber := by
  simp



theorem eqToHom_base_map {C D : Type*} [Category C] [Category D] {A}
    (F : C ⥤ D) {X Y : Grothendieck A} (p : X = Y) :
    F.map (eqToHom p).base = eqToHom (congr_arg F.obj (by rw [p])) :=
  by simp [eqToHom_map]



set_option maxHeartbeats 0 in


set_option trace.profiler true in
set_option trace.profiler.threshold 3000 in
theorem pairSection_naturality_map_fiber {x y} (f : x ⟶ y) :
    eqToHom (by rw [pairSection_naturality_map_base])
    ≫ ((σ ⋙ pairSection h).map f).fiber =
    (eqToHom (pairSection_naturality_obj h σ x)
      ≫ (pairSection (pairSection_naturality_aux h σ)
        ⋙ map (eqToHom (sigma_naturality B σ).symm)
        ⋙ pre (sigma (α ⋙ forgetToGrpd) B) σ).map f
      ≫ eqToHom (pairSection_naturality_obj h σ y).symm).fiber := by

      simp only [comp_fiber, eqToHom_map, eqToHom_fiber, eqToHom_comp_iff, eqToHom_trans_assoc]
      rw! [eqToHom_base_map]
      dsimp only [Functor.comp_map, pairSection_map]
      fapply Grothendieck.Groupoidal.ext
      ·
        -- simp only [pairSectionMap_fiber_base, eqToHom_refl, Grpd.id_eq_id, pre_map_fiber]
        -- simp only [map_map_fiber, Functor.id_map, Category.assoc, eqToHom_trans_assoc, pairSection_obj]
        -- rw [eqToHom_eqToHom_base]
        -- simp [pairSectionObj, pairSectionMap, pairSectionMapFiber, mapPoint']
        -- rw! [eqToHom_app (Eq.symm (sigma_naturality B σ)) y]
        sorry
      ·
        -- simp only[ pairSectionMap, pairSectionMapFiber, pairSectionObjFiber_base, eqToHom_refl,
        -- Grpd.id_eq_id, pre_map_fiber, Functor.id_map, homMk_fiber, eqToHom_trans_assoc]
        -- the above simp only comes from: simp [pairSectionMap_fiber_fiber, eqToHom_trans_assoc, pre_map_fiber, map_map_fiber,pairSectionMap, homMk_fiber, pairSectionMapFiber]
        -- doesnt work but looks useful: simp [eqToHom_eqToHom_fiber, map_map_fiber]
        sorry

-- TODO consider changing this statement. Namely the `map (eqToHom ⋯)` part.
theorem pairSection_naturality : σ ⋙ pairSection h =
    pairSection (pairSection_naturality_aux h σ)
    ⋙ map (eqToHom (sigma_naturality B σ).symm) ⋙ pre _ _ := by
  fapply CategoryTheory.Functor.ext
  · apply pairSection_naturality_obj
  · intros X Y f
    fapply Grothendieck.Groupoidal.ext
    . apply pairSection_naturality_map_base
    . apply pairSection_naturality_map_fiber

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
    apply obj_ext_hEq
    · simp
    · simp
  · intro p q h
    simp only [heq_eq_eq]
    apply Grothendieck.Groupoidal.ext
    -- TODO improve API for these two goals
    · simp [ι_map_fiber, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso, Grpd.forgetToCat]
    · simp [ι_map_base, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso]

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
  yonedaCategoryEquiv.symm (pair (smallUUvPolyTpCompDomEquiv ab).2.2.2)

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
    yonedaCategoryEquiv.symm (pair (smallUUvPolyTpCompDomEquiv ab).2.2.2) := by
  simp only [smallUPair, smallUPair_app, NatTrans.yonedaMk_app]

namespace SigmaPullback

open Limits

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
  · rw [smallUUvPolyTpCompDomEquiv_apply_fst]
  · sorry

variable (s : RepPullbackCone smallU.{v}.tp smallUSig.{v})

abbrev A := (smallUPTpEquiv s.snd).fst

abbrev B := (smallUPTpEquiv s.snd).snd

def lift' : y(Ctx.ofGrpd.obj $ Grpd.of ∫(sigma (A s) (B s))) ⟶
    smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp :=
  smallUUvPolyTpCompDomEquiv.symm
    ⟨ fst (B s), dependent (B s), snd (B s), snd_forgetToGrpd _ ⟩

def lift : y(s.pt) ⟶ smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp :=
  ym(smallU.{v}.sec (s.snd ≫ smallUSig) s.fst s.condition ≫ eqToHom (by
    dsimp only [smallU_ext, U.ext, U.classifier, A, B]
    have : yonedaCategoryEquiv (s.snd ≫ smallUSig) =
        sigma (smallUPTpEquiv s.snd).fst (smallUPTpEquiv s.snd).snd := by
      rw [smallUSig_app_eq, Equiv.apply_symm_apply]
    rw [this]))
  ≫ lift' s

theorem fac_left (s : RepPullbackCone smallU.{v}.tp smallUSig.{v}) :
    lift s ≫ smallUPair.{v} = s.fst := by
  simp [lift]
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
