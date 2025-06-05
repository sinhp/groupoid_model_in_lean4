import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

-- section

-- variable {C : Type u} [Category.{v} C]
-- variable {F : C ⥤ Grpd.{v₂, u₂}}

-- JH: It is still unclear to me weather the following lemmas will be useful
-- so far I have had difficulty with applying them or
-- found them to be no better than equivalents.

-- lemma Grpd.eqToHom_obj_heq {G H : Grpd} (h : G = H) (x : G) :
--     HEq ((eqToHom h).obj x) x := by
--   simp [Grpd.eqToHom_obj]

-- @[simp] lemma Grpd.eqToHom_obj_heq_iff {G H : Grpd} (h : G = H) (x y : G) :
--     HEq ((eqToHom h).obj x) y ↔ HEq x y := by
--   constructor
--   · apply (Grpd.eqToHom_obj_heq h _).symm.trans
--   · apply (Grpd.eqToHom_obj_heq h _).trans

-- lemma Grpd.eqToHom_map_heq {G H : Grpd} (h : G = H) {x y : G} (f : x ⟶ y) :
--     HEq ((eqToHom h).map f) f := by
--   simp [Grpd.eqToHom_hom]

-- @[simp] lemma Grpd.eqToHom_map_heq_iff {G H : Grpd} (h : G = H) {x y z w : G} (f : x ⟶ y) (g : z ⟶ w) :
--     HEq ((eqToHom h).map f) g ↔ HEq f g := by
--   constructor
--   · apply (Grpd.eqToHom_map_heq h f).symm.trans
--   · apply (Grpd.eqToHom_map_heq h f).trans

-- theorem Grothendieck.Groupoidal.hext {X Y : ∫(F)} (f g : X ⟶ Y) (w_base : f.base = g.base)
--     (w_fiber : HEq f.fiber g.fiber) : f = g :=
--   Grothendieck.hext f g w_base w_fiber

-- end

end ForOther

-- NOTE these simp lemmas from mathlib should maybe be removed
-- Grpd.forgetToCat...?
-- Some `AsSmall` related lemmas

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal PGrpd

attribute [local simp] eqToHom_map

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

@[simp] theorem sigmaMap_obj_base (a) :
    ((sigmaMap B f).obj a).base = (A.map f).obj a.base :=
  rfl

@[simp] theorem sigmaMap_obj_fiber (a) :
    ((sigmaMap B f).obj a).fiber = (B.map ((ιNatTrans f).app (base a))).obj (fiber a) := by
  rfl

@[simp] theorem sigmaMap_map_base {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).base = (A.map f).map p.base := rfl

theorem sigmaMap_map_fiber_aux {a b : sigmaObj B x} {p : a ⟶ b} :
    (((ι A y ⋙ B)).map ((sigmaMap B f).map p).base).obj ((sigmaMap B f).obj a).fiber =
    (B.map ((ιNatTrans f).app (base b))).obj (((ι A x ⋙ B).map p.base).obj a.fiber) := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map, pre_map_base, map_map_base,
    pre_obj_fiber, map_obj_fiber, whiskerRight_app]
  simp only [← Functor.comp_obj, ← Grpd.comp_eq_comp, ← Functor.map_comp]
  congr 3
  exact ((ιNatTrans f).naturality p.base).symm

@[simp] theorem sigmaMap_map_fiber {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).fiber =
    eqToHom (sigmaMap_map_fiber_aux B f) ≫ (B.map ((ιNatTrans f).app (base b))).map p.fiber := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map, pre_map_base, map_map_base,
    pre_map_fiber, map_map_fiber, whiskerRight_twice, whiskerRight_app, Cat.comp_obj]

variable {B}

@[simp] theorem sigmaMap_id_obj {p} : (sigmaMap B (𝟙 x)).obj p = p := by
  apply obj_hext
  · simp [sigmaMap]
  · simp [sigmaMap, Grpd.eqToHom_obj]

@[simp] theorem sigmaMap_id_map {p1 p2} {hp2 : p2 = (sigmaMap B (𝟙 x)).obj p2}
    (f : p1 ⟶ p2) :
    (sigmaMap B (𝟙 x)).map f =
    eqToHom (by simp) ≫ f ≫ eqToHom (by simp) := by
  have h (a : A.obj x) : B.map ((ιNatTrans (𝟙 x)).app a) =
      eqToHom (by simp [Functor.map_id]) :=
    calc
      B.map ((ιNatTrans (𝟙 x)).app a)
      _ = B.map (eqToHom (by simp [Functor.map_id])) := by
        rw [ιNatTrans_id_app]
      _ = eqToHom (by simp [Functor.map_id]) := by
        simp
  have h1 : B.map ((ι A x).map (eqToHom hp2).base) = eqToHom (by simp) := by
    simp [eqToHom_base]
  fapply Grothendieck.Groupoidal.ext
  · simp [sigmaMap]
  · simp [sigmaMap_map_fiber, Functor.congr_hom (h p2.base) f.fiber, eqToHom_base,
      Functor.congr_hom h1]

theorem sigmaMap_id : sigmaMap B (𝟙 x) = 𝟭 _ := by
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp
    · intro p
      simp

variable {z : Γ} {f} {g : y ⟶ z}

@[simp] theorem sigmaMap_comp_obj {p} : (sigmaMap B (f ≫ g)).obj p =
    (sigmaMap B g).obj ((sigmaMap B f).obj p) := by
  dsimp only [sigmaMap]
  apply obj_hext
  · simp
  · simp only [sigmaObj, Functor.comp_obj, pre_obj_base, map_obj_base, pre_obj_fiber,
      map_obj_fiber, whiskerRight_app, ιNatTrans_comp_app, Functor.map_comp, eqToHom_map,
      Grpd.comp_eq_comp]
    rw [Grpd.eqToHom_obj]
    simp


@[simp] theorem sigmaMap_comp_map {A : Γ ⥤ Grpd.{v₁,u₁}}
    {B : ∫(A) ⥤ Grpd.{v₁,u₁}} {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z}
    {p q : sigmaObj B x} (hpq : p ⟶ q)
    {h1 : (sigmaMap B (f ≫ g)).obj p = (sigmaMap B g).obj ((sigmaMap B f).obj p)}
    {h2 : (sigmaMap B g).obj ((sigmaMap B f).obj q) = (sigmaMap B (f ≫ g)).obj q}
    : (sigmaMap B (f ≫ g)).map hpq =
    eqToHom h1 ≫ (sigmaMap B g).map ((sigmaMap B f).map hpq) ≫ eqToHom h2 := by
  have h : B.map ((ιNatTrans (f ≫ g)).app q.base) =
    B.map ((ιNatTrans f).app q.base)
    ≫ B.map ((ιNatTrans g).app ((A.map f).obj q.base))
    ≫ eqToHom (by simp) := by simp
  -- dsimp only [sigmaMap]
  fapply Grothendieck.Groupoidal.hext
  · simp only [sigmaObj, sigmaMap_map_base, Grpd.map_comp_map, comp_base, eqToHom_base]
  · have h3 : (ι A z ⋙ B).map (eqToHom h2).base
        = eqToHom (by simp only [sigmaMap, Functor.comp_obj]; congr 3) := by
      rw [eqToHom_base, eqToHom_map]
    simp only [sigmaObj, Functor.comp_obj, sigmaMap_map_base, Functor.comp_map, sigmaMap_map_fiber,
      sigmaMap_obj_fiber, Functor.congr_hom h, Grpd.comp_eq_comp, eqToHom_trans_assoc, comp_base,
      Grothendieck.Groupoidal.comp_fiber, Grothendieck.Groupoidal.eqToHom_fiber, sigmaMap_obj_base,
      eqToHom_map, Functor.map_comp, Category.assoc, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rw! [Functor.congr_hom h3]
    simp only [sigmaObj, Functor.comp_obj, Functor.comp_map, id_eq, heq_eqToHom_comp_iff,
      heq_comp_eqToHom_iff, heq_eq_eq]

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

variable (B) {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)
theorem sigma_naturality_aux (x) :
    ι (σ ⋙ A) x ⋙ pre A σ ⋙ B = ι A (σ.obj x) ⋙ B := by
  rw [← ι_pre σ A x]
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
    rw [eqToHom_eq_homOf_map (sigma_naturality_aux B σ y)]
    rw [eqToHom_eq_homOf_map (sigma_naturality_aux B σ x).symm]
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

def pairObjFiber (x : Γ) : sigmaObj B x :=
  objMk (objFiber α x) (objFiber' h x)

@[simp] theorem pairObjFiber_base (x : Γ) : (pairObjFiber h x).base = objFiber α x :=
  rfl

@[simp] theorem pairObjFiber_fiber (x : Γ) :
    (pairObjFiber h x).fiber = (objFiber' h x) :=
  rfl

theorem pairSectionMap_aux_aux {x y} (f : x ⟶ y) :
    (ιNatTrans f).app (pairObjFiber h x).base
    ≫ (ι _ y).map (mapFiber α f)
    = (sec _ α rfl).map f := by
  apply Grothendieck.Groupoidal.ext
  · simp only [Grothendieck.forget_obj,
      Grothendieck.Groupoidal.comp_fiber, ιNatTrans_app_fiber, ι_obj_fiber, ι_map_fiber,
      eqToHom_trans_assoc, sec_map_fiber, mapFiber', mapFiber]
    rw! [CategoryTheory.Functor.map_id]
    simp only [Grothendieck.id_base, Grpd.id_eq_id, Functor.id_obj, eqToHom_refl, Functor.id_map,
      Category.id_comp, objFiber'_rfl]
    apply Category.id_comp
  · simp

/--
  The left hand side
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
theorem pairMapFiber_aux {x y} (f : x ⟶ y) :
    ((ι _ y ⋙ B).map (mapFiber α f)).obj ((sigmaMap B f).obj (pairObjFiber h x)).fiber =
    ((sec _ α rfl ⋙ B).map f).obj (objFiber' h x) := by
  simp only [Grpd.forgetToCat.eq_1, Functor.comp_obj, Grothendieck.forget_obj, Functor.comp_map,
    sigmaObj, sigmaMap, Grothendieck.forget_map, pre_obj_fiber, map_obj_fiber, whiskerRight_app]
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
def pairMapFiber {x y : Γ} (f : x ⟶ y) : (sigmaMap B f).obj (pairObjFiber h x)
    ⟶ (pairObjFiber h y : ∫(ι _ y ⋙ B)) :=
  homMk (mapFiber α f) (eqToHom (pairMapFiber_aux h f) ≫ mapFiber' h f)

@[simp↓] theorem pairMapFiber_base {x y} (f : x ⟶ y) :
    (pairMapFiber h f).base = mapFiber α f :=
  rfl

/-
1. The first implicit argument to `Groupoidal.Hom.fiber` is `(α ⋙ forgetToGrpd).obj y`.
   The global `simp` rule `Functor.comp_obj` (which normally fires before this)
   rewrites that to `forgetToGrpd.obj (α.obj x)`,
   and then this lemma no longer applies.
   As a workaround, we instruct `simp` to apply this before visiting subterms.

2. `@[simps! fiber]` on `pairMapFiber` generates a lemma
  that refers to `Grothendieck.Hom.fiber` rather than `Groupoidal.Hom.fiber`,
  so we write this by hand. -/
@[simp↓] theorem pairMapFiber_fiber {x y} (f : x ⟶ y) :
    (pairMapFiber h f).fiber = eqToHom (pairMapFiber_aux h f) ≫ mapFiber' h f :=
  rfl

theorem pairMapFiber_id (x : Γ) : pairMapFiber h (𝟙 x) = eqToHom (by simp) := by
  apply Grothendieck.Groupoidal.ext <;> simp

theorem pairMapFiber_comp_aux_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (mapFiber α g)).obj
    (((ι _ z ⋙ B ⋙ Grpd.forgetToCat).map
    (((sigmaMap B g).map (pairMapFiber h f))).base).obj
    ((sigmaMap B g).obj (((sigmaMap B f).obj (pairObjFiber h x)))).fiber)
    = ((sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g).obj (objFiber' h x) := by
  have h1 : (sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g = (sec _ α rfl ⋙ B).map (f ≫ g) := by
    rw [← Functor.map_comp]
  rw [Functor.congr_obj h1, ← pairMapFiber_aux,mapFiber_comp,
    Functor.map_comp, eqToHom_map, Grpd.comp_eq_comp]
  simp only [Functor.comp_obj, Functor.map_comp, Grpd.eqToHom_obj]
  congr 2
  have : (sigmaMap B g).obj ((sigmaMap B f).obj (pairObjFiber h x))
    = (sigmaMap B (f ≫ g)).obj (pairObjFiber h x) := by
    rw [sigmaMap_comp]
    rfl
  rw [eq_cast_iff_heq]
  congr

theorem pairMapFiber_comp_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (mapFiber α g)).map ((sigmaMap B g).map (pairMapFiber h f)).fiber
    = eqToHom (pairMapFiber_comp_aux_aux h f g)
    ≫ ((sec _ α rfl ⋙ B).map g).map (mapFiber' h f)
    ≫ eqToHom (by rw [← pairMapFiber_aux]) := by
  simp only [Functor.comp_map, sigmaObj, sigmaMap_map_fiber, whiskerRight_app,
    pre_map_fiber, map_map_fiber, Functor.map_comp,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    Grpd.map_comp_map', eqToHom_trans_assoc, eqToHom_comp_iff, comp_eqToHom_iff,
    eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
  rw! [pairSectionMap_aux_aux]
  simp only [pairMapFiber_fiber, Functor.map_comp, eqToHom_refl, Category.comp_id, eqToHom_map]

-- NOTE an improvement from 27 seconds to just 9 seconds (with pretty much the same proof)!
theorem pairMapFiber_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    (pairMapFiber h (f ≫ g)) = eqToHom (by simp)
    ≫ (((sigma (α ⋙ forgetToGrpd) B).map g).map (pairMapFiber h f) ≫ pairMapFiber h g) := by
  fapply Grothendieck.Groupoidal.ext
  · simp [- Functor.comp_obj, mapFiber] -- FIXME
  · rw! [pairMapFiber_fiber, Grothendieck.Groupoidal.comp_fiber, Grothendieck.Groupoidal.comp_fiber,
      Grothendieck.Groupoidal.eqToHom_fiber, eqToHom_map, pairMapFiber_comp_aux,
      Functor.congr_hom (Functor.congr_hom h.symm g) (mapFiber' h f), mapFiber'_comp]
    simp only [pairMapFiber_fiber, mapFiber', eqToHom_trans_assoc, Category.assoc,
      eqToHom_comp_iff]
    simp only [← Category.assoc]
    congr 1
    simp only [Grothendieck.forget_obj, Grpd.coe_of, Grpd.eqToHom_hom, pairObjFiber_base,
      Functor.comp_map, Grothendieck.forget_map, Grpd.comp_eq_comp, Category.assoc]
    conv => right; right; simp only [← congrArg_cast_hom_left, cast_cast]
    rw [conj_eqToHom_iff_heq]
    · simp only [heq_cast_iff_heq, cast_heq_iff_heq]
      congr 1
      · erw [Functor.congr_obj (Functor.congr_hom h.symm f) (objFiber' h x)]
        simp only [Grpd.forgetToCat, id_eq, Functor.comp_obj, Functor.comp_map,
          Grothendieck.forget_map, Grpd.comp_eq_comp, objFiber', objFiber,
          Grpd.eqToHom_obj, cast_cast, cast_eq]
      · simp only [objFiber', Functor.comp_obj, Grothendieck.forget_obj, objFiber,
          Grpd.eqToHom_obj, cast_cast, cast_eq]
      · simp only [heq_cast_iff_heq, heq_eq_eq]
    · simp only [Grpd.eqToHom_obj, Grpd.coe_of, objFiber', Functor.comp_obj,
      Grothendieck.forget_obj, objFiber, cast_cast, cast_eq]

variable (α) (β) (B) in
def pair : Γ ⥤ PGrpd.{v₁,u₁} :=
  PGrpd.functorTo (sigma _ B) (pairObjFiber h) (pairMapFiber h)
  (pairMapFiber_id h) (pairMapFiber_comp h)

@[simp] theorem pair_obj_base (x : Γ) :
    ((pair α β B h).obj x).base = ∫(ι (α ⋙ forgetToGrpd) x ⋙ B) :=
  rfl

@[simp] theorem pair_obj_fiber (x : Γ) :
    ((pair α β B h).obj x).fiber = pairObjFiber h x :=
  rfl

@[simp] theorem pair_map_base {x y : Γ} (f : x ⟶ y) :
    ((pair α β B h).map f).base = sigmaMap B f :=
  rfl

@[simp] theorem pair_map_fiber {x y : Γ} (f : x ⟶ y) :
    ((pair α β B h).map f).fiber = pairMapFiber h f :=
  rfl

@[simp] theorem pair_comp_forgetToGrpd :
    pair α β B h ⋙ forgetToGrpd = sigma (α ⋙ forgetToGrpd) B := rfl

section

variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

-- JH: TODO move?
-- TODO consider removal, unused after refactor
-- theorem map_eqToHom_toPGrpd {F G : Γ ⥤ Grpd} (h : F = G) :
--     map (eqToHom h) ⋙ toPGrpd G = toPGrpd F := by
--   subst h
--   simp [map_id_eq, Functor.id_comp]

include h in
theorem pair_naturality_aux : (σ ⋙ β) ⋙ forgetToGrpd =
  sec ((σ ⋙ α) ⋙ forgetToGrpd) (σ ⋙ α) rfl ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B := by
  rw [Functor.assoc, h, ← Functor.assoc, sec_naturality]
  rfl

theorem pair_naturality_ι_pre (x) :
    (ι ((σ ⋙ α) ⋙ forgetToGrpd) x ⋙ pre (α ⋙ forgetToGrpd) σ)
    = ι (α ⋙ forgetToGrpd) (σ.obj x) := by
  apply ι_pre σ (α ⋙ forgetToGrpd) x

theorem pair_naturality_obj (x : Δ) : HEq (pairObjFiber h (σ.obj x))
    (pairObjFiber (pair_naturality_aux h σ) x) := by
  apply obj_hext'
  · rw [← Functor.assoc, pair_naturality_ι_pre]
  · simp only [Grpd.forgetToCat, Functor.comp_obj, Grothendieck.forget_obj, pair_obj_fiber,
      id_eq, eq_mpr_eq_cast, cast_eq, heq_eq_eq]
    erw [pairObjFiber_base]
  · simp
    erw [pairObjFiber_fiber]

theorem pair_naturality_aux_1 {x y} (f : x ⟶ y) :
    HEq ((sigmaMap B (σ.map f)).obj (pairObjFiber h (σ.obj x)))
    ((sigmaMap (pre (α ⋙ forgetToGrpd) σ ⋙ B) f).obj (pairObjFiber (pair_naturality_aux h σ) x)) :=
  sorry

theorem pair_naturality : σ ⋙ pair α β B h = pair (σ ⋙ α) (σ ⋙ β) (pre (α ⋙ forgetToGrpd) σ ⋙ B)
    (by erw [Functor.assoc, h, ← Functor.assoc, sec_naturality, Functor.assoc]) := by
  apply PGrpd.Functor.hext
  · apply sigma_naturality
  · intro x
    apply pair_naturality_obj
  · intro x y f
    apply hext'
    · rw [← Functor.assoc, pair_naturality_ι_pre]
    · apply pair_naturality_aux_1
    · apply pair_naturality_obj
    · simp [- Functor.comp_obj, - Functor.comp_map, Functor.comp_map, mapFiber_naturality]
    · simp [- Functor.comp_obj, - Functor.comp_map, Functor.comp_map, ← mapFiber'_naturality]

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

theorem fst_forgetToGrpd : fst B ⋙ forgetToGrpd = forget ⋙ A := by
  dsimp only [fst, fst']
  rw [Functor.assoc, (Grothendieck.Groupoidal.isPullback A).comm_sq,
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

-- TODO follow the advice of improving API for those two goals
theorem assoc_forget : assoc B ⋙ forget = fst' B := by
  dsimp [assoc, fst']
  fapply CategoryTheory.Functor.ext
  · intro p
    apply Grothendieck.Groupoidal.obj_hext
    · simp
      sorry
    · simp [base]
      sorry
  · intro p q h
    apply Grothendieck.Groupoidal.ext
    · simp [eqToHom_map, assocHom, assocIso, preNatIso, Grothendieck.preNatIso, ιNatIso, Functor.map_id]
      sorry
    · sorry
    -- apply Grothendieck.Groupoidal.ext
    -- -- TODO improve API for these two goals
    -- · simp [ι_map, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso, Grpd.forgetToCat]
    -- · simp [ι_map, assocHom, assocIso, preNatIso, ιNatIso, Grothendieck.preNatIso]

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
  yonedaCategoryEquiv.symm (pair _ _ _ (smallUCompDomEquiv ab).2.2.2)

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
    yonedaCategoryEquiv.symm (pair _ _ _ (smallUCompDomEquiv ab).2.2.2) := by
  simp only [smallUPair, smallUPair_app, NatTrans.yonedaMk_app]

namespace SigmaPullback

open Limits

section

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

-- -- JH: this seems kind of bad to me. See `comm_sq`
-- theorem lift_heq_id_comp {Γ C : Type*} [Category Γ] [Category C]
--     {A B : Γ ⥤ Grpd.{v,v}}
--     (h : A = B) (F : ∫(A) ⥤ C) : HEq ((lift (toPGrpd B)) forget
--     (h ▸ comm_sq A : toPGrpd B ⋙ forgetToGrpd = forget ⋙ A) ⋙ F)
--     (Functor.id ∫(A) ⋙ F) := by
--   subst h
--   apply heq_of_eq
--   congr 1
--   symm
--   apply lift_uniq
--   · rfl
--   · rfl
-- end

-- lemma comm_sq_aux {Γ : Ctx} (ab : y(Γ) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp)
--     : sigma ((smallUCompDomEquiv ab).fst ⋙ forgetToGrpd)
--     (smallUCompDomEquiv ab).snd.fst =
--     sigma (smallUPTpEquiv (ab ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p)).fst
--     (smallUPTpEquiv (ab ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p)).snd := by
--   congr 1
--   · rw [smallUCompDomEquiv_apply_fst_forgetToGrpd]
--   · rw [smallUCompDomEquiv_apply_snd_fst ab]
--     apply lift_heq_id_comp
--     · rw [smallUCompDomEquiv_apply_fst_forgetToGrpd]

-- /-
--   For the natural model `smallU`, a map `ab : y(Γ) ⟶ compDom tp`
--   is equivalent to the data of `(α,B,β,h)` due to `smallUCompDomEquiv`
--   ```
--   (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
--     × (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v,v})
--     × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{v,v})
--     ×' (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec _ α rfl ⋙ B)
--   ```
--   The following lemma computes the base type
--   `α ⋙ forgetToGrpd : y(Γ) ⟶ Grpd` in two different ways.
--   LHS is via `smallUPTpEquiv`, the universal property of `P_tp Ty`.
--   RHS is via `smallUCompDomEquiv`
-- -/
-- theorem app_fst_comp_forgetToGrpd_eq (Γ : Ctx) (ab : y(Γ) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp) :
--     (smallUCompDomEquiv ab).fst ⋙ forgetToGrpd
--     = (smallUPTpEquiv (ab ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p)).fst := by
--   apply smallUCompDomEquiv_apply_fst_forgetToGrpd

theorem smallUCompDomEquiv_apply_snd_fst {Γ : Ctx} (ab : y(Γ) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp) :
    HEq (smallUCompDomEquiv ab).snd.fst
      (smallUPTpEquiv (ab ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p)).snd := sorry

set_option maxHeartbeats 0 in
theorem smallUComp_apply {Γ : Ctx} (ab : y(Γ) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp) :
    ab ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p
    = smallUPTpEquiv.symm ⟨(smallUCompDomEquiv ab).1 ⋙ forgetToGrpd,
      (smallUCompDomEquiv ab).2.1 ⟩ := by
  rw [← smallUPTpEquiv.apply_eq_iff_eq_symm_apply]
  ext
  · exact (smallUCompDomEquiv_apply_fst_forgetToGrpd ab).symm
  · simp only []
    dsimp only [smallUPTpEquiv, Equiv.trans_apply, smallUCompDomEquiv]
    conv => left; rw [Equiv.sigmaCongr_apply_snd]
    conv => right; rw [Equiv.sigmaCongr_apply_snd]
    -- rw [uvPolyTpCompDomEquiv_apply_snd_fst]
    -- rw [(yonedaCategoryEquiv_naturality_left' _)]
--   rw [smallU_lift]
--   simp only [Ctx.equivalence_inverse, Ctx.equivalence_functor,
--     AsSmall.down_obj, AsSmall.up_obj_down, Functor.FullyFaithful.preimage_map,
--     AsSmall.down_map, AsSmall.up_map_down]
--   rw! [smallU_var]
--   rfl

    sorry-- exact (smallUCompDomEquiv_apply_snd_fst ab).symm

set_option maxHeartbeats 0 in
theorem comm_sq : smallUPair.{v} ≫ smallU.{v}.tp =
    (smallU.{v}.uvPolyTp.comp smallU.{v}.uvPolyTp).p ≫ smallUSig := by
  apply hom_ext_yoneda
  intros Γ ab
  rw [← Category.assoc, ← Category.assoc, smallUPair_app_eq,
    smallUSig_app_eq, smallU_tp,
    ← yonedaCategoryEquiv_symm_naturality_right,
    pair_comp_forgetToGrpd]
  congr 1
  congr 1
  · exact smallUCompDomEquiv_apply_fst_forgetToGrpd ab
  -- sorry-- rw [comm_sq_aux]
  · sorry
    -- exact smallUCompDomEquiv_apply_snd_fst ab
    -- sorry-- rw [comm_sq_aux]

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

theorem fac_right (s : Limits.RepPullbackCone smallU.tp smallUSig) :
    lift s ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p = s.snd := by
  -- have h := UvPoly.compDomEquiv_symm_comp_p s.snd
  -- apply smallUPTpEquiv.apply_eq_iff_eq.mp
  -- ext
  -- · rw [smallUPTpEquiv]
  --   sorry
  -- · sorry
  sorry

theorem fac_left_aux_0 : yonedaCategoryEquiv s.fst ⋙ forgetToGrpd =
    FunctorOperation.pair _ _ _ (smallUCompDomEquiv (lift s)).snd.snd.snd ⋙ forgetToGrpd := sorry


-- set_option maxHeartbeats 0 in
-- set_option trace.profiler true in
-- set_option trace.profiler.threshold 500 in
-- theorem fac_left_aux (x : Ctx.toGrpd.obj s.pt) :
--     (sec (pair (smallUCompDomEquiv.{v, max (u+1)} (lift s)).snd.snd.snd ⋙ forgetToGrpd)
--     (pair (smallUCompDomEquiv.{v, max (u+1)} (lift s)).snd.snd.snd) rfl).obj
--     x =
--     (Grothendieck.Groupoidal.sec (FunctorOperation.pair
--     (smallUCompDomEquiv (lift s)).snd.snd.snd ⋙ forgetToGrpd)
--     (yonedaCategoryEquiv s.fst) (fac_left_aux_0 s)).obj
--     x := by
  -- apply Grothendieck.Groupoidal.obj_ext_hEq
  -- · exact (sec_obj_base ..).trans (sec_obj_base ..).symm
  -- · apply heq_of_eq_of_heq (sec_obj_fiber
  --     (FunctorOperation.pair (smallUCompDomEquiv (lift s)).snd.snd.snd ⋙ forgetToGrpd)
  --     (FunctorOperation.pair (smallUCompDomEquiv (lift s)).snd.snd.snd) rfl x)
  --   apply heq_of_heq_of_eq _ (sec_obj_fiber
  --           (FunctorOperation.pair (smallUCompDomEquiv (lift s)).snd.snd.snd ⋙ forgetToGrpd)
  --           (yonedaCategoryEquiv s.fst) (fac_left_aux_0 s) x).symm
  --   simp only [objPt', objPt, Grpd.eqToHom_obj, cast_heq_iff_heq, heq_cast_iff_heq]

    -- unfold PointedGroupoid.pt
    -- -- rw! (castMode := .all) [fac_left_aux_0 s]
    -- -- rw! (castMode := .all) [fac_left_aux_0 s]
    -- -- apply heq_of_eq
    -- -- -- simp
    -- -- congr 1
    -- -- · rw [fac_left_aux_0 s]
    -- -- --rw [Functor.congr_obj (fac_left_aux_0 s) x]
    -- -- · rw! (castMode := .all) [fac_left_aux_0 s]
    -- --  -- rw! [Functor.congr_obj (fac_left_aux_0 s) x]
    -- sorry -- rfl

-- theorem fac_left_aux_1 (x : Ctx.toGrpd.obj s.pt) :
--     (FunctorOperation.pair (smallUCompDomEquiv (lift s)).snd.snd.snd).obj x =
--     (yonedaCategoryEquiv s.fst).obj x := by
--   simp only [FunctorOperation.pair, pairSection, Functor.comp_obj, toPGrpd]
--   -- congr 1
--   -- · sorry
--   -- · sorry
--   sorry

set_option pp.proofs true in
set_option maxHeartbeats 0 in
theorem fac_left (s : RepPullbackCone smallU.{v}.tp smallUSig.{v}) :
    lift s ≫ smallUPair.{v} = s.fst := by
  rw [smallUPair_app_eq, yonedaCategoryEquiv.symm_apply_eq]
  apply PGrpd.Functor.hext
  · exact (fac_left_aux_0 s).symm
  · intro x
    sorry
  · intro x y f
    sorry
  -- · apply CategoryTheory.Functor.ext
    -- · sorry
    -- · intro x
    --   apply Grothendieck.Groupoidal.obj_ext_hEq
    --   · rw [sec_obj_base, sec_obj_base]
    --   · rw [sec_obj_fiber, sec_obj_fiber]
    --     -- unfold objPt'
    --     -- simp [objPt']
    --     sorry

theorem lift_uniq (s : Limits.RepPullbackCone smallU.tp smallUSig) (m : y(s.pt) ⟶ smallU.uvPolyTp.compDom smallU.uvPolyTp) :
    m ≫ smallUPair = s.fst → m ≫ (smallU.uvPolyTp.comp smallU.uvPolyTp).p
    = s.snd → m = lift s :=
  sorry

end

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
