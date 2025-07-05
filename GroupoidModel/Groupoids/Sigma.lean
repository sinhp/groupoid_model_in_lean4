import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

-- NOTE these simp lemmas from mathlib should maybe be removed
-- Grpd.forgetToCat...?
-- Some `AsSmall` related lemmas

namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal PGrpd

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp

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
  map (Functor.whiskerRight (ιNatTrans f) B) ⋙ pre (ι A y ⋙ B) (A.map f)

@[simp] theorem sigmaMap_obj_base (a) :
    ((sigmaMap B f).obj a).base = (A.map f).obj a.base :=
  rfl

@[simp] theorem sigmaMap_obj_fiber (a) :
    ((sigmaMap B f).obj a).fiber = (B.map ((ιNatTrans f).app (base a))).obj (fiber a) := rfl

@[simp] theorem sigmaMap_map_base {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).base = (A.map f).map p.base := rfl

theorem sigmaMap_map_fiber_aux {a b : sigmaObj B x} {p : a ⟶ b} :
    (((ι A y ⋙ B)).map ((sigmaMap B f).map p).base).obj ((sigmaMap B f).obj a).fiber =
    (B.map ((ιNatTrans f).app (base b))).obj (((ι A x ⋙ B).map p.base).obj a.fiber) := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map, pre_map_base, map_map_base,
    pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app]
  simp only [← Functor.comp_obj, ← Grpd.comp_eq_comp, ← Functor.map_comp]
  congr 3
  exact ((ιNatTrans f).naturality p.base).symm

@[simp] theorem sigmaMap_map_fiber {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).fiber =
    eqToHom (sigmaMap_map_fiber_aux B f) ≫ (B.map ((ιNatTrans f).app (base b))).map p.fiber := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map,
    pre_map_fiber, map_map_fiber, Functor.whiskerRight_app]

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
      eqToHom (by simp) :=
    calc
      B.map ((ιNatTrans (𝟙 x)).app a)
      _ = B.map (eqToHom (by simp)) := by
        rw [ιNatTrans_id_app]
      _ = eqToHom (by simp) := by
        simp
  have h1 : B.map ((ι A x).map (eqToHom hp2).base) = eqToHom (by simp) := by
    simp [eqToHom_base]
  fapply Grothendieck.Groupoidal.ext
  · simp [sigmaMap]
  · simp [sigmaMap_map_fiber, Functor.congr_hom (h p2.base) f.fiber,
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
  · simp only [sigmaObj, Functor.comp_obj, pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app,
      ιNatTrans_comp_app, Functor.map_comp, eqToHom_map, Grpd.comp_eq_comp, Grpd.eqToHom_obj, cast_heq_iff_heq, heq_eq_eq]
    aesop_cat

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
    simp only [sigmaObj, Functor.comp_obj, Functor.comp_map, heq_eqToHom_comp_iff,
      heq_comp_eqToHom_iff, heq_eq_eq]

theorem sigmaMap_comp : sigmaMap B (f ≫ g) = sigmaMap B f ⋙ sigmaMap B g := by
  apply CategoryTheory.Functor.ext
  · intro p q hpq
    simp
  · intro p
    simp

lemma sigmaMap_forget : sigmaMap B f ⋙ forget = forget ⋙ A.map f := rfl

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
  Functor.whiskerRight (ιNatTrans f) (pre A σ ⋙ B) =
    eqToHom (sigma_naturality_aux B σ x) ≫ Functor.whiskerRight (ιNatTrans (σ.map f)) B ≫
    eqToHom (by simp [Functor.assoc, sigma_naturality_aux B σ y]) := by
  simp [Functor.whiskerRight]
  congr
  funext X
  rw [NatTrans.comp_app]
  dsimp
  dsimp[ιNatTrans, Grothendieck.ιNatTrans, Grothendieck.Groupoidal.pre]
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
  · simp only [
      Grothendieck.Groupoidal.comp_fiber, ιNatTrans_app_fiber, ι_obj_fiber, ι_map_fiber,
      eqToHom_trans_assoc, sec_map_fiber, mapFiber', mapFiber]
    rw! [CategoryTheory.Functor.map_id]
    simp only [Grpd.id_eq_id, Functor.id_obj, eqToHom_refl, Functor.id_map,
      Category.id_comp, objFiber'_rfl, mapFiber'EqToHom]
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
    sigmaObj, sigmaMap, pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app]
  rw [← Grpd.map_comp_obj, pairSectionMap_aux_aux]
  rfl

/--
This can be thought of as the action of parallel transport on f
or perhaps the path over f, but defined within the fiber over y

  sigma A B x     ∋ pairObjFiber h x
  |                        -
  |                        |
  |  sigma A B f           |
  |                        |
  V                        V
  sigma A B y     ∋         PairMapFiber
                           _ ⟶ pairObjFiber h y
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
  simp only [Functor.comp_map, sigmaObj, sigmaMap_map_fiber,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    Grpd.map_comp_map', eqToHom_trans_assoc, eqToHom_comp_iff, comp_eqToHom_iff,
    eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
  rw! [pairSectionMap_aux_aux]
  simp only [pairMapFiber_fiber, Functor.map_comp, eqToHom_refl, Category.comp_id, eqToHom_map]

-- NOTE an improvement from 27 seconds to just 9 seconds (with pretty much the same proof)!
-- TODO remove bleedings of `Grothendieck`, e.g. `Grothendieck.forget_obj`
theorem pairMapFiber_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    (pairMapFiber h (f ≫ g)) = eqToHom (by simp)
    ≫ (((sigma (α ⋙ forgetToGrpd) B).map g).map (pairMapFiber h f) ≫ pairMapFiber h g) := by
  fapply Grothendieck.Groupoidal.ext
  · simp [- Functor.comp_obj, mapFiber] -- FIXME
  · rw! [pairMapFiber_fiber, Grothendieck.Groupoidal.comp_fiber, Grothendieck.Groupoidal.comp_fiber,
      Grothendieck.Groupoidal.eqToHom_fiber, eqToHom_map, pairMapFiber_comp_aux,
      Functor.congr_hom (Functor.congr_hom h.symm g) (mapFiber' h f), mapFiber'_comp]
    simp only [pairMapFiber_fiber, mapFiber', eqToHom_trans_assoc, Category.assoc,
      eqToHom_comp_iff, mapFiber'EqToHom]
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
  · simp only [heq_eq_eq]
    erw [pairObjFiber_base]
  · simp only [heq_eq_eq]
    erw [pairObjFiber_fiber]

theorem pair_naturality_aux_1 {x y} (f : x ⟶ y) :
    HEq ((sigmaMap B (σ.map f)).obj (pairObjFiber h (σ.obj x)))
    ((sigmaMap (pre (α ⋙ forgetToGrpd) σ ⋙ B) f).obj (pairObjFiber (pair_naturality_aux h σ) x)) := by
  apply obj_hext'
  . apply Eq.symm
    calc ι (σ ⋙ α ⋙ forgetToGrpd) y ⋙ Grothendieck.Groupoidal.pre (α ⋙ forgetToGrpd) σ ⋙ B =
        (ι ((σ ⋙ α) ⋙ forgetToGrpd) y ⋙ Grothendieck.Groupoidal.pre (α ⋙ forgetToGrpd) σ) ⋙ B := by exact
          rfl
        _ = ι (α ⋙ forgetToGrpd) (σ.obj y) ⋙ B := by rw! [pair_naturality_ι_pre]
  . simp only [heq_eq_eq]
    erw [sigmaMap_obj_base]
  . simp only [heq_eq_eq]
    erw [sigmaMap_obj_fiber]

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

namespace sigma
section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}} (B : ∫(A) ⥤ Grpd.{v₁,u₁})

@[simps] def fstAux : sigma A B ⟶ A where
  app x := Grpd.homOf forget

def fstAux' : ∫(sigma A B) ⥤ ∫(A) :=
  map (fstAux B)

/-- `fst` projects out the pointed groupoid `(A,a)` appearing in `(A,B,a : A,b : B a)` -/
def fst : ∫(sigma A B) ⥤ PGrpd :=
  fstAux' B ⋙ toPGrpd A

theorem fst_forgetToGrpd : fst B ⋙ forgetToGrpd = forget ⋙ A := by
  dsimp only [fst, fstAux']
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
    assocIso B f ≪≫ Functor.isoWhiskerLeft (sigmaMap B f) (assocIso B g)
    ≪≫ eqToIso (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp [assocIso, preNatIso_congr B (ιNatIso_comp A f g), preNatIso_comp, assocIso,
    sigmaMap, Functor.isoWhiskerLeft_trans]
  rfl

def assocHom {x y : Γ} (f : x ⟶ y) :
    assocFib B x ⟶ sigmaMap B f ⋙ assocFib B y :=
  (assocIso B f).hom

@[simp] theorem assocHom_id {x : Γ} :
    assocHom B (𝟙 x) = eqToHom (by simp [sigmaMap_id, Functor.id_comp]) := by
  simp [assocHom, assocIso_id]

theorem assocHom_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    assocHom B (f ≫ g) = assocHom B f ≫ Functor.whiskerLeft (sigmaMap B f) (assocHom B g) ≫
      eqToHom (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp [assocHom, assocIso_comp]

def assoc : ∫(sigma A B) ⥤ ∫(B) :=
  functorFrom (assocFib B) (assocHom B) (by simp) (by simp [assocHom_comp])

def snd : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ toPGrpd B

theorem ι_sigma_comp_map_fstAux (x) : ι (sigma A B) x ⋙ map (fstAux B)
    = forget ⋙ ι A x := by
  apply Grothendieck.Groupoidal.Functor.hext
  · rw [Functor.assoc, map_forget]
    rfl
  · intro x
    simp
  · intro x y f
    simp only [sigma_obj, sigmaObj, Functor.comp_obj, ι_obj_base,
      Functor.comp_map, ι_map_base, fstAux_app, ι_obj_fiber,
      Grothendieck.Groupoidal.forget_obj, map_map_fiber, sigma_map, eqToHom_refl, ι_map_fiber,
      Grothendieck.Groupoidal.forget_map, Category.id_comp, heq_eq_eq]
    convert comp_base (eqToHom _) f
    · rfl
    · simp

lemma asFunctorFrom_fib_map_fstAux {x : Γ} :
    asFunctorFrom_fib (map (fstAux B)) x = ι (sigma A B) x ⋙ map (fstAux B) :=
  rfl

lemma asFunctorFrom_hom_map_fstAux {c c' :Γ} (f: c ⟶ c') :
    asFunctorFrom_hom (map (fstAux B)) f = Functor.whiskerRight (ιNatTrans f) (map (fstAux B)) := by
  rfl

theorem functorFrom_comp_fib_assocFib_forget :
  functorFrom_comp_fib (assocFib B) forget = asFunctorFrom_fib (map (fstAux B)) := by
  ext x
  exact (ι_sigma_comp_map_fstAux B x).symm

lemma ιNatTrans_app_base_eq {c₁ c₂ : Γ} (f: c₁ ⟶ c₂) (x : ((sigma A B).obj c₁)) :
    (ιNatTrans f).app (base x) = (map (fstAux B)).map ((ιNatTrans f).app x) := by
  apply Grothendieck.Groupoidal.hext
  · rfl
  · simp only [map_map_fiber, eqToHom_refl, Category.id_comp]
    rfl

theorem assoc_forget : assoc B ⋙ forget = fstAux' B := by
  simp only [assoc, fstAux', functorFrom_comp]
  rw [← asFunctorFrom (map (fstAux B))]
  fapply CategoryTheory.Grothendieck.functorFrom_eq_of
  · exact functorFrom_comp_fib_assocFib_forget B
  · intro c₁ c₂ f
    rw [comp_eqToHom_iff]
    ext x
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply ιNatTrans_app_base_eq

theorem snd_forgetToGrpd : snd B ⋙ forgetToGrpd = fstAux' B ⋙ B :=
  calc
    _ = assoc B ⋙ forget ⋙ B := rfl
    _ = fstAux' B ⋙ B := by rw [← assoc_forget]; rfl

@[simp] theorem fst_obj_fiber {x} : ((fst B).obj x).fiber = x.fiber.base := rfl

@[simp] theorem fst_map_fiber {x y} (f : x ⟶ y) : ((fst B).map f).fiber = f.fiber.base := by
  simp [fst, fstAux']

@[simp] theorem snd_obj_fiber {x} : ((snd B).obj x).fiber = x.fiber.fiber := by
  simp [snd, assoc]; rfl

@[simp] theorem assoc_hom_app_fiber {x y : ∫(sigma A B)} (f : x ⟶ y) :
    (assocHom B (Hom.base f)).app x.fiber
    = homMk (homMk f.base (𝟙 _)) (𝟙 _) := by
  apply hext
  · apply hext
    · simp [sigmaObj, assocFib, Functor.comp_obj, assocHom,
        assocIso, preNatIso_hom_app_base, ιNatIso_hom]
    · rw [assocHom, assocIso, preNatIso_hom_app_base, ιNatIso_hom]
      simp
      rfl
  · simp [assocHom, assocIso]
    rfl

-- FIXME: should probably make `snd_map_base` and use that to prove the `eqToHom`
@[simp] theorem snd_map_fiber {x y} (f : x ⟶ y) : ((snd B).map f).fiber =
    eqToHom (by simp [snd, assoc]; rfl) ≫ Hom.fiber (Hom.fiber f) := by
  simp only [snd, assoc, Functor.comp_map]
  rw! [Grothendieck.Groupoidal.functorFrom_map, assoc_hom_app_fiber]
  simp only [toPGrpd_map_fiber, Grothendieck.Groupoidal.comp_fiber]
  rw! [CategoryTheory.Functor.map_id]
  simp

end

section

variable {Γ : Type*} [Category Γ] {A : Γ ⥤ Grpd} (B : ∫(A) ⥤ Grpd)
  (αβ : Γ ⥤ PGrpd) (hαβ : αβ ⋙ forgetToGrpd = sigma A B)

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "groupoid-term", meaning a functor `αβ : Γ ⥤ PGrpd`
satisfying `αβ ⋙ forgetToGrpd = sigma A B : Γ ⥤ Grpd`,
there is a groupoid-term `fst' : Γ ⥤ PGrpd` such that `fst ⋙ forgetToGrpd = A`,
thought of as `fst' : A`.
There is a "groupoid-type" `dependent' : ∫(fst ⋙ forgetToGrpd) ⥤ Grpd`,
which is hequal to `B` modulo `fst ⋙ forgetToGrpd` being equal to `A`.
And there is a groupoid-term `snd' : Γ ⥤ PGrpd` satisfying
`snd' ⋙ forgetToGrpd = sec _ fst rfl ⋙ dependent'`.
-/
def fst' : Γ ⥤ PGrpd := sec (sigma A B) αβ hαβ ⋙ fst B

@[inherit_doc fst'] theorem fst'_forgetToGrpd : fst' B αβ hαβ ⋙ forgetToGrpd = A :=
  rfl

@[inherit_doc fst'] def dependent' : ∫(fst' B αβ hαβ ⋙ forgetToGrpd) ⥤ Grpd :=
  map (eqToHom rfl) ⋙ B

end

section
variable {Γ : Type*} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫(A) ⥤ Grpd)
  (αβ : Γ ⥤ PGrpd) (hαβ : αβ ⋙ forgetToGrpd = sigma A B)

@[inherit_doc fst'] def snd' : Γ ⥤ PGrpd := sec (sigma A B) αβ hαβ ⋙ snd B

@[simp] theorem fst'_obj_base {x} : ((fst' B αβ hαβ).obj x).base =
    A.obj x := rfl

theorem fst'_obj_fiber {x} : ((fst' B αβ hαβ).obj x).fiber = (objFiber' hαβ x).base := by
  simp [fst']

@[simp] theorem fst'_map_base {x y} (f : x ⟶ y) : ((fst' B αβ hαβ).map f).base =
    A.map f := rfl

theorem fst'_map_fiber {x y} (f : x ⟶ y) : ((fst' B αβ hαβ).map f).fiber =
    (mapFiber' hαβ f).base := by
  simp [fst']

theorem sec_fstAux' : sec (sigma A B) αβ hαβ ⋙ fstAux' B =
  sec (fst' B αβ hαβ ⋙ forgetToGrpd) (fst' B αβ hαβ) rfl := by
  apply Grothendieck.Groupoidal.Functor.hext
  · rfl
  · intro x
    erw [Grothendieck.Groupoidal.sec_obj_fiber]
    rfl
  · intro x y f
    erw [Grothendieck.Groupoidal.sec_map_fiber]
    simp [fstAux', mapFiber'_rfl, mapFiber, fst'_map_fiber]

@[inherit_doc fst] theorem snd'_forgetToGrpd : snd' B αβ hαβ ⋙ forgetToGrpd
    = sec _ (fst' B αβ hαβ) rfl ⋙ dependent' B αβ hαβ := by
  rw [snd', Functor.assoc, snd_forgetToGrpd, dependent', ← Functor.assoc, sec_fstAux']
  simp [map_id_eq, Functor.id_comp]

theorem snd'_obj_fiber {x} : ((snd' B αβ hαβ).obj x).fiber = (objFiber' hαβ x).fiber := by
  simp [snd']

-- FIXME: here the `simp` proof should also be factored through a `snd_map_base`
theorem snd'_map_fiber {x y} (f : x ⟶ y) : ((snd' B αβ hαβ).map f).fiber =
    eqToHom (by simp [snd', snd, assoc]; rfl) ≫ Hom.fiber (mapFiber' hαβ f) := by
  simp [snd']

theorem ι_fst'_forgetToGrpd_comp_dependent' (x) :
    ι (fst' B αβ hαβ ⋙ forgetToGrpd) x ⋙ dependent' B αβ hαβ = ι A x ⋙ B := by
  simp [dependent', map_id_eq, Functor.id_comp, fst'_forgetToGrpd]

theorem pairObjFiber_snd'_eq (x : Γ) : pairObjFiber (snd'_forgetToGrpd B αβ hαβ) x =
    objMk (objFiber' hαβ x).base (objFiber' (snd'_forgetToGrpd B αβ hαβ) x) := by
  apply obj_hext
  · rw [pairObjFiber_base]
    simp [objFiber, fst'_obj_fiber]
  · rw [pairObjFiber_fiber]
    simp

theorem pairObjFiber_snd'_heq (x : Γ) : HEq (pairObjFiber (snd'_forgetToGrpd B αβ hαβ) x)
    (αβ.obj x).fiber := by
  rw [pairObjFiber_snd'_eq]
  apply @HEq.trans _ _ _ _ ((objFiber'EqToHom hαβ x).obj (αβ.obj x).fiber) _ ?_ ?_
  · apply obj_hext'
    · apply ι_fst'_forgetToGrpd_comp_dependent'
    · rfl
    · rfl
  · simp [Grpd.eqToHom_obj]

theorem pairMapFiber_snd'_eq {x y} (f : x ⟶ y) :
    pairMapFiber (snd'_forgetToGrpd B αβ hαβ) f
    = homMk (mapFiber (fst' B αβ hαβ) f)
      (eqToHom (pairMapFiber_aux (snd'_forgetToGrpd B αβ hαβ) f)
        ≫ mapFiber' (snd'_forgetToGrpd B αβ hαβ) f) := by
  apply hext
  · simp
  · simp

theorem pairMapFiber_snd'_heq_src_heq {x y} (f : x ⟶ y) :
    HEq ((sigmaMap (dependent' B αβ hαβ) f).obj (pairObjFiber (snd'_forgetToGrpd _ _ hαβ) x))
    ((objFiber'EqToHom hαβ y).obj ((αβ.map f).base.obj (αβ.obj x).fiber)) := by
  have h : (αβ.map f).base.obj (αβ.obj x).fiber = _ :=
    Functor.congr_obj (Functor.congr_hom hαβ f) (αβ.obj x).fiber
  rw [Grpd.eqToHom_obj, heq_cast_iff_heq, h]
  simp only [Grpd.forgetToCat, dependent', eqToHom_refl, sigmaObj, Functor.comp_obj,
    Grothendieck.forget_obj, fst'_obj_base, sigma_obj, sigma_map, Grpd.comp_eq_comp,
    Grpd.eqToHom_obj, heq_cast_iff_heq]
  rw! [map_id_eq]
  congr
  apply eq_of_heq
  rw [heq_cast_iff_heq]
  apply HEq.trans _ (pairObjFiber_snd'_heq B αβ hαβ x)
  simp only [pairObjFiber, Functor.comp_obj, Grothendieck.forget_obj, fst'_obj_base, sigmaObj]
  congr
  simp [map_id_eq]

theorem pairMapFiber_snd'_heq_trg_heq {y} :
    HEq (pairObjFiber (snd'_forgetToGrpd B αβ hαβ) y)
    ((objFiber'EqToHom hαβ y).obj (αβ.obj y).fiber) := by
  rw [Grpd.eqToHom_obj, heq_cast_iff_heq]
  exact pairObjFiber_snd'_heq B αβ hαβ y

theorem sigmaMap_obj_objFiber' {x y} (f : x ⟶ y) : (sigmaMap B f).obj (objFiber' hαβ x) =
    (objFiber'EqToHom hαβ y).obj ((αβ.map f).base.obj (αβ.obj x).fiber) := by
  erw [Functor.congr_obj (Functor.congr_hom hαβ.symm f) (objFiber' hαβ x)]
  simp [Grpd.eqToHom_obj, objFiber', objFiber]

theorem pairMapFiber_snd'_heq {x y} (f : x ⟶ y) : HEq (pairMapFiber (snd'_forgetToGrpd B αβ hαβ) f)
    (αβ.map f).fiber := by
  rw [pairMapFiber_snd'_eq]
  apply @HEq.trans _ _ _ _ ((objFiber'EqToHom hαβ y).map (αβ.map f).fiber) _ ?_ ?_
  · apply hext'
    · apply ι_fst'_forgetToGrpd_comp_dependent'
    · apply pairMapFiber_snd'_heq_src_heq
    · rw [Grpd.eqToHom_obj, heq_cast_iff_heq]
      exact pairObjFiber_snd'_heq B αβ hαβ y
    · rw [homMk_base, mapFiber, fst'_map_fiber]
      congr!
      · apply sigmaMap_obj_objFiber'
      · apply HEq.trans (eqToHom_comp_heq _ _)
        simp
    · simp only [homMk_fiber, eqToHom_comp_heq_iff]
      apply HEq.trans (mapFiber'_heq _ f)
      simp only [snd'_map_fiber, Functor.comp_map, eqToHom_comp_heq_iff]
      congr!
      · apply sigmaMap_obj_objFiber'
      · apply HEq.trans (eqToHom_comp_heq _ _)
        simp
  · simp [Grpd.eqToHom_hom]

theorem eta : pair (fst' B αβ hαβ) (snd' B αβ hαβ)
    (dependent' B αβ hαβ) (snd'_forgetToGrpd _ _ _) = αβ := by
  apply PGrpd.Functor.hext
  · rw [pair, PGrpd.functorTo_forget, hαβ]
    congr
    simp [dependent', map_id_eq, Functor.id_comp]
  · intro x
    exact pairObjFiber_snd'_heq _ _ _ _
  · intro x y f
    exact pairMapFiber_snd'_heq _ _ _ _

end

section
variable {Γ : Type*} [Groupoid Γ] {α β : Γ ⥤ PGrpd.{v₁,u₁}}
  {B : ∫(α ⋙ forgetToGrpd) ⥤ Grpd.{v₁,u₁}} (h : β ⋙ forgetToGrpd = sec _ α rfl ⋙ B)

@[simp] theorem fst'_pair : fst' B (pair α β B h) (pair_comp_forgetToGrpd _) = α := by
  apply PGrpd.Functor.hext
  · rw [fst'_forgetToGrpd]
  · intro x
    erw [fst'_obj_fiber]
  · intro x y f
    simp only [fst'_map_fiber, objFiber'_rfl, mapFiber'_rfl]
    erw [pairMapFiber_base, mapFiber]

@[simp] theorem snd'_pair : snd' B (pair α β B h) (pair_comp_forgetToGrpd _) = β := by
  apply PGrpd.Functor.hext
  · rw [snd'_forgetToGrpd, h, dependent']
    congr 2
    · rw [fst'_pair]
    · simp [map_id_eq, Functor.id_comp]
  · intro x
    simp only [snd'_obj_fiber, objFiber'_rfl, objFiber, pair_obj_fiber, pairObjFiber_fiber]
    simp [objFiber', Grpd.eqToHom_obj, objFiber]
  · intro x y f
    simp only [snd'_map_fiber]
    apply (eqToHom_comp_heq _ _).trans
    simp only [objFiber'_rfl, sigma_obj, Grpd.coe_of, mapFiber', eqToHom_refl,
      Grpd.id_eq_id, mapFiber'EqToHom, pair_map_fiber, Functor.id_map,
      Grothendieck.Groupoidal.comp_fiber, Grothendieck.Groupoidal.id_fiber, eqToHom_map]
    apply (eqToHom_comp_heq _ _).trans
    rw [pairMapFiber_fiber]
    apply (eqToHom_comp_heq _ _).trans
    simp only [mapFiber', mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc]
    apply (eqToHom_comp_heq _ _).trans
    simp

end

end sigma

end FunctorOperation

open FunctorOperation

/--
Behavior of the Σ-type former (a natural transformation) on an input.
By Yoneda, "an input" is the same as a map from a representable into the domain.
-/
def smallUSig_app {Γ : Ctx}
    (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Ty) :
    y(Γ) ⟶ smallU.{v}.Ty :=
  yonedaCategoryEquiv.symm (sigma _ (smallU.PtpEquiv.snd AB))

/--
Naturality for the formation rule for Σ-types.
Also known as Beck-Chevalley
-/
theorem smallUSig_naturality {Γ Δ : Ctx} (σ : Δ ⟶ Γ)
    (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Ty) :
    smallUSig_app (ym(σ) ≫ AB) = ym(σ) ≫ smallUSig_app AB := by
  dsimp only [smallUSig_app]
  rw [← yonedaCategoryEquiv_symm_naturality_left, sigma_naturality,
  -- note the order of rewrite is first the fiber, then the base
  -- this allows rw! to cast the proof in the `eqToHom`
    smallU.PtpEquiv.snd_naturality]
  rw! [smallU.PtpEquiv.fst_naturality]
  congr 2
  · simp [map_id_eq, Functor.id_comp]

/-- The formation rule for Σ-types for the ambient natural model `base`
  If possible, don't use NatTrans.app on this,
  instead precompose it with maps from representables.
-/
def smallUSig : smallU.{v}.Ptp.obj smallU.{v}.Ty
  ⟶ smallU.{v}.Ty :=
  NatTrans.yonedaMk smallUSig_app smallUSig_naturality

lemma smallUSig_app_eq {Γ : Ctx} (AB : y(Γ) ⟶ _) : AB ≫ smallUSig =
    smallUSig_app AB := by
  simp only [smallUSig, NatTrans.yonedaMk_app]

open smallU.compDom

def smallUPair_app {Γ : Ctx}
    (ab : y(Γ) ⟶ smallU.{v}.uvPolyTp.compDom smallU.{v}.uvPolyTp)
    : y(Γ) ⟶ smallU.{v}.Tm :=
  yonedaCategoryEquiv.symm (pair _ _ _ (snd_forgetToGrpd ab))

theorem smallUPair_naturality {Γ Δ : Ctx} (f : Δ ⟶ Γ)
    (ab : y(Γ) ⟶ smallU.compDom.{v}) :
    smallUPair_app (ym(f) ≫ ab) = ym(f) ≫ smallUPair_app ab := by
  dsimp only [smallUPair_app]
  rw [← yonedaCategoryEquiv_symm_naturality_left, pair_naturality]
  -- Like with `smallUSig_naturality` rw from inside to outside (w.r.t type dependency)
  rw! [dependent_naturality, snd_naturality, fst_naturality]
  simp [map_id_eq, Functor.id_comp]

def smallUPair : smallU.compDom.{v} ⟶ smallU.{v}.Tm :=
  NatTrans.yonedaMk smallUPair_app smallUPair_naturality

lemma smallUPair_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ _) : ab ≫ smallUPair =
    yonedaCategoryEquiv.symm (pair _ _ _ (snd_forgetToGrpd ab)) := by
  simp only [smallUPair, smallUPair_app, NatTrans.yonedaMk_app]

namespace SigmaPullback

open Limits

section

theorem smallUPair_tp : smallUPair.{v} ≫ smallU.{v}.tp =
    smallU.comp.{v} ≫ smallUSig.{v} := by
  apply hom_ext_yoneda
  intros Γ ab
  rw [← Category.assoc, ← Category.assoc, smallUPair_app_eq,
    smallUSig_app_eq, smallU_tp, π,
    ← yonedaCategoryEquiv_symm_naturality_right,
    pair_comp_forgetToGrpd, smallUSig_app]
  congr 2
  · rw [fst_forgetToGrpd]
  · exact dependent_heq.{v} ab

section
variable {Γ : Ctx} (AB : y(Γ) ⟶ smallU.Ptp.obj.{v} y(U.{v}))
  (αβ : y(Γ) ⟶ y(E.{v})) (hαβ : αβ ≫ ym(π) = AB ≫ smallUSig)

include hαβ in
theorem yonedaCategoryEquiv_forgetToGrpd : yonedaCategoryEquiv αβ ⋙ forgetToGrpd
    = sigma (smallU.PtpEquiv.fst AB) (smallU.PtpEquiv.snd AB) := by
  erw [← yonedaCategoryEquiv_naturality_right, hαβ]
  rw [smallUSig_app_eq, smallUSig_app, yonedaCategoryEquiv.apply_symm_apply]

def lift : y(Γ) ⟶ smallU.compDom.{v} :=
  let β' := smallU.PtpEquiv.snd AB
  let αβ' := yonedaCategoryEquiv αβ
  let hαβ' : yonedaCategoryEquiv αβ ⋙ forgetToGrpd
    = sigma (smallU.PtpEquiv.fst AB) (smallU.PtpEquiv.snd AB) :=
    yonedaCategoryEquiv_forgetToGrpd _ _ hαβ
  mk (sigma.fst' β' αβ' hαβ') (sigma.dependent' β' αβ' hαβ')
  (sigma.snd' β' αβ' hαβ') (sigma.snd'_forgetToGrpd β' αβ' hαβ')

theorem fac_left : lift.{v} AB αβ hαβ ≫ smallUPair.{v} = αβ := by
  rw [smallUPair_app_eq]
  dsimp only [lift]
  rw! [dependent_mk, snd_mk, fst_mk]
  simp only [eqToHom_refl, map_id_eq, Cat.of_α, Functor.id_comp]
  rw [yonedaCategoryEquiv.symm_apply_eq, sigma.eta]

theorem fac_right : lift.{v} AB αβ hαβ ≫ smallU.comp.{v} = AB := by
  apply smallU.PtpEquiv.hext
  · rw [← fst_forgetToGrpd]
    dsimp only [lift]
    rw [fst_mk, sigma.fst'_forgetToGrpd]
  · apply HEq.trans (dependent_heq _).symm
    rw [lift, dependent_mk]
    dsimp [sigma.dependent']
    simp [map_id_eq, Functor.id_comp]
    apply map_eqToHom_comp_heq

theorem hom_ext (m n : y(Γ) ⟶ smallU.compDom.{v})
    (hComp : m ≫ smallU.comp = n ≫ smallU.comp)
    (hPair : m ≫ smallUPair = n ≫ smallUPair) : m = n := by
  have h : (pair (fst m) (snd m) (dependent m)
        (snd_forgetToGrpd m)) =
      (pair (fst n) (snd n) (dependent n)
        (snd_forgetToGrpd n)) :=
      calc _
        _ = yonedaCategoryEquiv (m ≫ smallUPair) := by
          simp [smallUPair_app_eq m]
        _ = yonedaCategoryEquiv (n ≫ smallUPair) := by rw [hPair]
        _ = _ := by
          simp [smallUPair_app_eq n]
  have hdep : HEq (dependent m) (dependent n) := by
    refine (dependent_heq _).trans
      $ HEq.trans ?_ $ (dependent_heq _).symm
    rw [hComp]
  have : fst m ⋙ forgetToGrpd = fst n ⋙ forgetToGrpd := by
    rw [fst_forgetToGrpd, fst_forgetToGrpd, hComp]
  apply smallU.compDom.hext
  · calc fst m
      _ = sigma.fst' _ (FunctorOperation.pair (fst m) (snd m)
        (dependent m) (snd_forgetToGrpd m)) _ :=
          (sigma.fst'_pair _).symm
      _ = sigma.fst' _ (FunctorOperation.pair (fst n) (snd n)
        (dependent n) (snd_forgetToGrpd n)) _ := by
          rw! [h]
          congr!
      _ = fst n := sigma.fst'_pair _
  · exact hdep
  · calc snd m
      _ = sigma.snd' _ (FunctorOperation.pair (fst m) (snd m)
        (dependent m) (snd_forgetToGrpd m)) _ :=
          (sigma.snd'_pair _).symm
      _ = sigma.snd' _ (FunctorOperation.pair (fst n) (snd n)
        (dependent n) (snd_forgetToGrpd n)) _ := by
          rw! [h]
          congr!
      _ = snd n := sigma.snd'_pair _

theorem uniq (m : y(Γ) ⟶ smallU.compDom)
    (hmAB : m ≫ smallU.comp = AB) (hmαβ : m ≫ smallUPair = αβ) :
    m = lift AB αβ hαβ := by
  apply hom_ext
  · rw [hmAB, fac_right]
  · rw [hmαβ, fac_left]

variable (s : RepPullbackCone smallU.{v}.tp smallUSig.{v})

abbrev A := smallU.PtpEquiv.fst s.snd

abbrev B := smallU.PtpEquiv.snd s.snd

end
end

end SigmaPullback

open SigmaPullback

theorem smallU_pb : IsPullback smallUPair.{v,u} smallU.comp.{v,u}
    smallU.{v, u}.tp smallUSig.{v, u} :=
  Limits.RepPullbackCone.is_pullback smallUPair_tp.{v,u}
    (fun s => lift s.snd s.fst s.condition)
    (fun s => fac_left.{v,u} _ _ s.condition)
    (fun s => fac_right.{v,u} _ _ s.condition)
    (fun s m fac_left fac_right => uniq.{v,u} _ _ s.condition m fac_right fac_left)

def smallUSigma : NaturalModelSigma smallU.{v} where
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
