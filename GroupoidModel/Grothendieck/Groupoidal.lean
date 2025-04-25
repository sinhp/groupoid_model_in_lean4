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

variable {Γ : Type u} [Category.{v} Γ]
  (A : Γ ⥤ Grpd.{v₁,u₁})

abbrev Groupoid.compForgetToCat : Γ ⥤ Cat.{v₁,u₁} := A ⋙ Grpd.forgetToCat

namespace Grothendieck

/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
abbrev Groupoidal {C : Type u₁} [Category.{v₁,u₁} C] (F : C ⥤ Grpd.{v₂,u₂}) :=
  Grothendieck (Groupoid.compForgetToCat F)

notation:max "∫(" A ")" => Grothendieck.Groupoidal A

namespace Groupoidal

section

instance {C : Type u₁} [Category.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}} :
    Category (Groupoidal F) :=
  inferInstanceAs (Category (Grothendieck _))

variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance
    (X : C) : Groupoid (Groupoid.compForgetToCat F |>.obj X) where
  inv f := ((F.obj X).str').inv f

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

theorem ι_map (c : C) {X Y : ↑(F.obj c)} (f : X ⟶ Y) :
    (ι F c).map f = ⟨𝟙 _, eqToHom (by simp [ι_obj]) ≫ f⟩ :=
  Grothendieck.ι_map _ _ _

variable {F}

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y :=
  Grothendieck.ιNatTrans _

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

-- TODO move to ForMathlib
theorem Grothendieck.map_eqToHom_obj_base {F G : C ⥤ Cat.{v,u}} (h : F = G)
  (x) : ((Grothendieck.map (eqToHom h)).obj x).base = x.base := rfl

theorem map_id_eq : map (𝟙 F) = Functor.id (Cat.of <| Groupoidal <| F) :=
  Grothendieck.map_id_eq

end

/-- Applying a functor `G : D ⥤ C` to the base of the groupoidal Grothendieck
  construction induces a functor
  `Groupoidal (G ⋙ F) ⥤ Groupoidal F`. -/
def pre {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : D ⥤ Grpd.{v₂,u₂}) (G : C ⥤ D) :
    Groupoidal (G ⋙ F) ⥤ Groupoidal F :=
  Grothendieck.pre (F ⋙ Grpd.forgetToCat) G

-- TODO this should be replaced with Groupoidal.pre
def functorial {C D : Grpd.{v₁,u₁}} (F : C ⟶ D) (G : D ⥤ Grpd.{v₂,u₂}) :
  Grothendieck (Groupoid.compForgetToCat (F ⋙ G))
  ⥤ Grothendieck (Groupoid.compForgetToCat G) where
  obj X := ⟨F.obj X.base, X.fiber⟩
  map {X Y} f := ⟨F.map f.base, f.fiber⟩
  map_id X := by
    fapply Grothendieck.ext
    · exact F.map_id X.base
    · simp only [Grothendieck.id_fiber, eqToHom_trans]
  map_comp {X Y Z} f g := by
    simp only [Grothendieck.comp]
    fapply Grothendieck.ext
    · exact F.map_comp f.base g.base
    · erw [Grothendieck.comp_fiber (F:= Groupoid.compForgetToCat (F ⋙ G)) f g]
      simp [eqToHom_trans]

instance toPCatObjGroupoid
    (x : Grothendieck (Groupoid.compForgetToCat.{v,u,v₁,u₁} A)) :
    Groupoid x.toPCatObj := by
  dsimp [Grpd.forgetToCat]
  infer_instance

instance toPCatObjPointed (x : Grothendieck (Groupoid.compForgetToCat A)) :
    PointedGroupoid x.toPCatObj :=
  PointedGroupoid.of x.toPCatObj PointedCategory.pt

def toPGrpd : Grothendieck (Groupoid.compForgetToCat A) ⥤ PGrpd.{v₁,u₁} where
  obj x := PGrpd.of x.toPCatObj
  map := Grothendieck.toPCatMap
  map_id := (Grothendieck.toPCat (Groupoid.compForgetToCat A)).map_id
  map_comp := (Grothendieck.toPCat (Groupoid.compForgetToCat A)).map_comp

theorem toPGrpd_comp_forgetToPCat :
    toPGrpd A ⋙ PGrpd.forgetToPCat = toPCat (Groupoid.compForgetToCat A) :=
  rfl


section

variable {F : Γ ⥤ Grpd.{v₁,u₁}}

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_base {x y : Groupoidal F} (eq : x = y) :
    (eqToHom eq).base = eqToHom (by simp [eq]) := by
  cases eq
  simp

/-- This is the proof of equality used in the eqToHom in `Groupoidal.eqToHom_fiber` -/
theorem eqToHom_fiber_aux {g1 g2 : Groupoidal F}
    (eq : g1 = g2) : (F.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
  cases eq
  simp

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_fiber {g1 g2 : Groupoidal F} (eq : g1 = g2) : (eqToHom eq).fiber = eqToHom (eqToHom_fiber_aux eq) := by
  cases eq
  simp

@[ext (iff := false)]
theorem ext {X Y : Groupoidal F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g w_base w_fiber

@[simp] theorem ιNatTrans_id_app {X : Γ} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (𝟙 X)).app a =
    eqToHom (by simp) := Grothendieck.ιNatTrans_id_app

@[simp] theorem ιNatTrans_comp_app {X Y Z : Γ} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) := Grothendieck.ιNatTrans_comp_app

@[simp] theorem base_eqToHom {X Y : Groupoidal F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg base h) :=
  Grothendieck.base_eqToHom _

@[simp] theorem comp_base {X Y Z : Groupoidal F} (f : X ⟶ Y)
    (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

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

-- theorem eta (p : Groupoidal F) : ⟨p.base, p.fiber⟩ = p := rfl

theorem obj_ext_hEq {p1 p2 : Groupoidal F} (hbase : p1.base = p2.base)
    (hfib : HEq p1.fiber p2.fiber) : p1 = p2 :=
  Grothendieck.obj_ext_hEq hbase hfib


variable (α : F ⟶ G) (X : Groupoidal F)

@[simp] theorem map_obj_base : ((map α).obj X).base = X.base :=
  Grothendieck.map_obj_base _ _

@[simp] theorem map_obj_fiber :
    ((map α).obj X).fiber = (α.app X.base).obj X.fiber :=
  Grothendieck.map_obj_fiber _ _

variable {X} {Y : Groupoidal F} (f : X ⟶ Y)

@[simp] theorem map_map_base : ((Groupoidal.map α).map f).base = f.base
    := Grothendieck.map_map_base _ _

@[simp] theorem map_map_fiber :
  ((Groupoidal.map α).map f).fiber =
    eqToHom (Functor.congr_obj (map.proof_1 (whiskerRight α _) f) X.fiber)
    ≫ (α.app Y.base).map f.fiber := Grothendieck.map_map_fiber _ _

@[simp] theorem fiber_eqToHom (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) :=
  Grothendieck.fiber_eqToHom _

@[simp] theorem comp_fiber {Z : Groupoidal F}
    (g : Y ⟶ Z) : Hom.fiber (f ≫ g) = eqToHom (by simp [Grpd.forgetToCat])
    ≫ (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl
end
end


namespace IsMegaPullback

theorem comm_sq : Groupoidal.toPGrpd A ⋙ PGrpd.forgetToGrpd
    = Grothendieck.forget _ ⋙ A := rfl

variable {A} {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PGrpd.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ A)

theorem toPGrpd_eq_lift :
    toPGrpd A =
    PGrpd.IsMegaPullback.lift
      (toPCat (Groupoid.compForgetToCat A))
      (Grothendieck.forget _ ⋙ A) rfl :=
  PGrpd.IsMegaPullback.lift_uniq
    (toPCat (Groupoid.compForgetToCat A))
    (Grothendieck.forget _ ⋙ A)
    rfl _ rfl rfl

def lift : C ⥤ Groupoidal A :=
  Grothendieck.IsMegaPullback.lift
    (fst ⋙ PGrpd.forgetToPCat) snd (by
      simp only [Groupoid.compForgetToCat, ← Functor.assoc, ← w]
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
    lift fst snd w ⋙ Grothendieck.forget _
    = snd :=
  Grothendieck.IsMegaPullback.fac_right
    (fst ⋙ PGrpd.forgetToPCat) snd (by
    rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq,
      ← Functor.assoc, w, Functor.assoc])

theorem lift_uniq (m : C ⥤ Groupoidal A)
    (hl : m ⋙ toPGrpd _ = fst)
    (hr : m ⋙ Grothendieck.forget _ = snd) :
    m = lift _ _ w := by
  apply Grothendieck.IsMegaPullback.lift_uniq
  · rw [← toPGrpd_comp_forgetToPCat, ← hl, Functor.assoc]
  · exact hr

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
`var' : Grothendieck(Groupoid.compForgetToCat A) ⟶ Grothendieck(Grpd.forgetToCat)`
given by pullback pasting in the following pasting diagram.

  ↑Grothendieck (Groupoid.compForgetToCat A) .-.-.-.-> ↑GrothendieckForgetToCat -----> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
noncomputable def var' :
    IsPullback.uLiftGrothendieck (Groupoid.compForgetToCat.{u} A)
    ⟶ IsPullback.uLiftGrothendieck Grpd.forgetToCat.{u,u} :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget
      (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
      (Grothendieck.isPullback
        (Groupoid.compForgetToCat.{u} A)).cone.condition_one

theorem var'_uLiftToPCat :
    var' A ≫ (uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = uLiftToPCat (Groupoid.compForgetToCat.{u} A) :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_fst
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A)).cone.condition_one

theorem var'_forget :
    var' A ≫ (uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    = uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A) ≫ uLiftA A :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_snd
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A)) ((IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A)).cone.condition_one


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
    (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
    (IsPullback.uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    (uLiftA A) :=
  IsPullback.of_right'
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A))
    (Grothendieck.isPullback (Grpd.forgetToCat.{u,u}))

theorem isPullback_aux:
    IsPullback
      (Cat.homOf (var' A)
        ≫ (Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
      (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
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
    = IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A) := var'_uLiftToPCat A
  dsimp [IsPullback.uLiftToPCat] at h
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
      = IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat A) ⋙ uLiftA A :=
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

↑Grothendieck (Groupoid.compForgetToCat A) -- toPGrpd --> PGrpd
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
      (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf (ULift.downFunctor.{u,u} ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {Δ : Type u₃} [Category.{v₃} Δ]
    (σ : Δ ⥤ Γ)

@[simp] theorem ιCompPre (A : Γ ⥤ Grpd.{v₁,u₁}) (x : Δ)
    : ι (σ ⋙ A) x ⋙ Groupoidal.pre A σ = ι A (σ.obj x) :=
  Grothendieck.ιCompPre _ (A ⋙ Grpd.forgetToCat) _

end

section

variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A)

def sec' :
    Γ ⥤ Groupoidal A :=
  Groupoidal.IsMegaPullback.lift α (Functor.id _)
    (by simp [h, Functor.id_comp])

@[simp] def sec'_toPGrpd : Groupoidal.sec' h ⋙ Groupoidal.toPGrpd _ = α := by
  simp [Groupoidal.sec']

@[simp] def sec'_forget : Groupoidal.sec' h ⋙ Grothendieck.forget _
    = Functor.id _ :=
  rfl

end

variable {Γ : Type u} [Category.{v} Γ]
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
def sec (α : Γ ⥤ PGrpd.{v₁,u₁}) :
    Γ ⥤ Groupoidal (α ⋙ PGrpd.forgetToGrpd) :=
  sec' rfl

@[simp] def sec_toPGrpd (α : Γ ⥤ PGrpd.{v₁,u₁}) :
    Groupoidal.sec α ⋙ Groupoidal.toPGrpd _ = α := sec'_toPGrpd _

@[simp] def sec_forget (α : Γ ⥤ PGrpd.{v₁,u₁}) :
    Groupoidal.sec α ⋙ Grothendieck.forget _ = Functor.id _ := rfl

end Groupoidal
end Grothendieck
end CategoryTheory
