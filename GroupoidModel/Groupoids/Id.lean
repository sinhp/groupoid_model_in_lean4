import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.ForMathlib
import GroupoidModel.Grothendieck.Groupoidal.Basic
import GroupoidModel.Grothendieck.Groupoidal.IsPullback
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.ForMathlib.CategoryTheory.Functor.IsPullback
import GroupoidModel.Pointed.IsPullback
import Mathlib.CategoryTheory.Groupoid.Discrete
import Poly.UvPoly.Basic
import GroupoidModel.Groupoids.Basic
import GroupoidModel.Groupoids.IsPullback
import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Russell_PER_MS.NaturalModel

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

noncomputable

section BiPointed

def PGrpd.inc (G : Type) [Groupoid G] : G ⥤ PGrpd  where
  obj x := {base := Grpd.of G,fiber := x}
  map f := {base := Functor.id G, fiber := f}
  map_comp {X Y Z} f g := by
    simp[CategoryStruct.comp,Grothendieck.comp,Grpd.forgetToCat]
    congr

namespace GrothendieckPointedCategories

abbrev BPCat := Grothendieck (PCat.forgetToCat)

namespace BPCat

abbrev forgetToCat : BPCat ⥤ Cat where
  obj x := x.base.base
  map f := f.base.base
  map_comp := by
    intros x y z f g
    exact rfl

abbrev FirstPointed  : BPCat ⥤ PCat := Grothendieck.forget _

def SecondPointed : BPCat ⥤ PCat where
  obj x := {base := x.base.base, fiber := x.fiber}
  map f := {base := f.base.base, fiber := f.fiber}
  map_comp := by
    intros x y z f g
    exact rfl

/- This needs a better name but I cant come up with one now-/
theorem Comutes : FirstPointed ⋙ PCat.forgetToCat = SecondPointed ⋙ PCat.forgetToCat := by
  simp[FirstPointed,SecondPointed,PCat.forgetToCat,Functor.comp]


def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PCat.forgetToCat.{u,v} PCat.forgetToCat.{u,v}
  := @CategoryTheory.Grothendieck.isPullback PCat _ (PCat.forgetToCat)

end BPCat

abbrev BPGrpd := Grothendieck.Groupoidal (PGrpd.forgetToGrpd)

instance : Groupoid BPGrpd := sorry


namespace BPGrpd

abbrev forgetToGrpd : BPGrpd ⥤ Grpd where
  obj x := x.base.base
  map f := f.base.base
  map_comp := by
    intros x y z f g
    exact rfl

abbrev FirstPointed  : BPGrpd ⥤ PGrpd := @Grothendieck.Groupoidal.forget _ _ (PGrpd.forgetToGrpd)

def SecondPointed : BPGrpd ⥤ PGrpd where
  obj x := {base := x.base.base, fiber := x.fiber}
  map f := {base := f.base.base, fiber := f.fiber}
  map_comp := by
    intros x y z f g
    exact rfl

/- Same thing with this name-/
theorem Comutes : FirstPointed ⋙ PGrpd.forgetToGrpd = SecondPointed ⋙ PGrpd.forgetToGrpd := by
  simp[FirstPointed,SecondPointed,PGrpd.forgetToGrpd,Functor.comp]
  exact Prod.mk_inj.mp rfl

def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PGrpd.forgetToGrpd.{u,v} PGrpd.forgetToGrpd.{u,v} := by
  apply @CategoryTheory.Grothendieck.Groupoidal.isPullback PGrpd _ (PGrpd.forgetToGrpd)

def inc (G : Type) [Groupoid G] : G ⥤ BPGrpd := by
  fapply isPullback.lift
  . exact PGrpd.inc G
  . exact PGrpd.inc G
  . simp

end BPGrpd

section Id

/-
In this section we build this diagram

PGrpd-----Refl---->PGrpd
  |                 |
  |                 |
  |                 |
Diag                |
  |                 |
  |                 |
  v                 v
BPGrpd----Id----->Grpd

This is NOT a pullback.

Instead we use Diag and Refl to define a functor R : PGrpd ⥤ Grothendieck.Groupoidal Id
-/


def Id : BPGrpd.{u,u} ⥤ Grpd.{u,u} where
  obj x := Grpd.of (CategoryTheory.Discrete (x.base.fiber ⟶ x.fiber))
  map f := Discrete.functor (fun(a) => { as := inv f.base.fiber ≫ (f.base.base.map a) ≫ f.fiber})
  map_comp {X Y Z} f g := by
    simp
    fapply CategoryTheory.Functor.ext
    . intros a
      rcases a with ⟨a⟩
      simp
      exact
        IsIso.hom_inv_id_assoc
          ((Grothendieck.Groupoidal.Hom.base g).base.map (Grothendieck.Groupoidal.Hom.base f).fiber)
          ((Grothendieck.Groupoidal.Hom.base g).base.map
              ((Grothendieck.Groupoidal.Hom.base f).base.map a) ≫
            (Grothendieck.Groupoidal.Hom.base g).base.map (Grothendieck.Groupoidal.Hom.fiber f) ≫
              Grothendieck.Groupoidal.Hom.fiber g)
    . intro x y t
      simp[Discrete.functor]
      exact Eq.symm (eq_of_comp_right_eq fun {X_1} ↦ congrFun rfl)
  map_id X := by
    simp[Discrete.functor]
    apply CategoryTheory.Functor.ext
    . intro a b f
      refine eq_of_comp_right_eq fun {X_1} h ↦ rfl
    . intro x
      simp[Discrete.functor]
      congr
      simp[Functor.id,Grpd.forgetToCat]

def Diag : PGrpd ⥤ BPGrpd where
  obj x := {base := x, fiber := x.fiber}
  map f := {base := f, fiber := f.fiber}
  map_comp {X Y Z} f g:= by
    simp[CategoryStruct.comp,Grothendieck.Groupoidal.comp,Grothendieck.comp]

def Refl : PGrpd ⥤ PGrpd where
  obj x := {base := Grpd.of (CategoryTheory.Discrete (x.fiber ⟶ x.fiber)), fiber := { as := 𝟙 x.fiber}}
  map {X Y} f := by
    fconstructor
    . exact Discrete.functor (fun g => {as := (inv f.fiber ≫ f.base.map g ≫ f.fiber)})
    . refine eqToHom ?_
      simp[Grpd.forgetToCat]
  map_id X := by
    simp[Discrete.functor,CategoryStruct.id,Grothendieck.id]
    congr 1
    . apply CategoryTheory.Functor.ext
      . intro x y f
        simp
        refine eq_of_comp_right_eq fun {X_1} h ↦ rfl
      . intro x
        simp[Grpd.forgetToCat]
    . simp [Grpd.forgetToCat]
      set eq := of_eq_true ..
      rw! [eq]
      simp
      refine eq_true ?_
      congr
      simp
  map_comp {X Y Z} f g := by
    simp[Discrete.functor,CategoryStruct.id,Grothendieck.id]
    congr 1
    . apply CategoryTheory.Functor.ext
      . intros a b w
        sorry
      . intro w
        simp[Grpd.forgetToCat]
    . simp[eqToHom_map]
      sorry

theorem Comute : Diag ⋙ Id = Refl ⋙ PGrpd.forgetToGrpd := by
  fapply CategoryTheory.Functor.ext
  . intro X
    simp[Diag,Id,Refl,PGrpd.forgetToGrpd,Grpd.of,Bundled.of]
    congr
  . intro X Y f
    simp[Diag,Id,Refl,PGrpd.forgetToGrpd]
    exact rfl

def R : PGrpd ⥤ Grothendieck.Groupoidal Id := (Grothendieck.Groupoidal.isPullback Id).lift Refl Diag Comute.symm

def K : Grothendieck.Groupoidal Id ⥤ Grpd := Grothendieck.Groupoidal.forget ⋙  BPGrpd.forgetToGrpd

theorem RKForget : R ⋙ K = PGrpd.forgetToGrpd := by
  simp [K,R,<- Functor.assoc,CategoryTheory.Functor.IsPullback.fac_right,Diag]
  fapply CategoryTheory.Functor.ext
  . intro X
    simp[Grothendieck.Groupoidal.base]
  . intro X Y f
    simp[Grothendieck.Groupoidal.base,Grothendieck.Groupoidal.Hom.base]
    exact rfl


/- Here I define the path groupoid and how it can be used to create identitys
Note that this is not the same as Id.
-/

def Path : Type u := ULift.{u} Bool

instance : Groupoid.{u,u} Path where
  Hom x y := PUnit
  id := fun _ => PUnit.unit
  comp := by intros; fconstructor
  inv := fun _ => PUnit.unit
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

abbrev Paths (G : Type u) [Groupoid.{u,u} G] : Type u := (Path ⥤ G)

/- This should be able to be made into a groupoid but I am having trouble with leans instances-/
instance (G : Type u) [Groupoid G] : Category.{u,u} (Paths G) := by
  exact Functor.category

def Path_Refl (G : Type u) [Groupoid G] : G ⥤ (Paths G) where
  obj x := by
    fconstructor
    fconstructor
    . exact fun _ => x
    . exact fun _ => 𝟙 x
    . exact congrFun rfl
    . simp
  map f := by
    fconstructor
    . intro x
      exact f
    . simp

def PreJ (G : Type u) [Groupoid G]  : Paths G ⥤ G := by
  fconstructor
  fconstructor
  . intro p
    refine p.obj { down := false }
  . intros X Y f
    refine f.app ?_
  . exact congrFun rfl
  . simp

theorem PreJLift  (G : Type u) [Groupoid G] : (Path_Refl G) ⋙ (PreJ G) = 𝟭 G := by
  simp [Path_Refl,PreJ,Functor.comp,Functor.id]

end Id

section Contract
/-
At some point I think we will need to contract groupoids along there isomorphisms. In this sections
I define how to do that.
-/

variable {C : Type u} [Category C] (a b : C) (f : a ⟶ b) [iso : IsIso f]

inductive ContractBase : Type u where
  | inc (x : {x : C // x ≠ a ∧ x ≠ b}) : ContractBase
  | p : ContractBase

def ContractHom (x y : ContractBase a b) : Type := match x,y with
  | ContractBase.inc t, ContractBase.inc u => t.val ⟶ u.val
  | ContractBase.inc t, ContractBase.p => t.val ⟶ a
  | ContractBase.p , ContractBase.inc t => b ⟶ t.val
  | ContractBase.p, ContractBase.p => b ⟶ a

def ContractHomId (x : ContractBase a b) : ContractHom a b x x := match x with
  | ContractBase.inc t => 𝟙 t.val
  | ContractBase.p => inv f

def ContractHomComp {x y z : ContractBase a b} (g : ContractHom a b x y) (h : ContractHom a b y z) :
  ContractHom a b x z := match x,y,z with
  | ContractBase.inc _, ContractBase.inc _, ContractBase.inc _ => g ≫ h
  | ContractBase.inc _, ContractBase.inc _, ContractBase.p => g ≫ h
  | ContractBase.inc _, ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
  | ContractBase.inc _, ContractBase.p, ContractBase.p => g ≫ f ≫  h
  | ContractBase.p , ContractBase.inc _, ContractBase.inc _ => g ≫ h
  | ContractBase.p , ContractBase.inc _, ContractBase.p => g ≫ h
  | ContractBase.p , ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
  | ContractBase.p , ContractBase.p, ContractBase.p => g ≫ f ≫ h

instance ic (iso : IsIso f) : Category (ContractBase a b) where
  Hom := ContractHom a b
  id := ContractHomId a b f
  comp := ContractHomComp a b f
  id_comp := by
    intros x y g
    cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
  comp_id := by
    intros x y g
    cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
  assoc := by
    intros w x y z g h i
    cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
end Contract
section GrpdContract

variable {G : Type u} [Groupoid G]

def Grpd.Contract (a b : G) : Type u := ContractBase a b

instance icc {a b : G} (f : a ⟶ b) : Category (Grpd.Contract a b) := ic a b f (isIso_of_op f)

instance {a b : G} (f : a ⟶ b) : Groupoid (Grpd.Contract a b) where
    Hom := ContractHom a b
    id := ContractHomId a b f
    comp := ContractHomComp a b f
    id_comp := by
      intros x y g
      cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
    comp_id := by
      intros x y g
      cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
    assoc := by
      intros w x y z g h i
      cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
    inv {a b} g := by
      cases a <;> cases b
      . dsimp[Quiver.Hom, ContractHom]
        dsimp[ContractHom] at g
        exact inv g
      . dsimp[Quiver.Hom, ContractHom]
        dsimp[ContractHom] at g
        exact inv (g ≫ f)
      . dsimp[Quiver.Hom, ContractHom]
        dsimp[ContractHom] at g
        exact inv (f ≫ g)
      . dsimp[Quiver.Hom, ContractHom]
        dsimp[ContractHom] at g
        exact (inv f) ≫ (inv g) ≫ (inv f)
    inv_comp {a b} g := sorry
    comp_inv := by sorry

def CTtoGrpd {a b : G} (f : a ⟶ b) : Grpd := by
  refine @Grpd.of (Grpd.Contract a b) ?_
  exact instGroupoidContractOfHom f

end GrpdContract

section ContractMap

-- def PJ : Grothendieck.Groupoidal Id ⥤ PGrpd where
--   obj x := by
--     rcases x with ⟨base,fiber⟩
--     rcases base with ⟨pg,p2⟩
--     rcases pg with ⟨base,p1⟩
--     simp[Grpd.forgetToCat] at p2 p1
--     fconstructor
--     . refine CTtoGrpd ?_ (G := base) (a := p1) (b := p2)
--       simp[Grpd.forgetToCat,Id] at fiber
--       rcases fiber with ⟨f⟩
--       simp[Grothendieck.Groupoidal.base,Grothendieck.Groupoidal.fiber] at f
--       exact f
--     . simp[Grpd.forgetToCat,CTtoGrpd,Grpd.Contract]
--       exact ContractBase.p
--   map {x y} F := by
--     simp[Quiver.Hom]
--     rcases F with ⟨base,fiber⟩
--     rcases base with ⟨pg,p2⟩
--     rcases pg with ⟨base,p1⟩
--     simp[Grpd.forgetToCat] at p2 p1
--     fconstructor
--     . fconstructor
--       fconstructor
--       . intro x
--         cases x
--         rename_i x'
--         rcases x' with ⟨x',p⟩
--         fconstructor
--         fconstructor
--         . refine base.obj x'
--         . simp

end ContractMap

section Poly
/-
In this section I am trying to move the previous results about groupoids to the
category of contexts
-/



/-
yonedaCategoryEquiv
-/
#check GroupoidModel.yonedaCategoryEquiv
/-
This is the equivelant of Id above
-/

def Id' : GroupoidModel.U.ext (GroupoidModel.π.{u,u}) ⟶ GroupoidModel.U.{u,u} := by
  dsimp[GroupoidModel.U.ext,GroupoidModel.U,GroupoidModel.Ctx.ofCategory]
  refine AsSmall.up.map ?_
  dsimp [Quiver.Hom]
  refine Core.functorToCore ?_
  refine ?_ ⋙ AsSmall.up
  refine ?_ ⋙ Id
  dsimp [BPGrpd]
  let F : (GroupoidModel.Ctx.toGrpd.obj GroupoidModel.E) ⥤ PGrpd := by
    dsimp[GroupoidModel.E,GroupoidModel.Ctx.ofCategory]
    refine ?_ ⋙ Core.inclusion PGrpd
    refine Core.map' ?_
    exact AsSmall.down
  let h : F ⋙ PGrpd.forgetToGrpd = (GroupoidModel.U.classifier GroupoidModel.π) := by
    exact rfl
  rw[<-h]
  exact Grothendieck.Groupoidal.pre PGrpd.forgetToGrpd F

def Refl' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.E.{u,u} := by
  dsimp[GroupoidModel.E, GroupoidModel.Ctx.ofCategory]
  refine AsSmall.up.map ?_
  dsimp[Quiver.Hom]
  refine Core.map' ?_
  refine AsSmall.down ⋙ ?_ ⋙ AsSmall.up
  exact Refl

/- Lean is gas lighting me -/
def Diag' : GroupoidModel.E.{v,u} ⟶ GroupoidModel.U.ext (GroupoidModel.π.{v,u}) := by
  refine IsPullback.lift (GroupoidModel.IsPullback.SmallU.isPullback_disp_π.{v,u} (GroupoidModel.π.{v,u})) ?_ ?_ ?_
  . refine eqToHom sorry
  . refine eqToHom sorry
  . simp

-- theorem Comm : Refl'.{u} ≫ GroupoidModel.π.{u,u} = Diag'.{u} ≫ Id'.{u} := by sorry

-- def R' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.U.ext.{u,u} Id' := by
--   refine IsPullback.lift (GroupoidModel.IsPullback.SmallU.isPullback_disp_π.{u,u} Id'.{u} (Γ := GroupoidModel.U.ext GroupoidModel.π.{u,u}) ) ?_ ?_ ?_


set_option pp.universes true
#check Quiver.comp


-- #check GroupoidModel.smallU.Tm
-- #check Core.functorToCore
-- #check BPGrpd.FirstPointed
-- #check GroupoidModel.smallU.ext

def Tmm : Psh.{u + 2, u + 2} GroupoidModel.Ctx.{u + 1} := by
    refine yoneda.obj ?_
    apply GroupoidModel.smallU.ext.{u,u}
    apply (GroupoidModel.smallU.tp.{u,u})

#check GroupoidModel.yonedaCategoryEquiv
#check Functor.FullyFaithful.preimage


def Tmm_is_BPGrpd : Tmm.{u} ⟶ yoneda.obj (GroupoidModel.Ctx.ofGrpd.obj (Grpd.of (BPGrpd.{u}))) := by
    dsimp [Tmm]
    refine yoneda.map (AsSmall.up.map ?_)
    dsimp [BPGrpd]
    refine Grpd.homOf ?_
    dsimp [GroupoidModel.π,GroupoidModel.yonedaCategoryEquiv,GroupoidModel.Ctx.homOfFunctor]
    rw [Yoneda.fullyFaithful.preimage_map]
    let F : (GroupoidModel.Ctx.toGrpd.obj GroupoidModel.E.{u, u+1}) ⥤ PGrpd.{u,u} := by
      dsimp[GroupoidModel.E,GroupoidModel.Ctx.ofCategory]
      refine ?_ ⋙ Core.inclusion PGrpd
      refine Core.map' ?_
      exact AsSmall.down
    let h : (GroupoidModel.toCoreAsSmallEquiv (AsSmall.up.map (Grpd.homOf (Core.map' (AsSmall.down.{u, u+1, u+1} ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up.{u, u+1, u+1}))))) = F ⋙ PGrpd.forgetToGrpd.{u,u} := by
       exact rfl
    rw! [h]
    refine ?_ ⋙ Grothendieck.Groupoidal.pre PGrpd.forgetToGrpd.{u,u} F ⋙ ?_
    . exact
      Functor.id.{u + 1, u + 1}
        (Grothendieck.Groupoidal.{u + 1, u + 1, u, u}
          (Functor.comp.{u + 1, u, u, u + 1, u + 1, u + 1} F PGrpd.forgetToGrpd.{u, u}))
    . sorry -- Even with universes I can not see how this is not ID


def GroupoidModel.smallU.IdBase : NaturalModelBase.NaturalModelIdBase GroupoidModel.smallU.{u,u} where
  Tmm := Tmm
  p1 := by
    apply GroupoidModel.smallU.var.{u,u}
  p2 := by
    refine yoneda.map ?_
    apply GroupoidModel.smallU.disp.{u,u} (GroupoidModel.smallU.tp.{u,u})
  Tm_Pullback := by
    apply GroupoidModel.smallU.disp_pullback.{u,u}
  Id := by
    refine Tmm_is_BPGrpd.{u} ≫ ?_
    refine yoneda.map ?_
    fconstructor
    dsimp[GroupoidModel.U.ext,GroupoidModel.U,GroupoidModel.Ctx.ofCategory,Quiver.Hom]
    refine Core.functorToCore ?_
    refine ?_ ⋙ AsSmall.up
    refine ?_ ⋙ Id
    sorry -- I think some how the functor itself is in the wrong universe
  Refl := sorry
