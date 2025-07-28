import GroupoidModel.Groupoids.NaturalModelBase

import GroupoidModel.Syntax.NaturalModel

import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone

import SEq.Tactic.DepRewrite

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

open GroupoidModel

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

namespace BPGrpd


abbrev FirstPointed  : BPGrpd ⥤ PGrpd := @Grothendieck.Groupoidal.forget _ _ (PGrpd.forgetToGrpd)

abbrev forgetToGrpd : BPGrpd ⥤ Grpd := FirstPointed ⋙ PGrpd.forgetToGrpd


def SecondPointed : BPGrpd ⥤ PGrpd where
  obj x := {base := x.base.base, fiber := x.fiber}
  map f := {base := f.base.base, fiber := f.fiber}
  map_comp := by
    intros x y z f g
    exact rfl

/- Same thing with this name-/
theorem Comutes : FirstPointed ⋙ PGrpd.forgetToGrpd = SecondPointed ⋙ PGrpd.forgetToGrpd := by
  simp[FirstPointed,SecondPointed,PGrpd.forgetToGrpd,Functor.comp]
  -- exact Prod.mk_inj.mp rfl

/- BPGrpd is the pullback of PGrpd.forgetToGrpd with itself -/
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

def Id: BPGrpd.{u,u} ⥤ Grpd.{u,u} where
  obj (x: BPGrpd) := Grpd.of (CategoryTheory.Discrete (x.base.fiber ⟶ x.fiber))
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
      simp[Grpd.forgetToCat]
      exact rfl

/-
JH: This should be given automatically by the pullback universal property of BPGrpd.
But I think this should be automatically produced from the spec `NaturalModelIdBase.pb_isPullback`
-/
def Diag : PGrpd ⥤ BPGrpd where
  obj x := {base := x, fiber := x.fiber}
  map f := {base := f, fiber := f.fiber}
  map_comp {X Y Z} f g:= by
    simp[CategoryStruct.comp,Grothendieck.Groupoidal.comp,Grothendieck.comp]

/-
JH: maybe use `PGrpd.functorTo` or even `Grothendieck.map`?
-/
def Refl : PGrpd ⥤ PGrpd where
  obj x := {base := Grpd.of (CategoryTheory.Discrete (x.fiber ⟶ x.fiber)), fiber := { as := 𝟙 x.fiber}}
  map {X Y} f := { base := Discrete.functor fun g ↦ { as := inv f.fiber ≫ f.base.map g ≫ f.fiber },
                   fiber := eqToHom sorry }
  map_id X := by
    simp[Discrete.functor,CategoryStruct.id,Grothendieck.id]
    congr 1
    . apply CategoryTheory.Functor.ext
      . intro x y f
        refine eq_of_comp_right_eq fun {X_1} h ↦ rfl
      . intro x
        simp[Grpd.forgetToCat]
    . simp [Grpd.forgetToCat]
      sorry
      -- set eq := of_eq_true ..
      -- rw! [eq]
      -- simp
      -- refine eq_true ?_
      -- congr
      -- simp
  map_comp {X Y Z} f g := by
    simp[Discrete.functor]
    congr 1
    . apply CategoryTheory.Functor.ext
      . intros a b w
        sorry
      . intro w
        simp[Grpd.forgetToCat]
        exact rfl
    . simp[eqToHom_map]
      sorry

theorem Comute : Diag ⋙ Id = Refl ⋙ PGrpd.forgetToGrpd := sorry
-- by
  -- fapply CategoryTheory.Functor.ext
  -- . intro X
  --   simp[Diag,Id,Refl,PGrpd.forgetToGrpd,Grpd.of,Bundled.of]
  --   congr
  -- . intro X Y f
  --   simp[Diag,Id,Refl,PGrpd.forgetToGrpd]
  --   exact rfl

/- This is the universal lift
            Refl
PGrpd ------------>
 |----> ∫Id -----> PGrpd
 |  R   |            |
 |      |            |
 Diag   |            | forget
 |      |            |
 |      V            V
 ---> BPGrpd -----> Grpd
              Id
-/
def R : PGrpd ⥤ Grothendieck.Groupoidal Id := (Grothendieck.Groupoidal.isPullback Id).lift Refl Diag Comute.symm

/- This is the composition

PGrpd
 |----> ∫Id
 |  R   |
 |      |
 Diag   | forget
 |      |
 |      V
 ---> BPGrpd
        |
        |
        | BPGrpd.forgetToGrpd
        |
        V
      Grpd
-/
-- TODO : consider removal?
-- def K : Grothendieck.Groupoidal Id ⥤ Grpd := Grothendieck.Groupoidal.forget ⋙  BPGrpd.forgetToGrpd

/- This is the universal lift
            Refl
PGrpd ------------>
 |----> ∫Id -----> PGrpd
 |  R   |            |
 |      |            |
 Diag   |            | forget
 |      |            |
 |      V            V
 ---> BPGrpd -----> Grpd
              Id
-/
theorem RKForget : R ⋙ Grothendieck.Groupoidal.forget ⋙ BPGrpd.forgetToGrpd =
    PGrpd.forgetToGrpd := by
  simp [R,<- Functor.assoc,CategoryTheory.Functor.IsPullback.fac_right,Diag]
  fapply CategoryTheory.Functor.ext
  . intro X
    simp[Grothendieck.Groupoidal.base]
  . intro X Y f
    simp[Grothendieck.Groupoidal.base,Grothendieck.Groupoidal.Hom.base]


-- /- Here I define the path groupoid and how it can be used to create identities
-- Note that this is not the same as Id.
-- -/

-- def Path : Type u := ULift.{u} Bool

-- instance : Groupoid.{u,u} Path where
--   Hom x y := PUnit
--   id := fun _ => PUnit.unit
--   comp := by intros; fconstructor
--   inv := fun _ => PUnit.unit
--   id_comp := by intros; rfl
--   comp_id := by intros; rfl
--   assoc := by intros; rfl

-- abbrev Paths (G : Type u) [Groupoid.{u,u} G] : Type u := (Path ⥤ G)

-- /- This should be able to be made into a groupoid but I am having trouble with leans instances-/
-- instance (G : Type u) [Groupoid G] : Category.{u,u} (Paths G) := by
--   exact Functor.category

-- def Path_Refl (G : Type u) [Groupoid G] : G ⥤ (Paths G) where
--   obj x := by
--     fconstructor
--     fconstructor
--     . exact fun _ => x
--     . exact fun _ => 𝟙 x
--     . exact congrFun rfl
--     . simp
--   map f := by
--     fconstructor
--     . intro x
--       exact f
--     . simp

-- def PreJ (G : Type u) [Groupoid G]  : Paths G ⥤ G := by
--   fconstructor
--   fconstructor
--   . intro p
--     refine p.obj { down := false }
--   . intros X Y f
--     refine f.app ?_
--   . exact congrFun rfl
--   . simp

-- theorem PreJLift  (G : Type u) [Groupoid G] : (Path_Refl G) ⋙ (PreJ G) = 𝟭 G := by
--   simp [Path_Refl,PreJ,Functor.comp,Functor.id]

end Id

-- section Contract
-- /-
-- At some point I think we will need to contract groupoids along there isomorphisms. In this sections
-- I define how to do that.
-- -/

-- variable {C : Type u} [Category C] (a b : C) (f : a ⟶ b) [iso : IsIso f]

-- inductive ContractBase : Type u where
--   | inc (x : {x : C // x ≠ a ∧ x ≠ b}) : ContractBase
--   | p : ContractBase

-- def ContractHom (x y : ContractBase a b) : Type := match x,y with
--   | ContractBase.inc t, ContractBase.inc u => t.val ⟶ u.val
--   | ContractBase.inc t, ContractBase.p => t.val ⟶ a
--   | ContractBase.p , ContractBase.inc t => b ⟶ t.val
--   | ContractBase.p, ContractBase.p => b ⟶ a

-- def ContractHomId (x : ContractBase a b) : ContractHom a b x x := match x with
--   | ContractBase.inc t => 𝟙 t.val
--   | ContractBase.p => inv f

-- def ContractHomComp {x y z : ContractBase a b} (g : ContractHom a b x y) (h : ContractHom a b y z) :
--   ContractHom a b x z := match x,y,z with
--   | ContractBase.inc _, ContractBase.inc _, ContractBase.inc _ => g ≫ h
--   | ContractBase.inc _, ContractBase.inc _, ContractBase.p => g ≫ h
--   | ContractBase.inc _, ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
--   | ContractBase.inc _, ContractBase.p, ContractBase.p => g ≫ f ≫  h
--   | ContractBase.p , ContractBase.inc _, ContractBase.inc _ => g ≫ h
--   | ContractBase.p , ContractBase.inc _, ContractBase.p => g ≫ h
--   | ContractBase.p , ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
--   | ContractBase.p , ContractBase.p, ContractBase.p => g ≫ f ≫ h

-- instance ic (iso : IsIso f) : Category (ContractBase a b) where
--   Hom := ContractHom a b
--   id := ContractHomId a b f
--   comp := ContractHomComp a b f
--   id_comp := by
--     intros x y g
--     cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--   comp_id := by
--     intros x y g
--     cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--   assoc := by
--     intros w x y z g h i
--     cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
-- end Contract
-- section GrpdContract

-- variable {G : Type u} [Groupoid G]

-- def Grpd.Contract (a b : G) : Type u := ContractBase a b

-- instance icc {a b : G} (f : a ⟶ b) : Category (Grpd.Contract a b) := ic a b f (isIso_of_op f)

-- instance {a b : G} (f : a ⟶ b) : Groupoid (Grpd.Contract a b) where
--     Hom := ContractHom a b
--     id := ContractHomId a b f
--     comp := ContractHomComp a b f
--     id_comp := by
--       intros x y g
--       cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--     comp_id := by
--       intros x y g
--       cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--     assoc := by
--       intros w x y z g h i
--       cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
--     inv {a b} g := by
--       cases a <;> cases b
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv g
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv (g ≫ f)
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv (f ≫ g)
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact (inv f) ≫ (inv g) ≫ (inv f)
--     inv_comp {a b} g := sorry
--     comp_inv := by sorry

-- def CTtoGrpd {a b : G} (f : a ⟶ b) : Grpd := by
--   refine @Grpd.of (Grpd.Contract a b) ?_
--   exact instGroupoidContractOfHom f

-- end GrpdContract

-- section ContractMap

-- -- def PJ : Grothendieck.Groupoidal Id ⥤ PGrpd where
-- --   obj x := by
-- --     rcases x with ⟨base,fiber⟩
-- --     rcases base with ⟨pg,p2⟩
-- --     rcases pg with ⟨base,p1⟩
-- --     simp[Grpd.forgetToCat] at p2 p1
-- --     fconstructor
-- --     . refine CTtoGrpd ?_ (G := base) (a := p1) (b := p2)
-- --       simp[Grpd.forgetToCat,Id] at fiber
-- --       rcases fiber with ⟨f⟩
-- --       simp[Grothendieck.Groupoidal.base,Grothendieck.Groupoidal.fiber] at f
-- --       exact f
-- --     . simp[Grpd.forgetToCat,CTtoGrpd,Grpd.Contract]
-- --       exact ContractBase.p
-- --   map {x y} F := by
-- --     simp[Quiver.Hom]
-- --     rcases F with ⟨base,fiber⟩
-- --     rcases base with ⟨pg,p2⟩
-- --     rcases pg with ⟨base,p1⟩
-- --     simp[Grpd.forgetToCat] at p2 p1
-- --     fconstructor
-- --     . fconstructor
-- --       fconstructor
-- --       . intro x
-- --         cases x
-- --         rename_i x'
-- --         rcases x' with ⟨x',p⟩
-- --         fconstructor
-- --         fconstructor
-- --         . refine base.obj x'
-- --         . simp

-- end ContractMap

section Poly
/-
In this section I am trying to move the previous results about groupoids to the
category of contexts
-/



/-
This is the equivelant of Id above
-/

-- TODO tidy up this definition. remove tactic mode + use yonedaCategoryEquiv
def Id' : y(GroupoidModel.U.ext (GroupoidModel.π.{u,u})) ⟶ smallU.Ty.{u,u} :=
  yonedaCategoryEquiv.symm (sorry)
  -- dsimp[GroupoidModel.U.ext,GroupoidModel.U,GroupoidModel.Ctx.ofCategory]
  -- refine AsSmall.up.map ?_
  -- dsimp [Quiver.Hom]
  -- refine Core.functorToCore ?_
  -- refine ?_ ⋙ AsSmall.up
  -- refine ?_ ⋙ Id
  -- dsimp [BPGrpd]
  -- let F : (GroupoidModel.Ctx.toGrpd.obj GroupoidModel.E) ⥤ PGrpd := by sorry
  --   -- dsimp[GroupoidModel.E,GroupoidModel.Ctx.ofCategory]
  --   -- refine ?_ ⋙ Core.inclusion PGrpd
  --   -- refine Core.map' ?_
  --   -- exact AsSmall.down
  -- let h : F ⋙ PGrpd.forgetToGrpd = (GroupoidModel.U.classifier GroupoidModel.π) := by sorry
  --   -- exact rfl
  -- rw[<-h]
  -- exact Grothendieck.Groupoidal.pre PGrpd.forgetToGrpd F

def Refl' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.E.{u,u} := by
  dsimp[GroupoidModel.E, GroupoidModel.Ctx.ofCategory]
  refine AsSmall.up.map ?_
  dsimp[Quiver.Hom]
  sorry
  -- refine Core.map' ?_
  -- refine AsSmall.down ⋙ ?_ ⋙ AsSmall.up
  -- exact Refl

/- Lean is gas lighting me -/
def Diag' : GroupoidModel.E.{v,u} ⟶ GroupoidModel.U.ext (GroupoidModel.π.{v,u}) := by
  refine IsPullback.lift (GroupoidModel.IsPullback.SmallU.isPullback_disp_π.{v,u} (GroupoidModel.π.{v,u})) ?_ ?_ ?_
  . refine eqToHom sorry
  . refine eqToHom sorry
  . simp



namespace smallUId

def id : Limits.pullback smallU.{v}.tp smallU.{v}.tp ⟶ smallU.{v}.Ty := sorry

def refl: smallU.{v}.Tm ⟶ smallU.{v}.Tm := sorry

def comm: Limits.pullback.lift (𝟙 smallU.Tm) (𝟙 smallU.Tm) rfl ≫ id = refl ≫ smallU.tp := sorry

-- TODO: make sure universe levels are most general
-- TODO: make namespaces consistent with Sigma file
def smallUIdBase : NaturalModelBase.NaturalModelIdBase smallU.{u,u} where
  pb := y(GroupoidModel.U.ext GroupoidModel.π.{u,u})
  p1 := sorry -- smallU.{u,u}.var GroupoidModel.π.{u,u}
  p2 := sorry -- ym(smallU.{u,u}.disp GroupoidModel.π.{u,u})
  pb_isPullback := sorry
  Id := Id'
  refl := sorry
  Id_comm := sorry
