import GroupoidModel.Groupoids.NaturalModelBase

import GroupoidModel.Syntax.NaturalModel

import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone

import SEq.Tactic.DepRewrite

universe w v u v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory

open Functor.Groupoidal


-- def PGrpd.inc (G : Type) [Groupoid G] : G ⥤ PGrpd  where
--   obj x := {base := Grpd.of G,fiber := x}
--   map f := {base := Functor.id G, fiber := f}
--   map_comp {X Y Z} f g := by
--     fapply Functor.Grothendieck.Hom.ext
--     · simp [Grpd.comp_eq_comp]
--     · simp [Grpd.forgetToCat]

-- namespace GrothendieckPointedCategories

-- abbrev BPCat := Grothendieck (PCat.forgetToCat)

-- namespace BPCat

-- abbrev forgetToCat : BPCat ⥤ Cat where
--   obj x := x.base.base
--   map f := f.base.base
--   map_comp := by
--     intros x y z f g
--     exact rfl

-- abbrev FirstPointed  : BPCat ⥤ PCat := Grothendieck.forget _

-- def SecondPointed : BPCat ⥤ PCat where
--   obj x := {base := x.base.base, fiber := x.fiber}
--   map f := {base := f.base.base, fiber := f.fiber}
--   map_comp := by
--     intros x y z f g
--     exact rfl

-- /- This needs a better name but I cant come up with one now-/
-- theorem Comutes : FirstPointed ⋙ PCat.forgetToCat = SecondPointed ⋙ PCat.forgetToCat := by
--   simp[FirstPointed,SecondPointed,PCat.forgetToCat,Functor.comp]


-- def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PCat.forgetToCat.{u,v} PCat.forgetToCat.{u,v}
--   := @CategoryTheory.Grothendieck.isPullback PCat _ (PCat.forgetToCat)

-- end BPCat

abbrev BPGrpd := ∫ PGrpd.forgetToGrpd

namespace BPGrpd

abbrev snd : BPGrpd ⥤ PGrpd := Functor.Groupoidal.forget

abbrev forgetToGrpd : BPGrpd ⥤ Grpd := snd ⋙ PGrpd.forgetToGrpd

def fst : BPGrpd ⥤ PGrpd := toPGrpd _

/-- The commutative square
  BPGrpd ----> PGrpd
    |            |
    |            |
    |            |
    |            |
    V            V
   PGrpd ----> Grpd
-/
theorem snd_forgetToGrpd : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ PGrpd.forgetToGrpd := by
  simp [fst, snd, toPGrpd_forgetToGrpd]

/- BPGrpd is the pullback of PGrpd.forgetToGrpd with itself -/
def isPullback : Functor.IsPullback fst.{u,v} snd.{u,v} PGrpd.forgetToGrpd.{u,v}
    PGrpd.forgetToGrpd.{u,v} := by
  apply @Functor.Groupoidal.isPullback PGrpd _ (PGrpd.forgetToGrpd)

-- -- TODO: docstring + why is it called `inc`?
-- def inc (G : Type) [Groupoid G] : G ⥤ BPGrpd := by
--   fapply isPullback.lift
--   . exact PGrpd.inc G
--   . exact PGrpd.inc G
--   . simp

end BPGrpd

end CategoryTheory

namespace GroupoidModel

open CategoryTheory Functor.Groupoidal

namespace FunctorOperation

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

/-- The identity type former takes a bipointed groupoid `((A,a0),a1)` to the set of isomorphisms
between its two given points `A(a0,a1)`.
Here `A = x.base.base`, `a0 = x.base.fiber` and `a1 = x.fiber`. -/
def idObj (x : BPGrpd) : Grpd := Grpd.of (CategoryTheory.Discrete (x.base.fiber ⟶ x.fiber))

/-- The identity type former takes a morphism of bipointed groupoids
`((F,f0),f1) : ((A,a0),a1) ⟶ ((B,b0),b1)`
to the function `A(a0,a1) → B(b0,b1)` taking `g : a0 ≅ a1` to `f0⁻¹ ⋙ F g ⋙ f1` where
`f0⁻¹ : b0 ⟶ F a0`, `F g : F a0 ⟶ F a1` and `f1 : F a1 ⟶ b1`. -/
def idMap {x y : BPGrpd} (f : x ⟶ y) : idObj x ⥤ idObj y :=
  Discrete.functor (fun g => ⟨ inv f.base.fiber ≫ (f.base.base.map g) ≫ f.fiber ⟩)

lemma Discrete.functor_ext' {X C : Type*} [Category C] {F G : X → C} (h : ∀ x : X, F x = G x) :
    Discrete.functor F = Discrete.functor G := by
  have : F = G := by aesop
  subst this
  rfl

lemma Discrete.functor_eq {X C : Type*} [Category C] {F : Discrete X ⥤ C} :
    F = Discrete.functor fun x ↦ F.obj ⟨x⟩ := by
  fapply CategoryTheory.Functor.ext
  · aesop
  · intro x y f
    cases x ; rcases f with ⟨⟨h⟩⟩
    cases h
    simp

lemma Discrete.functor_ext {X C : Type*} [Category C] (F G : Discrete X ⥤ C)
    (h : ∀ x : X, F.obj ⟨x⟩ = G.obj ⟨x⟩) :
    F = G :=
  calc F
    _ = Discrete.functor (fun x => F.obj ⟨x⟩) := Discrete.functor_eq
    _ = Discrete.functor (fun x => G.obj ⟨x⟩) := Discrete.functor_ext' h
    _ = G := Discrete.functor_eq.symm

lemma Discrete.ext {X : Type*} {x y : Discrete X} (h : x.as = y.as) : x = y := by
  cases x; cases h
  rfl

/-- The identity type formation rule, equivalently viewed as a functor. -/
@[simps]
def id : BPGrpd.{u,u} ⥤ Grpd.{u,u} where
  obj := idObj
  map := idMap
  map_id X := by
    apply Discrete.functor_ext
    intro x
    apply Discrete.ext
    dsimp only [idMap, Grpd.forgetToCat]
    aesop
  map_comp {X Y Z} f g := by
    apply Discrete.functor_ext
    intro a
    apply Discrete.ext
    dsimp only [idMap, Grpd.forgetToCat]
    aesop

/--
The diagonal functor into the pullback.
It creates a second copy of the point from the input pointed groupoid.

This version of `diag` is used for better definitional reduction.
-/
def diag : PGrpd ⥤ BPGrpd where
  obj x := objMk x x.fiber
  map f := homMk f f.fiber
  map_comp {X Y Z} f g:= by
    fapply Hom.ext
    · simp
    · simp [Grpd.forgetToCat]

/--
This version of `diag` is used for functor equational reasoning.
-/
def diag' : PGrpd ⥤ BPGrpd :=
  BPGrpd.isPullback.lift (𝟭 _) (𝟭 _) rfl

lemma diag_eq_diag' : diag = diag' :=
  BPGrpd.isPullback.lift_uniq _ _ _ rfl rfl

def reflObjFiber (x : PGrpd) : Discrete (x.fiber ⟶ x.fiber) := ⟨𝟙 x.fiber⟩

def refl : PGrpd ⥤ PGrpd :=
  PGrpd.functorTo (diag ⋙ id) reflObjFiber (fun f => Discrete.eqToHom (by
    simp [idMap, diag, reflObjFiber, Grpd.forgetToCat]))
    (by simp)
    (by intros; simp [Discrete.eqToHom, eqToHom_map])

theorem refl_forgetToGrpd : refl ⋙ PGrpd.forgetToGrpd = diag ⋙ id := rfl

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
def comparison : PGrpd ⥤ ∫ id :=
  (isPullback id).lift refl diag refl_forgetToGrpd

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
theorem comparison_comp_forget_comp_forgetToGrpd : comparison ⋙ forget ⋙ BPGrpd.forgetToGrpd =
    PGrpd.forgetToGrpd := by
  simp only [comparison, diag, ← Functor.assoc, Functor.IsPullback.fac_right]
  fapply CategoryTheory.Functor.ext
  . intro X
    simp
  . intro X Y f
    simp


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
end FunctorOperation

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

/-
In this section I am trying to move the previous results about groupoids to the
category of contexts
-/


def Refl' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.E.{u,u} :=
  AsSmall.up.map (𝟭 (Core (AsSmall PGrpd)))

namespace smallUId

lemma isKernelPair : IsKernelPair smallU.tp.{u} ym(Ctx.homOfFunctor BPGrpd.fst)
    ym(Ctx.homOfFunctor BPGrpd.snd) :=
  Functor.map_isPullback yoneda (IsPullback.isPullback_homOfFunctor _ _ _ _ BPGrpd.isPullback)

def Id : y(Ctx.ofCategory BPGrpd.{u,u}) ⟶ smallU.Ty.{u} :=
  ym(Ctx.homOfFunctor FunctorOperation.id)

def refl : smallU.Tm.{u} ⟶ smallU.Tm.{u} :=
  ym(Ctx.homOfFunctor FunctorOperation.refl)

lemma refl_tp : refl ≫ smallU.tp.{u} = isKernelPair.lift (𝟙 smallU.Tm) (𝟙 smallU.Tm) rfl ≫ Id := by
  convert_to _ = ym(Ctx.homOfFunctor (BPGrpd.isPullback.lift (𝟭 PGrpd.{u,u}) (𝟭 PGrpd.{u,u}) rfl)) ≫ Id
  · congr 1
    apply isKernelPair.hom_ext
    · erw [isKernelPair.lift_fst]
      simp [← Functor.map_comp, ← Ctx.homOfFunctor_comp, BPGrpd.isPullback.fac_left, E]
    · erw [isKernelPair.lift_snd]
      simp [← Functor.map_comp, ← Ctx.homOfFunctor_comp, BPGrpd.isPullback.fac_right, E]
  · simp only [smallU_Ty, smallU_Tm, refl, smallU_tp, π, ← Functor.map_comp, ←
      Ctx.homOfFunctor_comp, FunctorOperation.refl_forgetToGrpd, FunctorOperation.diag_eq_diag',
      FunctorOperation.diag', Id]
    rfl

lemma i_isPullback : IsPullback ym(Ctx.homOfFunctor (toPGrpd FunctorOperation.id))
    ym(Ctx.homOfFunctor Functor.Groupoidal.forget) smallU.tp Id :=
  Functor.map_isPullback yoneda
    (IsPullback.isPullback_homOfFunctor _ _ _ _ (isPullback FunctorOperation.id))

def smallUIdElimBase : NaturalModelBase.IdElimBase smallU.{u} where
  k := y(Ctx.ofCategory BPGrpd.{u,u})
  k1 := ym(Ctx.homOfFunctor BPGrpd.fst)
  k2 := ym(Ctx.homOfFunctor BPGrpd.snd)
  isKernelPair := isKernelPair
  Id := Id
  refl := refl
  refl_tp := refl_tp
  i := y(Ctx.ofCategory (∫ FunctorOperation.id.{u}))
  i1 := ym(Ctx.homOfFunctor (toPGrpd _))
  i2 := ym(Ctx.homOfFunctor forget)
  i_isPullback := i_isPullback

-- TODO: make namespaces consistent with Sigma file
def smallUId : NaturalModelBase.Id smallU.{u} := {
  smallUIdElimBase with
  weakPullback := {
    w := sorry -- this should be completed automatically
    lift := sorry
    fac_left := sorry
    fac_right := sorry
  }}

-- def smallUIdBase : NaturalModelBase.Id smallU.{u} where
--   k := y(smallU.ext.{u} smallU.tp.{u})
--   k1 := smallU.var smallU.tp
--   k2 := ym(smallU.disp smallU.tp)
--   isKernelPair := smallU.disp_pullback _
--   Id := Id
--   refl := sorry
--   refl_tp := sorry
--   i := sorry
--   i1 := sorry
--   i2 := sorry
--   i_isPullback := sorry
--   weakPullback := sorry

end smallUId

end GroupoidModel
