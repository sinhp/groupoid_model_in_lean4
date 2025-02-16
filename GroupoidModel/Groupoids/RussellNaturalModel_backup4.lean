import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Core

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.
-/

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck

/-
Grpd.{u, u} is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).

We want our context category to be a small category so we will use
`AsSmall.{u}` for some large enough `u`
-/

namespace CategoryTheory

namespace IsPullback
variable {C : Type u₁} [Category.{v₁} C]

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Construct an `IsPullback` from an `IsPullback`
  and an isomorphism with the tip of the cone -/
theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
      IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := sorry

end IsPullback

instance asSmallGroupoid (Γ : Type w) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{max w u v} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

def Grpd.asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

namespace PGrpd

instance asSmallPointedGroupoid (Γ : Type w) [PointedGroupoid.{v} Γ] :
    PointedGroupoid.{max w v u, max w v u} (AsSmall.{max w v u} Γ) := {
  asSmallGroupoid.{w,v,u} Γ with
  pt := AsSmall.up.obj PointedGroupoid.pt}

def asSmallFunctor : PGrpd.{v, u} ⥤ PGrpd.{max w v u, max w v u} where
  obj Γ := PGrpd.of $ AsSmall.{max w v u} Γ
  map F := {
    toFunctor := AsSmall.down ⋙ F.toFunctor ⋙ AsSmall.up
    point := AsSmall.up.map F.point}


end PGrpd

namespace Core

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

@[simp]
theorem id_inv (X : C) :
    Iso.inv (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl

@[simp]
theorem comp_inv {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inv = g.inv ≫ f.inv :=
  rfl

def functor' (F : C ⥤ D) : Core C ⥤ Core D where
  obj := F.obj
  map f := {
    hom := F.map f.hom
    inv := F.map f.inv}
  map_id x := by
    simp only [Grpd.coe_of, id_hom, Functor.map_id, id_inv]
    congr 1
  map_comp f g := by
    simp only [Grpd.coe_of, comp_hom, Functor.map_comp, comp_inv]
    congr 1

lemma functor'_comp_inclusion (F : C ⥤ D) :
    functor' F ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (functor' F)

variable {Γ : Type u} [Groupoid.{v} Γ]

/-  A functor from a groupoid into a category is equivalent
    to a functor from the groupoid into the core -/
def functorToCoreEquiv : Γ ⥤ D ≃ Γ ⥤ Core D where
  toFun := functorToCore
  invFun := forgetFunctorToCore.obj
  left_inv _ := rfl
  right_inv _ := by
    simp [functorToCore, forgetFunctorToCore]
    apply Functor.ext
    · intro x y f
      simp only [inclusion, id_eq, Functor.comp_obj, Functor.comp_map,
        IsIso.Iso.inv_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      congr
    · intro 
      rfl 

end Core

  
namespace PGrpd

namespace IsPullback
def CAT :=
  Cat.of (Cat.{max (v+1) u, max (v+1) u})
def PCAT :=
  Cat.of (PCat.{max (v+1) u, max (v+1) u})
def GRPD :=
  Cat.of (Grpd.{max (v+1) u, max (v+1) u})
def PGRPD :=
  Cat.of (PGrpd.{max (v+1) u, max (v+1) u})
def grpd : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (ULift.{max (v+1) u + 1, max (v+1) u} (AsSmall.{u} Grpd.{v,v}))
def pgrpd : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (ULift.{max (v+1) u + 1, max (v+1) u} (AsSmall.{u} PGrpd.{v,v}))

abbrev grothendieckAsSmallFunctor :=
  Grothendieck $
    Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

def GROTH : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (ULift.{max u (v+1) + 1, max (v+1) u}
        grothendieckAsSmallFunctor.{v,u})

def PCATFORGETTOCAT : PCAT.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf PCat.forgetToCat.{max (v+1) u, max (v+1) u}
def PGRPDFORGETTOGRPD : PGRPD.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf PGrpd.forgetToGrpd.{max (v+1) u, max (v+1) u}
def pgrpdforgettogrpd : pgrpd.{v,u} ⟶ grpd.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor)
def grpdAsSmallFunctor : grpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ Grpd.asSmallFunctor.{max u (v+1)})
def pgrpdAsSmallFunctor : pgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1)})

def GROTHToPGRPD : GROTH.{v,u} ⟶ PCAT.{v,u} :=
  Cat.homOf (downFunctor ⋙ Grothendieck.toPCat _)
def GROTHFORGET : GROTH.{v,u} ⟶ grpd.{v,u} :=
  Cat.homOf (downFunctor ⋙ Grothendieck.forget _ ⋙ AsSmall.up ⋙ upFunctor)

def asSmallFunctorCompForgetToCat' :
    grpd.{v,u} ⥤ Cat.{max (v+1) u, max (v+1) u} :=
  downFunctor
    ⋙ AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

def asSmallFunctorCompForgetToCat : grpd.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf asSmallFunctorCompForgetToCat'

-- def lift {C : Type u₁} [Category.{v₁} C]
--   (F : C ⥤ Grpd.{v, u})
--   (G : C ⥤ PGrpd.{max w (v+1) (u+1), max w (v+1) (u+1)})
--   (h : F ⋙ Grpd.asSmallFunctor.{max w (v+1) (u+1), v, u}
--     = G ⋙ PGrpd.forgetToGrpd.{max w (v+1) (u+1), max w (v+1) (u+1)})
--     : C ⥤ PGrpd.{v,u} where
--   obj X :=
--     let x : (G ⋙ forgetToGrpd).obj X := (G.obj X).str.pt
--     let x' : Grpd.asSmallFunctor.obj (F.obj X) := ((eqToHom h.symm).app X).obj x
--     PGrpd.fromGrpd (F.obj X)
--       (AsSmall.down.obj.{v, u, max (max (u + 1) (v + 1)) w} x')
--   map {X Y} f := {
--     toFunctor := F.map f
--     point := sorry
--   }
--   --   let x : (G ⋙ forgetToGrpd).obj Y := (G.map f).str.pt
--   --   let x' : Grpd.asSmallFunctor.obj (F.obj X) := ((eqToHom h.symm).app X).obj x
--   --   PointedFunctor.of sorry
--   -- map_id := sorry
--   map_comp := sorry

def grothendieckAsSmallFunctorToPGrpd :
    grothendieckAsSmallFunctor.{v, u} ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max (v + 1) u} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}

def pGrpdToGrothendieckAsSmallFunctor :
    PGrpd.{v, v} ⥤ grothendieckAsSmallFunctor.{v,u} where
  obj x := {
    base := Grpd.of x
    fiber := AsSmall.up.obj.{v, v, max (v + 1) u} x.str.pt}
  map f := {
    base := f.toFunctor
    fiber := AsSmall.up.map f.point}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [Grpd.forgetToCat, Grpd.asSmallFunctor]
    · rfl

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor' :
    grothendieckAsSmallFunctor.{v,u} ⥤ Grothendieck asSmallFunctorCompForgetToCat'.{v,u} where
  obj x := {
    base := ULift.upFunctor.obj $ AsSmall.up.obj x.base
    fiber := x.fiber}
  map f := {
    base := ULift.upFunctor.map $ AsSmall.up.map f.base
    fiber := f.fiber}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor :
    Grothendieck asSmallFunctorCompForgetToCat'.{v,u} ⥤ grothendieckAsSmallFunctor.{v,u} where
  obj x := {
    base :=  AsSmall.down.obj $ ULift.downFunctor.obj $ x.base
    fiber := x.fiber}
  map f := {
    base := AsSmall.down.map $ ULift.downFunctor.map.{_, _, max (u + 1) (v + 2)} f.base
    fiber := f.fiber}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

-- theorem pGrpd_iso_GrothendieckAsSmallFunctor_left :
--     pGrpdToGrothendieckAsSmallFunctor.{v,u}
--       ⋙ grothendieckAsSmallFunctorToPGrpd.{v,u}
--       = Functor.id _ := rfl

-- theorem pGrpd_iso_GrothendieckAsSmallFunctor_right :
--     grothendieckAsSmallFunctorToPGrpd.{v,u}
--       ⋙ pGrpdToGrothendieckAsSmallFunctor.{v,u}
--       = Functor.id _ := rfl

def pGrpd_iso_GrothendieckAsSmallFunctor :
    pgrpd.{v,u}
      ≅ Cat.of (ULift.{max u (v+1) + 1, max (v+1) u}
        grothendieckAsSmallFunctor.{v,u}) where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor


-- /--
-- The following square is a pullback

-- Groupoidal (asSmallFunctor) -- toPGrpd --> PCat.{max v u, max v u}
--         |                                     |
--         |                                     |
--     forget                               PCat.forgetToCat
--         |                                     |
--         v                                     v
--  Grpd.{v,v}--asSmallFunctor ⋙ forgetToCat-->Cat.{max v u, max v u}
-- -/
theorem isPullback_forget_forgetToGrpd :
    IsPullback GROTHToPGRPD.{v,v} GROTHFORGET.{v,v} PCATFORGETTOCAT.{v,v} asSmallFunctorCompForgetToCat.{v,v} := sorry

def sdlkfj := IsPullback.uLiftToPCat asSmallFunctorCompForgetToCat'.{v,v}

def pgrpdIsoULiftGrothendieck :
    pgrpd.{v,v+1}
      ≅ IsPullback.uLiftGrothendieck.{v+1,v+2}
        asSmallFunctorCompForgetToCat'.{v,v} where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor'
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

theorem isPullback1 : IsPullback
    (IsPullback.uLiftToPCat asSmallFunctorCompForgetToCat'.{v,v})
    (IsPullback.uLiftGrothendieckForget asSmallFunctorCompForgetToCat')
    IsPullback.uLiftPCatForgetToCat
    (IsPullback.uLiftA asSmallFunctorCompForgetToCat') :=
  Grothendieck.isPullback (asSmallFunctorCompForgetToCat'.{v,v})

-- def pgrpdAsSmallFunctor' : pgrpd.{v,v} ⟶ IsPullback.uLiftPCat.{max u (v+1),max u (v+1) + 1} :=
--   Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1), v, v} ⋙ PGrpd.forgetToPCat ⋙ ULift.upFunctor)

-- theorem pgrd : pgrpdIsoULiftGrothendieck.hom
--     ≫ IsPullback.uLiftToPCat asSmallFunctorCompForgetToCat'.{v,v}
--     = pgrpdAsSmallFunctor' := sorry
-- #exit
def asdlf := IsPullback.of_iso_isPullback isPullback1 pgrpdIsoULiftGrothendieck



-- def west' : pgrpd.{v,u} ⟶ grpd.{v,u} :=
--   Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor)
-- def north' : pgrpd.{v,u} ⟶ PGRPD.{v,u} :=
--   Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1)})

-- /--
-- The following square is a pullback

-- Groupoidal (asSmallFunctor) -- toPGrpd --> PGrpd.{max v u, max v u}
--         |                                     |
--         |                                     |
--     forget                         PGrpd.forgetToGrpd
--         |                                     |
--         v                                     v
--       Grpd.{v,v}  -- asSmallFunctor --> Grpd.{max v u, max v u}
-- -/
-- theorem isPullback_forget_forgetToGrpd :
--     IsPullback north west east south :=
  
--   sorry

-- /--
-- The following square is a pullback

--       PGrpd.{v,v} -- asSmallFunctor --> PGrpd.{max v u, max v u}
--         |                                     |
--         |                                     |
--     PGrpd.forgetToGrpd               PGrpd.forgetToGrpd
--         |                                     |
--         v                                     v
--       Grpd.{v,v}  -- asSmallFunctor --> Grpd.{max v u, max v u}
-- -/
-- theorem isPullback_forgetToGrpd_forgetToGrpd :
--     IsPullback north west east south := by
--   apply IsPullback.of_isLimit'
--   constructor
--   · sorry
--   · sorry
--   · intro s
--     constructor
--     · sorry
--     · sorry
--     · sorry
--   · constructor; rfl

-- #check Cat.asSmallFunctor
-- def south : grpd.{v,u} ⟶ GRPD.{v,u} :=
--   Cat.homOf (downFunctor.{max (v+1) u, max (v+1) u, max (v+1) u + 1} ⋙ AsSmall.down.{v} ⋙ Grpd.asSmallFunctor.{max u (v+1)})

-- set_option pp.universes true
-- #print south

end IsPullback
end PGrpd


namespace GroupoidNaturalModel
abbrev SGrpd := AsSmall.{u} Grpd.{u,u}

def SGrpd.ofGrpd : Grpd.{u,u} ⥤ SGrpd.{u} := AsSmall.up

def SGrpd.asSmallFunctor : SGrpd.{u} ⥤ SGrpd.{max v u} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor ⋙ AsSmall.up

inductive SGrpd1Carrier : Type 2 where
  | small    (_ : SGrpd.{0})
  | large    (_ : SGrpd.{1})

def SGrpd1Carrier.toLarge : SGrpd1Carrier → SGrpd.{1}
  | .small A => SGrpd.asSmallFunctor.obj.{1} A
  | .large A => A

def SGrpd1 : Type 2 :=
  InducedCategory SGrpd.{1} SGrpd1Carrier.toLarge

def SGrpd1.toLarge (A : SGrpd1) := SGrpd1Carrier.toLarge A

-- FIXME why does deriving SmallCategory no longer work?
instance SGrpd1.smallCategory : SmallCategory.{2} SGrpd1 :=
  InducedCategory.category _

inductive SGrpd2Carrier : Type 3 where
  | small    (_ : SGrpd1)
  | large    (_ : SGrpd.{2})

def SGrpd2Carrier.toLarge : SGrpd2Carrier → SGrpd.{2}
  | .small A => SGrpd.asSmallFunctor.obj.{2} $ A.toLarge
  | .large A => A

-- TODO there are more helpful properties of this construction
/-- A model of Grpd with two internal universes,
  with the property that the small universes
  inject into the large ones. -/
def SGrpd2 : Type 3 := InducedCategory SGrpd.{2} SGrpd2Carrier.toLarge

def SGrpd2.toLarge (A : SGrpd2) := SGrpd2Carrier.toLarge A

-- FIXME why does deriving SmallCategory no longer work?
instance SGrpd2.smallCategory : SmallCategory.{3} SGrpd2 :=
  InducedCategory.category _

def SGrpd1.smallFunctor : SGrpd.{0} ⥤ SGrpd1 where
  obj := .small
  map f := SGrpd.asSmallFunctor.map f

def SGrpd2.smallFunctor : SGrpd1 ⥤ SGrpd2 where
  obj := .small
  map f := SGrpd.asSmallFunctor.map f


namespace SGrpd

def ofGroupoid (Γ : Type u) [Groupoid.{u} Γ] : SGrpd.{u} :=
  ofGrpd.obj (Grpd.of Γ)

def toGrpd : SGrpd.{u} ⥤ Grpd.{u,u} := AsSmall.down

-- def SGrpd.coreOfCategory (C : Type u) [Category.{v} C] : SGrpd.{max w v u} :=
--   SGrpd.ofGroupoid (Core (AsSmall.{w} C))

def core : Cat.{v,v+1} ⥤ SGrpd.{max u (v + 1)} :=
  Core.functor.{v,v+1}
  ⋙ Grpd.asSmallFunctor.{u,v,v+1}
  ⋙ SGrpd.ofGrpd.{max u (v + 1)}

variable {Γ Δ : SGrpd.{max u (v + 1)}} {C D : Type (v+1)}
  [Category.{v,v+1} C] [Category.{v,v+1} D]

def yonedaCoreEquiv' :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ SGrpd.toGrpd.obj Γ ⥤ Core C where
  toFun A := toGrpd.map A ⋙ AsSmall.down 
  invFun A := SGrpd.ofGrpd.map (A ⋙ AsSmall.up)
  left_inv _ := rfl
  right_inv _ := rfl

-- /- The bijection y(Γ) → y(core C) ≃ Γ ⥤ C -/
-- def yonedaCoreEquiv :
--     (y(Γ) ⟶ y(core.obj.{v,u} (Cat.of C)))
--       ≃ SGrpd.toGrpd.obj Γ ⥤ C :=
--   Yoneda.fullyFaithful.homEquiv.symm.trans
--     (yonedaCoreEquiv'.trans
--     Core.functorToCoreEquiv.symm)

/- The bijection Γ → core C ≃ Γ ⥤ C -/
def yonedaCoreEquiv :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ SGrpd.toGrpd.obj Γ ⥤ C :=
  Equiv.trans
    yonedaCoreEquiv'
    Core.functorToCoreEquiv.symm

end SGrpd

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := downFunctor ⋙ f ⋙ upFunctor

variable (C D) [Category.{u} C] [Category.{u} D]

abbrev yonedaCat : Cat.{u,u+1} ⥤ SGrpd.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLim : Limits.PreservesLimits yonedaCat :=
  Limits.comp_preservesLimits _ _

variable {Γ Δ : SGrpd.{u}} {C D : Type (u+1)}
  [Category.{u,u+1} C] [Category.{u,u+1} D]

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
def yonedaCatEquiv :
    (yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C))
      ≃ SGrpd.toGrpd.obj Γ ⥤ C :=
  Equiv.trans yonedaEquiv
    {toFun     := λ A ↦ ULift.upFunctor ⋙ A
     invFun    := λ A ↦ ULift.downFunctor ⋙ A
     left_inv  := λ _ ↦ rfl
     right_inv := λ _ ↦ rfl}

lemma yonedaCatEquiv_yonedaEquivSymm {Γ : SGrpd}
    (A : (yonedaCat.obj (Cat.of C)).obj (Opposite.op Γ)) :
    yonedaCatEquiv (yonedaEquiv.symm A) = upFunctor ⋙ A := by
  congr

theorem yonedaCatEquiv_naturality
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C)) (σ : Δ ⟶ Γ) :
    (AsSmall.down.map σ) ⋙ yonedaCatEquiv A
      = yonedaCatEquiv (yoneda.map σ ≫ A) := by
  simp only [AsSmall.down_obj, AsSmall.down_map, yonedaCatEquiv,
    Functor.op_obj, Functor.comp_obj, Cat.of_α,
    Equiv.trans_apply, Equiv.coe_fn_mk, ← yonedaEquiv_naturality]
  rfl

theorem yonedaCatEquiv_comp
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of D)) (U : D ⥤ C) :
    yonedaCatEquiv (A ≫ yonedaCat.map U) = yonedaCatEquiv A ⋙ U := by
  aesop_cat

abbrev Ty : Psh SGrpd.{u} := yonedaCat.obj (Cat.of Grpd.{u,u})

abbrev Tm : Psh SGrpd.{u} := yonedaCat.obj (Cat.of PGrpd.{u,u})

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

section Ty
variable {Γ : SGrpd.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev ext : SGrpd := SGrpd.ofGrpd.obj $ Grpd.of (Groupoidal (yonedaCatEquiv A))

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget _)

abbrev var : (y(ext A) : Psh SGrpd) ⟶ Tm :=
  yonedaCatEquiv.symm (Groupoidal.toPGrpd (yonedaCatEquiv A))

/-- The image of (roughly) `Groupoidal.toPGrpd : Grothendieck A ⥤ PGrpd`
  under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
  -/
abbrev yonedaCatMapToPGrpd :
    yonedaCat.obj (IsPullback.uLiftGrothendieck $
      Groupoid.compForgetToCat (yonedaCatEquiv A)) ⟶ Tm :=
  yonedaCat.map
      (Cat.homOf (ULift.downFunctor ⋙ Groupoidal.toPGrpd (yonedaCatEquiv A)))

/-- The image of (roughly) `Grothendieck.forget : Grothendieck A ⥤ Γ` under
  `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapGrothendieckForget :=
      (yonedaCat.map $ IsPullback.uLiftGrothendieckForget
        (Groupoid.compForgetToCat.{u} $ yonedaCatEquiv A))

/-- The image of `yonedaCatEquiv A` under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapYonedaCatEquiv :
    yonedaCat.obj (IsPullback.uLiftΓ.{u,u} $ SGrpd.toGrpd.obj Γ) ⟶ Ty :=
  yonedaCat.map (Cat.homOf (ULift.downFunctor.{u,u} ⋙ (yonedaCatEquiv A)))

/-- The image of the pullback `Grothendieck.Groupoidal.isPullback` under `yonedaCat` -/
theorem isPullback_yonedaCatGrothendieckForget_tp :
    IsPullback
      (yonedaCatMapToPGrpd A)
      (yonedaCatMapGrothendieckForget A)
      tp
      (yonedaCatMapYonedaCatEquiv A) :=
  Functor.map_isPullback yonedaCat (Groupoidal.isPullback (yonedaCatEquiv A))

/-- This is a natural isomorphism between functors in the following diagram
  SGrpd.{u}------ yoneda -----> Psh SGrpd
   |                              Λ
   |                              |
   |                              |
  inclusion                 precomposition with inclusion
   |                              |
   |                              |
   |                              |
   V                              |
Cat.{big univ}-- yoneda -----> Psh Cat
  
-/
def asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat :
    (AsSmall.up) ⋙ (yoneda : SGrpd.{u} ⥤ SGrpd.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦
        AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

/-- `yoneda.map (disp A)` is isomorphic to `yonedaCat(uLiftGrothendieckForget _)` in
  the arrow category, hence forming a pullback square

  yoneda (ext A) ------≅----> yonedaCat(uLift (ext A))
         |                                |
         |                                |
         |                                |
         |                                |
         |                                |
         v                                v
      yoneda Γ --------≅----> yonedaCat(uLift Γ)
-/
theorem isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget :
    IsPullback
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app _)
      (yoneda.map (disp A))
      (yonedaCatMapGrothendieckForget A)
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app
        $ SGrpd.toGrpd.obj Γ)
      :=
    IsPullback.of_horiz_isIso ⟨
      asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.naturality
      (AsSmall.down.map (disp A))⟩

/-- The pullback required for the natural model `GroupoidNaturalModel.base`-/
theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

end Ty

-- TODO link to this in blueprint
/-- The natural model that acts as the ambient
  model in which the other universes live.
  Note that unlike the other universes this is *not* representable,
  but enjoys having representable fibers that land in itself.
-/
def base : NaturalModelBase SGrpd.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext := ext
  disp := disp
  var := var
  disp_pullback := isPullback_yonedaDisp_tp

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `baseU`. -/
abbrev U : SGrpd.{max u (v + 1)} :=
  SGrpd.core.obj.{v,u} $ Cat.of Grpd.{v,v}

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `baseU`. -/
abbrev E : SGrpd.{max u (v + 1)} :=
  SGrpd.core.obj.{v,u} $ Cat.of PGrpd.{v,v}

/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `baseU`. -/
abbrev π : E.{v} ⟶ U.{v} :=
  SGrpd.core.map.{v,u} $ Cat.homOf PGrpd.forgetToGrpd

namespace U
variable {Γ : SGrpd.{max u (v + 1)}} (A : Γ ⟶ U.{v})

/-- `liftSucc` is the base map between two `v`-small universes 
    E.{v} ---------------> E.{v+1}
    |                      |
    |                      |
    |                      |
    |                      |
    v                      v
    U.{v}-----liftsucc---->U.{v+1}
 -/
def liftSucc' : U.{v,max u (v+2)} ⟶ U.{v+1,max u (v+2)} :=
  SGrpd.ofGrpd.map $
    AsSmall.down
    ⋙ (Core.functor'.{v,v+1,v+1,v+2} Grpd.asSmallFunctor.{v+1}
      : Core Grpd.{v,v} ⥤ Core Grpd.{v+1,v+1})
    ⋙ AsSmall.up

def toTy' : SGrpd.toGrpd.obj U.{v,u} ⥤ Grpd.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Core.inclusion Grpd.{v,v}
    ⋙ Grpd.asSmallFunctor.{max u (v+1)}

def toTm' : SGrpd.toGrpd.obj E.{v,u} ⥤ PGrpd.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Core.inclusion PGrpd.{v,v}
    ⋙ PGrpd.asSmallFunctor.{max u (v+1)}

/-- `toTy` is the map that classifies the universe
  `U` of `v`-small types as a map into the type classifier `Ty`.
  This will fit into the pullback square

    E --------toTm---> Tm
    |                   |
    |                   |
    |                   |
    |                   |
    v                   v
    U---------toTy----->Ty

-/
def toTy : y(U.{v,u}) ⟶ Ty.{max u (v+1)} :=
  yonedaCatEquiv.symm toTy'

lemma toTy_eq : yonedaCatEquiv.symm toTy' = sorry := by
  dsimp [yonedaCatEquiv, toTy']
  -- rw [yonedaEquiv_symm]
  
  sorry

def toTm : y(E.{v,u}) ⟶ Tm.{max u (v+1)} :=
  yonedaCatEquiv.symm toTm'


def isPullback_π_tp :
    IsPullback toTm ym(π) tp toTy := by
  
  sorry

-- /-- This is a natural model isomorphic to `baseU`,
--   its type classifier `Ty` is exactly `y(U.{v})` but its term classifier
--   `Tm` is the context extension from the ambient model `base`
-- -/
-- def baseU' : NaturalModelBase SGrpd.{max u (v+1)} :=
--   NaturalModelBase.pullback base.{max u (v + 1)} toTy.{v,u}

theorem baseU'_isPullback :
    IsPullback (base.var toTy) (yoneda.map (base.disp toTy)) base.tp toTy.{v,u}
  := base.{max u (v+1)}.disp_pullback toTy.{v,u}

def baseU'.TmIsoEHom : Groupoidal (toTy'.{v,u})
    ⥤ PGrpd.{v,v} := by
  dsimp [toTy']
  
  sorry

def baseU'.TmIsoE : base.{max u (v+1)}.ext toTy.{v,u} ≅ E.{v} where
  -- Functor.mapIso AsSmall.up.map sorry 
  hom := SGrpd.yonedaCoreEquiv.invFun baseU'.TmIsoEHom
    
  inv := sorry

abbrev ext : SGrpd.{max u (v + 1)} :=
  GroupoidNaturalModel.ext (ym(A) ≫ toTy)

-- def ext_iso_ext : U.ext A ≅ GroupoidNaturalModel.ext (ym(A) ≫ toTy) := sorry

abbrev disp : ext A ⟶ Γ :=
  GroupoidNaturalModel.disp (ym(A) ≫ toTy)

abbrev var : ext A ⟶ E.{v} := sorry
  -- SGrpd.yonedaCoreEquiv.symm $ Groupoidal.toPGrpd (SGrpd.yonedaCoreEquiv A)

theorem isPullback_disp_π {Γ : SGrpd.{max u (v + 1)}} (A : Γ ⟶ U.{v}) :
    IsPullback (U.var (A)) (U.disp (A)) π A :=
  sorry

theorem isPullback_yoneda_disp_yoneda_π
    {Γ : SGrpd.{max u (v + 1)}} (A : Γ ⟶ U.{v}) :
    IsPullback
      ym(U.var (A))
      ym(U.disp (A))
      ym(π)
      ym(A) := 
  Functor.map_isPullback yoneda (isPullback_disp_π A)


end U

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v + 1)`-large,
  its representable fibers can be larger than itself.

  This natural model is given by pullback of the natural model `base`.
  TODO However, we likely want to use the explicit `Tm = y(E)` and
  `tp = ym(π)` instead of the grothendieck construction provided.
-/
def baseU : NaturalModelBase SGrpd.{max u (v + 1)} where
  Ty := y(U.{v})
  Tm := y(E.{v})
  tp := ym(π.{v})
  ext A := U.ext (Yoneda.fullyFaithful.preimage A)
  disp A := U.disp (Yoneda.fullyFaithful.preimage A)
  var A := ym(U.var (Yoneda.fullyFaithful.preimage A))
  disp_pullback A := by
    convert U.isPullback_yoneda_disp_yoneda_π (Yoneda.fullyFaithful.preimage A)
    aesop_cat

def baseUU : NaturalModelBase SGrpd.{max u (v + 2)} :=
  baseU.{v+1,u}.pullback ym(U.liftSucc'.{v,u})

def uHomSeqObjs (i : Nat) (h : i < 3) : NaturalModelBase SGrpd.{2} :=
  match i with
  | 0 => baseUU.{0,2}
  | 1 => baseU.{1,2}
  | 2 => base.{2}
  | (n+3) => by omega

-- instance : Limits.HasTerminal SGrpd := sorry

open NaturalModelBase

-- def baseUU.UHom : UHom baseUU.{v,max u (v+2)} baseU.{v+1,max u (v+2)} := {
--   baseU.pullbackHom ym(ULiftSucc'.{v,u}) with
--   U := sorry
--   U_pb := sorry
-- }

-- def baseU.UHom : UHom baseU.{v,max u (v+1)} base.{max u (v+1)} := {
--   base.pullbackHom ULiftMax with
--   U := sorry
--   U_pb := sorry
-- }

def uHomSeqHomSucc' (i : Nat) (h : i < 2) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => by
    dsimp [uHomSeqObjs]
    
    sorry -- NaturalModelBase.UHom.ofTarskiU base.{2} _ _
  | 1 => sorry
  | (n+2) => by omega

/--
  The groupoid natural model with two nested representable universes
-/
def uHomSeq : NaturalModelBase.UHomSeq SGrpd.{2} where
  length := 2
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

end GroupoidNaturalModel

open GroupoidNaturalModel



end CategoryTheory

-- noncomputable
end
