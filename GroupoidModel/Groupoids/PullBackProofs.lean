import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import GroupoidModel.Groupoids.GroupoidalGrothendieck
import GroupoidModel.Groupoids.PointedCat
-- import GroupoidModel.NaturalModel

/-!
Here we show some lemmas about pullbacks
-/

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace Limits

universe u₃ v₃
variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C]

open CategoryTheory
open Functor

/-- A `c : RepCone F` is:
* an object `c.pt` and
* a natural transformation `c.π : yoneda.obj c.pt ⟶ F`
from the constant `yoneda.obj c.pt` functor to `F`.
-/
structure RepCone (F : J ⥤ Cᵒᵖ ⥤ Type v₃) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from the constant functor at `X` to `F` -/
  π : (const J).obj (yoneda.obj pt) ⟶ F

namespace RepCone

variable {F : J ⥤ Cᵒᵖ ⥤ Type v₃}

@[reducible] def cone (s : RepCone F) : Limits.Cone F where
  pt := yoneda.obj s.pt
  π := s.π

end RepCone

variable {F : J ⥤ Cᵒᵖ ⥤ Type v₃}

structure RepIsLimit (t : Cone F) where
  lift : ∀ s : RepCone F, s.cone.pt ⟶ t.pt
  fac : ∀ (s : RepCone F) (j : J),
    lift s ≫ t.π.app j = (s.cone).π.app j := by aesop_cat
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : RepCone F) (m : s.cone.pt ⟶ t.pt)
    (_ : ∀ j : J, m ≫ t.π.app j = s.cone.π.app j), m = lift s := by
    aesop_cat

-- @[reducible] def repConeOfConePt 
--   (s : Cone F) (c : Cᵒᵖ) (x : s.pt.obj c) :
--   RepCone F := 
--     { pt := c.unop
--       π := {app := λ j ↦ yonedaEquiv.invFun x ≫ s.π.app j}}

abbrev ConeMap (s : Cone F) (c : C) :=
 yoneda.obj c ⟶ s.pt

@[simp] def repConeOfConeMap 
  (s : Cone F) (c : C) (x' : ConeMap s c) :
  RepCone F := 
    { pt := c
      π := {app := λ j ↦ x' ≫ s.π.app j}}

namespace RepIsLimit

variable {t : Cone F} (P : RepIsLimit t) {s : Cone F} 

def lift' (c : C) (x' : ConeMap s c) : (ConeMap t c) :=
  P.lift $ repConeOfConeMap s c x'

@[simp] lemma lift'_naturality {s : Cone F} {c d : C}
  (f : c ⟶ d) (x' : ConeMap s d) :
  lift' P c (yoneda.map f ≫ x') = yoneda.map f ≫ lift' P d x' := by
  apply Eq.symm
  apply P.uniq (repConeOfConeMap s c (yoneda.map f ≫ x')) (yoneda.map f ≫ lift' P d x')
  intro j
  have h := P.fac (repConeOfConeMap s d x') j
  dsimp[repConeOfConeMap]
  dsimp[repConeOfConeMap] at h
  rw[Category.assoc, Category.assoc, ← h]
  rfl

@[simp] def lift''_app (s : Cone F) (c : C)  :
  s.pt.obj (Opposite.op c) → t.pt.obj (Opposite.op c) :=
    yonedaEquiv ∘ lift' P c ∘ yonedaEquiv.symm

def lift''_app_naturality 
  {c d : C} (f : c ⟶ d) :
  s.pt.map (f.op) ≫ lift''_app P s c
    = lift''_app P s d ≫ t.pt.map (Opposite.op f) := by
  ext x
  simp[lift''_app, lift']
  rw[yonedaEquiv_naturality']
  have h := lift'_naturality P f (yonedaEquiv.symm x)
  simp[lift'] at h
  simp
  rw[← h, yonedaEquiv_symm_naturality_left]

variable (s)

def lift'' : s.pt ⟶ t.pt := {
    app := λ c ↦ lift''_app P s c.unop
    naturality := by
      intros
      apply lift''_app_naturality
}

def fac_ext (j : J) (c : C) (x) :
  (lift'' P s ≫ t.π.app j).app (Opposite.op c) x
  = (s.π.app j).app (Opposite.op c) x := by
  dsimp[lift'',lift',← yonedaEquiv_comp]
  let x' := yonedaEquiv.symm x
  have h := P.fac (repConeOfConeMap s c x') j 
  dsimp [repConeOfConeMap] at h
  simp [h, lift'', lift', yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv x]

def uniq_ext (m : s.pt ⟶ t.pt)
  (hm : ∀ (j : J), m ≫ t.π.app j = s.π.app j) (c : C) (x) :
  m.app (Opposite.op c) x
  = (P.lift'' s).app (Opposite.op c) x := by
  let x' := yonedaEquiv.symm x
  have hj : (∀ (j : J), (x' ≫ m) ≫ t.π.app j = x' ≫ s.π.app j) := by simp[hm]
  have h := P.uniq (repConeOfConeMap s c x') (x' ≫ m) hj
  dsimp [repConeOfConeMap] at h
  simp [lift'', lift', yonedaEquiv_comp, ← h, Equiv.apply_symm_apply yonedaEquiv x]

def IsLimit {t : Cone F} (P : RepIsLimit t)
  : IsLimit t where
  lift := lift'' P
  fac := λ s j ↦ by
    ext c x
    apply fac_ext
  uniq := λ s m hm ↦ by
    ext c x
    apply uniq_ext P s m hm

end RepIsLimit

abbrev RepPullbackCone {X Y Z : Cᵒᵖ ⥤ Type v₃} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  RepCone (cospan f g)

namespace RepPullbackCone

variable {W X Y Z : Cᵒᵖ ⥤ Type v₃} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbrev fst (t : RepPullbackCone f g) : yoneda.obj t.pt ⟶ X :=
  t.π.app WalkingCospan.left

/-- The second projection of a pullback cone. -/
abbrev snd (t : RepPullbackCone f g) : yoneda.obj t.pt ⟶ Y :=
  t.π.app WalkingCospan.right

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom Limits.PullbackCone

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def repIsLimitAux (t : PullbackCone f g) (lift : ∀ s : RepPullbackCone f g, yoneda.obj s.pt ⟶ t.pt)
    (fac_left : ∀ s : RepPullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : RepPullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : ∀ (s : RepPullbackCone f g) (m : yoneda.obj s.pt ⟶ t.pt)
      (_ : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) : RepIsLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.cone.w inl, ← t.w inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a limit cone.
-/
def RepIsLimit.mk {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : RepPullbackCone f g, yoneda.obj s.pt ⟶ W)
    (fac_left : ∀ s : RepPullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : RepPullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : RepPullbackCone f g) (m : yoneda.obj s.pt ⟶ W)
      (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (PullbackCone.mk fst snd eq) :=
  RepIsLimit.IsLimit $
  repIsLimitAux _ lift fac_left fac_right fun s m w =>
  uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

-- lemma Idaf {P X Y Z : C ⥤ Type v₁} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : IsPullback fst snd f g := sorry

end RepPullbackCone


end Limits

noncomputable section

section Pullbacks

section Lemmas

/--theorem PointedCategory.ext {P1 P2 : PCat.{u,u}} (eq_cat : P1.α  = P2.α): P1 = P2 := by sorry -/
theorem PointedFunctor.eqToHom_toFunctor {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).toFunctor = (eqToHom (congrArg PCat.forgetPoint.obj eq)) := by
    cases eq
    simp[ PointedFunctor.id, CategoryStruct.id, PCat.forgetPoint,Cat.of,Bundled.of]

/-- This is the proof of equality used in the eqToHom in `PointedFunctor.eqToHom_point` -/
theorem PointedFunctor.eqToHom_point_help {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).obj PointedCategory.pt = PointedCategory.pt  := by
  cases eq
  simp [CategoryStruct.id]

/-- This shows that the point of an eqToHom in PCat is an eqToHom-/
theorem PointedFunctor.eqToHom_point {P1 P2 : PCat.{u,u}} (eq : P1 = P2) : (eqToHom eq).point = (eqToHom (PointedFunctor.eqToHom_point_help eq)) := by
  cases eq
  simp[PointedFunctor.id, CategoryStruct.id, PCat.forgetPoint,Cat.of,Bundled.of]

/-- This is the turns the object part of eqToHom functors into a cast-/
theorem Cat.eqToHom_obj (C1 C2 : Cat.{u,v})(x : C1)(eq : C1 = C2): (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the proof of equality used in the eqToHom in `Cat.eqToHom_hom` -/
theorem Cat.eqToHom_hom_help {C1 C2 : Cat.{u,v}}(x y: C1)(eq : C1 = C2): (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem Cat.eqToHom_hom {C1 C2 : Cat.{u,v}}{x y: C1}(f : x ⟶ y)(eq : C1 = C2): (eqToHom eq).map f = (cast (Cat.eqToHom_hom_help x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the proof of equality used in the eqToHom in `PCat.eqToHom_hom` -/
theorem PCat.eqToHom_hom_help {C1 C2 : PCat.{u,v}}(x y: C1)(eq : C1 = C2): (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom pointed functors into a cast-/
theorem PCat.eqToHom_hom {C1 C2 : PCat.{u,v}}{x y: C1}(f : x ⟶ y)(eq : C1 = C2): (eqToHom eq).map f = (cast (PCat.eqToHom_hom_help x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This shows that two objects are equal in Grothendieck A if they have equal bases and fibers that are equal after being cast-/
theorem Grothendieck.ext' {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}(g1 g2 : Grothendieck A)(eq_base : g1.base = g2.base)
  (eq_fiber : g1.fiber = (A.map (eqToHom eq_base.symm)).obj g2.fiber ) : (g1 = g2) := by
    rcases g1 with ⟨g1.base,g1.fiber⟩
    rcases g2 with ⟨g2.base,g2.fiber⟩
    simp at eq_fiber eq_base
    cases eq_base
    simp
    rw[eq_fiber]
    simp [eqToHom_map, CategoryStruct.id]

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem Grothendieck.eqToHom_base {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}(g1 g2 : Grothendieck A)
  (eq : g1 = g2) : (eqToHom eq).base = (eqToHom (congrArg (Grothendieck.forget A).obj eq)) := by
    cases eq
    simp

/-- This is the proof of equality used in the eqToHom in `Grothendieck.eqToHom_fiber` -/
theorem Grothendieck.eqToHom_fiber_help {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}{g1 g2 : Grothendieck A}
  (eq : g1 = g2) : (A.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
    cases eq
    simp

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem Grothendieck.eqToHom_fiber {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}}{g1 g2 : Grothendieck A}
  (eq : g1 = g2) : (eqToHom eq).fiber = eqToHom (Grothendieck.eqToHom_fiber_help eq) := by
    cases eq
    simp

/-- This eliminates an eqToHom on the right side of an equality-/
theorem RightSidedEqToHom {C : Type v} [Category C] {x y z : C} (eq : y = z) {f : x ⟶ y} {g : x ⟶ z}
  (heq : HEq f g) : f ≫ eqToHom eq = g := by
    cases eq
    simp
    simp at heq
    exact heq

/-- This theorem is used to eliminate eqToHom form both sides of an equation-/
theorem CastEqToHomSolve {C : Type v} [Category C] {x x1 x2 y y1 y2: C} (eqx1 : x = x1)(eqx2 : x = x2)
  (eqy1 : y1 = y)(eqy2 : y2 = y){f : x1 ⟶ y1}{g : x2 ⟶ y2}(heq : HEq f g) : eqToHom eqx1 ≫ f ≫ eqToHom eqy1 = eqToHom eqx2 ≫ g ≫ eqToHom eqy2:= by
    cases eqx1
    cases eqx2
    cases eqy1
    cases eqy2
    simp
    simp at heq
    exact heq

end Lemmas



section GrothendieckPullBack
/-
In this section we prove that the following square is a PullBack

  Grothendieck A ---- CatVar' ----> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetPoint
        |                           |
        v                           v
        Γ--------------A----------->Cat
-/

-- This takes in two equal functors F and G from C in to Cat and an x:C and returns (F.obj x) ≅ (G.obj x).
def CastFunc {C : Cat.{u,u+1}}{F1 : C ⥤ Cat.{u,u}}{F2 : C ⥤ Cat.{u,u}}(Comm : F1 = F2 )(x : C) :
  Equivalence (F1.obj x) (F2.obj x) := Cat.equivOfIso (eqToIso (Functor.congr_obj  Comm  x))

-- This turns the cast functor in an eqToHom
theorem CastFuncIsEqToHom {C : Cat.{u,u+1}} {F1 : C ⥤ Cat.{u,u}} {F2 : C ⥤ Cat.{u,u}} (Comm : F1 = F2 )(x : C):
  (CastFunc Comm x).functor = (eqToHom (Functor.congr_obj Comm x)) := by
    simp[CastFunc,Cat.equivOfIso]

-- This is a functor that takes a category up a universe level
def Up_uni (Δ : Type u)[Category.{u} Δ] :  Δ ⥤ (ULift.{u+1,u} Δ) where
  obj x := {down := x}
  map f := f

-- This is a functor that takes a category down a universe level
def Down_uni (Δ : Type u)[Category.{u} Δ]: (ULift.{u+1,u} Δ) ⥤ Δ where
  obj x := x.down
  map f := f

-- This is a helper theorem for eliminating Up_uni and Down_uni functors
theorem Up_Down {C : Type (u+1)}[Category.{u} C]{Δ : Type u}[Category.{u} Δ] (F : C ⥤ Δ)
  (G : C ⥤ (ULift.{u+1,u} Δ)): ((F ⋙ (Up_uni Δ)) = G) ↔ (F = (G ⋙ (Down_uni Δ))) := by
    unfold Up_uni
    unfold Down_uni
    simp [Functor.comp]
    refine Iff.intro ?_ ?_ <;> intro h
    · rw[<- h]
    · rw[h]

-- This is the functor from the Grothendieck to Pointed Categorys
def CatVar' (Γ : Cat)(A : Γ ⥤ Cat) : (Grothendieck A) ⥤ PCat where
  obj x := ⟨(A.obj x.base), PointedCategory.of (A.obj x.base) x.fiber⟩
  map f := ⟨A.map f.base, f.fiber⟩
  map_id x := by
    dsimp
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    apply PointedFunctor.ext
    · simp [CategoryStruct.id]
    · simp [CategoryStruct.id, PointedFunctor.id]
  map_comp {x y z} f g := by
    dsimp [PointedFunctor.comp]
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    let _ := (PointedCategory.of (A.obj z.base) z.fiber)
    apply PointedFunctor.ext
    · simp
    · simp [A.map_comp]; rfl

-- This is the proof that the square commutes
theorem Comm {Γ : Cat}(A : Γ ⥤ Cat) : (Down_uni (Grothendieck A) ⋙ CatVar' Γ A) ⋙ PCat.forgetPoint =
  ((Down_uni (Grothendieck A)) ⋙ Grothendieck.forget A ⋙ (Up_uni Γ)) ⋙ Down_uni ↑Γ ⋙ A := by
    apply Functor.ext
    · intros X Y f
      simp [PCat.forgetPoint,Down_uni,Up_uni,CatVar']
    · intro X
      simp [PCat.forgetPoint,Down_uni,Up_uni,CatVar']
      exact rfl

-- This is a helper functor from from a pointed category to itself without a point
def ForgetPointFunctor (P : PCat.{u,u}) : P ⥤ (PCat.forgetPoint.obj P) :=
  Functor.id P

-- This is the construction of universal map of th limit
def Grothendieck.UnivesalMap {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A) : C ⥤ Grothendieck A where
  obj x := {base := (F2.obj x), fiber := ((ForgetPointFunctor (F1.obj x)) ⋙ (CastFunc Comm x).functor).obj ((F1.obj x).str.pt)}
  map f := by
    rename_i X Y
    refine {base := F2.map f, fiber := (eqToHom ?_) ≫ (((CastFunc Comm Y).functor).map (F1.map f).point)}
    dsimp
    have h1 := Functor.congr_hom Comm.symm f
    dsimp at h1
    have h2 : (eqToHom (Functor.congr_obj (Eq.symm Comm) X)).obj
     ((eqToHom (CastFunc.proof_1 Comm X )).obj (@PointedCategory.pt (↑(F1.obj X)) (F1.obj X).str)) =
      ((eqToHom (CastFunc.proof_1 Comm X)) ≫ (eqToHom (Functor.congr_obj (Eq.symm Comm) X))).obj
       (@PointedCategory.pt (↑(F1.obj X)) (F1.obj X).str) := by rfl
    simp[h1,CastFunc,Cat.equivOfIso,ForgetPointFunctor,h2,eqToHom_trans,eqToHom_refl,CategoryStruct.id,PCat.forgetPoint]
  map_id x := by
    dsimp [CategoryStruct.id,Grothendieck.id]
    apply Grothendieck.ext
    simp[Grothendieck.Hom.fiber,(dcongr_arg PointedFunctor.point (F1.map_id x)),eqToHom_map,CategoryStruct.id]
    exact F2.map_id x
  map_comp f g := by
    rename_i X Y Z
    dsimp [CategoryStruct.comp,comp]
    fapply Grothendieck.ext
    · simp
    · dsimp [Hom.fiber]
      have h1 := PointedFunctor.congr_point (F1.map_comp f g)
      dsimp [CategoryStruct.comp] at h1
      simp [h1,(CastFunc Comm Z).functor.map_comp,(CastFunc Comm Z).functor.map_comp,<- Category.assoc,eqToHom_map]
      refine congrArg (fun(F) => F ≫ ((CastFunc Comm Z).functor.map (F1.map g).point)) ?_
      simp [Category.assoc]
      have comm1 := Functor.congr_hom Comm (g)
      simp [Functor.Comp,PCat.forgetPoint] at comm1
      have comm2 := Functor.congr_hom comm1 (F1.map f).point
      rw [comm2]
      simp [Functor.map_comp,eqToHom_map]
      have rwh1 : (CastFunc Comm Z).functor.map ((eqToHom (Eq.symm (Functor.congr_obj Comm Z))).map ((A.map (F2.map g)).map ((eqToHom (Functor.congr_obj Comm Y)).map (F1.map f).point))) =
        ((eqToHom (Functor.congr_obj Comm Y)) ≫ (A.map (F2.map g)) ≫ ((eqToHom (Eq.symm (Functor.congr_obj Comm Z)))) ≫ ((CastFunc Comm Z).functor)).map ((F1.map f).point) := rfl
      have rwh2 : ((eqToHom (Functor.congr_obj Comm Y)) ≫ (A.map (F2.map g)) ≫ ((eqToHom (Eq.symm (Functor.congr_obj Comm Z)))) ≫ ((CastFunc Comm Z).functor)) =
        (CastFunc Comm Y).functor ≫ A.map (F2.map g) := by
        rw[CastFuncIsEqToHom,eqToHom_trans,<- CastFuncIsEqToHom Comm]
        simp
      have rwh3 := Functor.congr_hom rwh2 (F1.map f).point
      rw [rwh1,rwh3]
      simp

--This is the proof that the universal map composed with CatVar' is the the map F1
theorem Grothendieck.UnivesalMap_CatVar'_Comm {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A) : (Grothendieck.UnivesalMap A C F1 F2 Comm) ⋙ (CatVar' Γ A) = F1 := by
    fapply Functor.ext
    intro x
    have Comm' := Functor.congr_obj Comm x
    simp [PCat.forgetPoint] at Comm'
    simp [UnivesalMap,CatVar']
    congr 1
    · simp [<- Comm',Cat.of,Bundled.of]
    · simp [PointedCategory.of,ForgetPointFunctor,CastFunc,Cat.equivOfIso]
      congr 1
      · rw [<- Comm']
        simp [Cat.of,Bundled.of]
      · rw [<- Comm']
        simp [Cat.of,Bundled.of,Cat.str]
      · refine heq_of_cast_eq ?h_obj.h.e_3.e_3.e ?h_obj.h.e_3.e_3.x
        · rw [<- Comm']
          simp [Cat.of,Bundled.of]
        · simp [Cat.eqToHom_obj]
    · intros X Y f
      simp[UnivesalMap,CatVar']
      let _ : PointedCategory (A.obj (F2.obj X)) := by
        apply PointedCategory.mk
        exact (CastFunc Comm X).functor.obj ((ForgetPointFunctor (F1.obj X)).obj ((F1.obj X).str.pt))
      let _ : PointedCategory ↑(A.obj (F2.obj Y)) := by
        apply PointedCategory.mk
        exact (CastFunc Comm Y).functor.obj ((ForgetPointFunctor (F1.obj Y)).obj ((F1.obj Y).str.pt))
      apply PointedFunctor.ext
      · simp [CastFunc,Cat.equivOfIso,CategoryStruct.comp,PointedFunctor.eqToHom_point,eqToHom_map]
        congr <;> try simp [PointedFunctor.eqToHom_toFunctor]
        have rwHelp1 : ((eqToHom (CastFunc.proof_1 Comm Y)).map (F1.map f).point) = ((eqToHom (CastFunc.proof_1 Comm Y)).map (F1.map f).point) ≫ eqToHom rfl  := by
          simp
        rw [rwHelp1]
        refine heq_of_cast_eq ?_ ?_
        · congr 1 <;> simp [PointedFunctor.eqToHom_toFunctor]
          rfl
        · simp [Cat.eqToHom_hom,PCat.eqToHom_hom]
      · have r := Functor.congr_hom Comm.symm f
        simp
        simp [PCat.forgetPoint] at r
        rw [r]
        simp [CategoryStruct.comp,PointedFunctor.comp,PointedFunctor.eqToHom_toFunctor]

-- This is the proof that the universal map is unique
theorem Grothendieck.UnivesalMap_Uniq {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u})(C : Cat.{u,u+1})
  (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Γ)(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ A)(F : C ⥤ Grothendieck A)
  (F1comm :F ⋙ (CatVar' Γ A) = F1)(F2comm : F ⋙ (Grothendieck.forget A) = F2) :
  F = (Grothendieck.UnivesalMap A C F1 F2 Comm) := by
    fapply Functor.ext
    · intro X
      dsimp [UnivesalMap]
      have eq_base : (F.obj X).base = F2.obj X := by
        rw [<- (Functor.congr_obj F2comm X)]
        simp
      have abstract : F.obj X = Grothendieck.mk ((F.obj X).base) ((F.obj X).fiber) := rfl
      rw [abstract]
      fapply Grothendieck.ext'
      · simpa
      · simp[eqToHom_map,CastFunc,Cat.equivOfIso,ForgetPointFunctor,PointedCategory.pt]
        aesop_cat
    . intros X Y f
      fapply Grothendieck.ext
      . dsimp[UnivesalMap]
        dsimp [forget,Functor.comp] at F2comm
        have h := Functor.congr_hom F2comm f
        simp at h
        simp [h, Grothendieck.eqToHom_base]
      . dsimp[UnivesalMap]
        dsimp [CatVar',Functor.comp] at F1comm
        have h := (PointedFunctor.congr_point ((Functor.congr_hom F1comm f)))
        simp at h
        rw [h]
        simp [eqToHom_map,PointedFunctor.eqToHom_point,Grothendieck.eqToHom_fiber,CastFunc,Cat.equivOfIso]
        have hh : ∀{G1 G2 : Grothendieck A}(eq : G1 = G2), A.map (eqToHom eq).base = eqToHom ?_ := by
          simp[Grothendieck.eqToHom_base,eqToHom_map]
        · congr
        simp [Functor.congr_hom (hh ?_),Cat.eqToHom_hom,PCat.eqToHom_hom]
        refine CastEqToHomSolve _ _ _ _ ?_
        apply @HEq.trans _ _ _ _ (F1.map f).point
        · apply cast_heq
        · apply HEq.symm
          apply cast_heq

-- This is the type of cones
abbrev GrothendieckCones {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} PCat.{u,u})
  (Cat.of.{u,u+1} (ULift.{u+1,u} Γ))
  (Cat.of.{u,u+1} Cat.{u,u})
  PCat.forgetPoint.{u,u}
  ((Down_uni Γ) ⋙ A)

-- This is the cone we will prove is the limit
abbrev GrothendieckLim {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}): (GrothendieckCones A) :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of PCat.{u,u})
    (Cat.of (ULift.{u + 1, u} Γ))
    (Cat.of Cat.{u,u})
    (PCat.forgetPoint.{u,u})
    ((Down_uni Γ) ⋙ A)
    (Cat.of (ULift.{u+1,u} (Grothendieck A)))
    ((Down_uni (Grothendieck A)) ⋙ CatVar' Γ A)
    (Down_uni (Grothendieck A) ⋙ Grothendieck.forget A ⋙ Up_uni Γ)
    (Comm A)

-- This is the proof that the limit cone is a limit
def GrothendieckLimisLim {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) : Limits.IsLimit (GrothendieckLim A) := by
  refine Limits.PullbackCone.isLimitAux' (GrothendieckLim A) ?_
  intro s
  let FL := (s.π).app (Option.some Limits.WalkingPair.left)
  let FR := (s.π).app (Option.some Limits.WalkingPair.right)
  let Comm := (((s.π).naturality (Limits.WalkingCospan.Hom.inl)).symm).trans ((s.π).naturality (Limits.WalkingCospan.Hom.inr))
  fconstructor
  · dsimp [GrothendieckLim,Quiver.Hom,Cat.of,Bundled.of]
    refine (Grothendieck.UnivesalMap A s.pt FL (FR ⋙ (Down_uni Γ)) ?_) ⋙ (Up_uni (Grothendieck A))
    exact (((s.π).naturality (Limits.WalkingCospan.Hom.inl)).symm).trans ((s.π).naturality (Limits.WalkingCospan.Hom.inr))
  · refine ⟨?_,?_,?_⟩
    · exact Grothendieck.UnivesalMap_CatVar'_Comm A s.pt FL (FR ⋙ (Down_uni Γ)) Comm
    · exact rfl
    · intros m h1 h2
      have r := Grothendieck.UnivesalMap_Uniq A s.pt FL (FR ⋙ (Down_uni Γ)) Comm (m ⋙ (Down_uni (Grothendieck A))) h1 ?C
      · exact ((Up_Down (Grothendieck.UnivesalMap A s.pt FL (FR ⋙ Down_uni ↑Γ) Comm) m).mpr r.symm).symm
      · exact ((Up_Down (((m ⋙ Down_uni (Grothendieck A)) ⋙ Grothendieck.forget A)) s.snd).mp h2)

-- This converts the proof of the limit to the proof of a pull back
theorem GrothendieckLimisPullBack {Γ : Cat.{u,u}}(A : Γ ⥤ Cat.{u,u}) :
  @IsPullback (Cat.{u,u+1}) _
  (Cat.of (ULift.{u+1,u} (Grothendieck A)))
  (Cat.of PCat.{u,u}) (Cat.of (ULift.{u+1,u} Γ))
  (Cat.of Cat.{u,u})
  ((Down_uni (Grothendieck A)) ⋙ (CatVar' Γ A))
  ((Down_uni (Grothendieck A)) ⋙ (Grothendieck.forget A) ⋙ (Up_uni Γ))
  (PCat.forgetPoint)
  ((Down_uni Γ) ⋙ A) := by
    fconstructor
    · constructor
      exact Comm A
    · constructor
      exact GrothendieckLimisLim A

end GrothendieckPullBack


section PointedPullBack
/-
In this section we prove that the following square is a PullBack

      PGrpd---PGrpd.forgetToCat--->PCat
        |                           |
        |                           |
 PGrpd.forgetPoint           PCat.forgetPoint
        |                           |
        v                           v
      Grpd----Grpd.forgetToCat---->Cat
-/

/-This is the proof that the diagram commutes-/
theorem PComm : PGrpd.forgetToCat.{u,u} ⋙ PCat.forgetPoint.{u,u} = PGrpd.forgetPoint.{u,u} ⋙ Grpd.forgetToCat.{u,u} := by
  simp[PGrpd.forgetToCat,PCat.forgetPoint,PGrpd.forgetPoint,Grpd.forgetToCat,Functor.comp]
  congr

-- This is the type of cones
abbrev PointedCones := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} Grpd.{u,u})
  (Cat.of.{u,u+1} PCat.{u,u})
  (Cat.of.{u,u+1} Cat.{u,u})
  (Grpd.forgetToCat)
  PCat.forgetPoint.{u,u}

-- This is the cone we will show to be the limit
abbrev PointedLim : PointedCones :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of.{u,u+1} Grpd.{u,u})
    (Cat.of.{u,u+1} PCat.{u,u})
    (Cat.of.{u,u+1} Cat.{u,u})
    (Grpd.forgetToCat)
    PCat.forgetPoint.{u,u}
    (Cat.of PGrpd)
    PGrpd.forgetPoint
    PGrpd.forgetToCat
    PComm

/-- This is the construction of the universal map for the limit-/
def Pointed.UnivesalMap (C : Cat.{u,u+1}) (F1 : C ⥤ PCat.{u,u})(F2 : C ⥤ Grpd.{u,u})(Comm : F1 ⋙ PCat.forgetPoint = F2 ⋙ Grpd.forgetToCat) : C ⥤ PGrpd where
  obj x := by
    fapply PGrpd.fromGrpd
    · exact F2.obj x
    · have eq := Functor.congr_obj Comm x
      simp [PCat.forgetPoint, Grpd.forgetToCat,Cat.of,Bundled.of] at eq
      have eq' := congrArg Bundled.α eq
      simp at eq'
      rw [<- eq']
      exact (F1.obj x).str.pt
  map f := by
    simp [Quiver.Hom]
    fconstructor
    · exact F2.map f
    · rename_i X Y
      have r1 := (ForgetPointFunctor (F1.obj Y)).map ((F1.map f).point)
      have r2 := (CastFunc Comm Y).functor.map r1
      refine eqToHom ?A ≫ r2 ≫ eqToHom ?B
      · sorry
      · sorry

/- The proof of uniquness of the universal map-/
def Pointed.UnivesalMap_Uniq (s : PointedCones) : s ⟶ PointedLim := by
  refine { hom := ?hom, w := ?w }
  · sorry
  · sorry

/- The proof that PointedLim is a limit-/
def PointedLimisLim : Limits.IsLimit PointedLim := by
  refine Limits.PullbackCone.isLimitAux' PointedLim ?_
  intros s
  fconstructor
  · sorry
  · refine ⟨?_,?_,?_⟩
    · sorry
    · sorry
    · sorry

end PointedPullBack
end Pullbacks

def CatLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
    obj x := Cat.of (ULift.{u + 1, u} ↑x)
    map {x y} f := (Down_uni x) ⋙ f ⋙ (Up_uni y)

def CatLift_BackDown (C : Cat.{u,u}) : CatLift.obj C ⥤ C where
    obj x := x.down
    map f := f

def CatLift_BackUp (C : Cat.{u,u}) : C ⥤ CatLift.obj C where
    obj x := {down := x}
    map f := f

namespace PshGrpd

variable (C D) [Category.{u} C] [Category.{u} D]

def ι : Grpd.{u, u} ⥤ Cat.{u,u+1} := Grpd.forgetToCat ⋙ CatLift

-- def κ : Grpd.{u, u} ⥤ Cat.{u,u} := Grpd.forgetToCat

-- lemma κ_yoneda_whiskeringLeft_κ_eq_yoneda :
--   κ.{u} ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj κ.op = yoneda := rfl

def ofCat : Cat.{u,u+1} ⥤ (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj ι.op

instance ofCatPreservesLim : Limits.PreservesLimits ofCat := by
  dsimp [ofCat,Limits.PreservesLimits]
  refine @Limits.compPreservesLimits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact yonedaFunctorPreservesLimits
  · refine @Adjunction.rightAdjointPreservesLimits ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · refine @Functor.lan ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact (Grpd.forgetToCat.op ⋙ CatLift.op)
      · intro F
        exact Functor.instHasLeftKanExtension (Grpd.forgetToCat.op ⋙ CatLift.op) F
    · exact (Grpd.forgetToCat.op ⋙ CatLift.op).lanAdjunction (Type (u + 1))

end PshGrpd

open PshGrpd

-- This is a Covariant Functor that takes a Groupoid Γ to Γ ⥤ Grpd
def Ty_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := x.unop ⥤ Grpd.{u,u}
  map f A := f.unop ⋙ A

def Ty_functor_iso_ofCat_Grpd : Ty_functor ≅ ofCat.obj (Cat.of Grpd.{u,u}) where
  hom := by
    fconstructor
    · unfold Ty_functor
      unfold ofCat
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackDown (Grpd.forgetToCat.obj X)
      · exact 𝟭 Grpd
    · simp [Ty_functor,ofCat]
      intros X Y f
      exact rfl
  inv := by
    fconstructor
    · unfold Ty_functor
      unfold ofCat
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackUp (Grpd.forgetToCat.obj X)
      · exact 𝟭 Grpd
    · simp [Ty_functor,ofCat]
      intros X Y f
      exact rfl

-- This is a Covariant Functor that takes a Groupoid Γ to Γ ⥤ PointedGroupoid
def Tm_functor : Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1) where
  obj x := x.unop ⥤ PGrpd.{u,u}
  map f A := f.unop ⋙ A

-- I am not sure if this iso will be helpfull but it works as a sanity check to make sure Tm is defined correctly
def Tm_functor_iso_ofCat_PGrpd : Tm_functor ≅ ofCat.obj (Cat.of PGrpd.{u,u}) where
  hom := by
    fconstructor
    · unfold Tm_functor
      unfold ofCat
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackDown (Grpd.forgetToCat.obj X)
      · exact 𝟭 PGrpd
    · simp [Ty_functor,ofCat]
      intros X Y f
      exact rfl
  inv := by
    fconstructor
    · unfold Tm_functor
      unfold ofCat
      intro X F
      rcases X with ⟨X⟩
      refine ?_ ⋙ F ⋙ ?_
      · refine CatLift_BackUp (Grpd.forgetToCat.obj X)
      · exact 𝟭 PGrpd
    · simp [Ty_functor,ofCat]
      intros X Y f
      exact rfl

-- This is the typing natural transformation
def tp_NatTrans : Tm_functor ⟶ Ty_functor where
  app x := by
    intro a
    exact a ⋙ PGrpd.forgetPoint

-- This is the var construction of var before applying yoneda
def var' (Γ : Grpd)(A : Γ ⥤ Grpd) : (GroupoidalGrothendieck A) ⥤ PGrpd where
  obj x := ⟨(A.obj x.base), (PointedGroupoid.of (A.obj x.base) x.fiber)⟩
  map f := ⟨A.map f.base, f.fiber⟩
  map_id x := by
    dsimp
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    dsimp [GroupoidalGrothendieck] at x ⊢
    apply PointedFunctor.ext <;>
      simp only [PGrpd.id_toFunctor, Functor.id_obj, PGrpd.id_point,
        Category.comp_id, Functor.map_id]
    rfl
  map_comp {x y z} f g := by
    dsimp [GroupoidalGrothendieck]
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    let _ := (PointedCategory.of (A.obj z.base) z.fiber)
    apply PointedFunctor.ext
    . simp [A.map_comp, Grothendieck.comp_fiber, Grpd.forgetToCat]
    . simp; rfl

/-

GGrothendieck A -----var'--------> PGrpd---PGrpd.forgetToCat--->PCat
        |                             |                           |
        |                             |                           |
GGrothendieck.forget           PGrpd.forgetPoint         PCat.forgetPoint
        |                             |                           |
        v                             v                           v
        Γ--------------A-----------> Grpd----Grpd.forgetToCat---->Cat
-/

theorem LeftSquareComutes {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : (Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A) ⋙ PGrpd.forgetPoint
 = ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ)) ⋙ (Down_uni Γ) ⋙ A := by sorry

-- This is the type of cones
abbrev GroupoidCones {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) := @CategoryTheory.Limits.PullbackCone
  Cat.{u,u+1} _
  (Cat.of.{u,u+1} (ULift.{u+1,u} Γ))
  (Cat.of.{u,u+1} PGrpd.{u,u})
  (Cat.of.{u,u+1} Grpd.{u,u})
  ((Down_uni Γ) ⋙ A)
  PGrpd.forgetPoint.{u,u}

-- This is the cone we will prove is the limit
abbrev GroupoidLim {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}): (GroupoidCones A) :=
  @Limits.PullbackCone.mk Cat.{u,u+1} _
    (Cat.of (ULift.{u + 1, u} Γ))
    (Cat.of PGrpd.{u,u})
    (Cat.of Grpd.{u,u})
    ((Down_uni Γ) ⋙ A)
    (PGrpd.forgetPoint.{u,u})
    (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A)))
    (Down_uni (GroupoidalGrothendieck A) ⋙ GroupoidalGrothendieck.forget ⋙ Up_uni Γ)
    ((Down_uni (GroupoidalGrothendieck A)) ⋙ var' Γ A)
    (LeftSquareComutes A)

-- CategoryTheory.Limits.leftSquareIsPullback.{v, u} {C : Type u} [Category.{v, u} C] {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂}
--   {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃} {t₂ : Limits.PullbackCone g₂ i₃} {i₂ : t₂.pt ⟶ Y₂} (t₁ : Limits.PullbackCone g₁ i₂)
--   (hi₂ : i₂ = t₂.fst) (H : Limits.IsLimit t₂) (H' : Limits.IsLimit (t₂.pasteHoriz t₁ hi₂)) : Limits.IsLimit t₁
def PBasLim {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : Limits.IsLimit (GroupoidLim A) := by
  dsimp [GroupoidLim]
  refine Limits.leftSquareIsPullback (C := Cat.{u,u+1})
    (X₃ := Cat.of PCat.{u,u})
    (Y₁ := Cat.of (ULift.{u+1,u} Γ))
    (Y₂ := Cat.of Grpd.{u,u})
    (Y₃ := Cat.of Cat.{u,u})
    (g₂ := Grpd.forgetToCat)
    (g₁ := (Down_uni Γ) ⋙ A)
    (i₂ := PGrpd.forgetPoint)
    (i₃ := PCat.forgetPoint)
    (t₁ := GroupoidLim _)
    ?_
    PointedLimisLim
    ?H'
  sorry
  sorry

def PBasPB {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : @IsPullback (Cat.{u,u+1}) _
  (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A)))
  (Cat.of PGrpd.{u,u})
  (Cat.of (ULift.{u+1,u} Γ))
  (Cat.of Grpd.{u,u})
  ((Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A))
  ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ))
  (PGrpd.forgetPoint)
  ((Down_uni Γ) ⋙ A) := by
    refine IsPullback.flip ?_ -- This filips the pullback, There is on that is done sidways further up that should be fixed
    fconstructor
    · constructor
      exact LeftSquareComutes A
    · constructor
      exact PBasLim A


def ofCatPB {Γ : Grpd.{u,u}}(A : Γ ⥤ Grpd.{u,u}) : @IsPullback (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) _
  (ofCat.obj (Cat.of (ULift.{u+1,u} (GroupoidalGrothendieck A))))
  (ofCat.obj (Cat.of PGrpd.{u,u}))
  (ofCat.obj (Cat.of (ULift.{u+1,u} Γ)))
  (ofCat.obj (Cat.of Grpd.{u,u}))
  (ofCat.map ((Down_uni (GroupoidalGrothendieck A)) ⋙ (var' Γ A)))
  (ofCat.map ((Down_uni (GroupoidalGrothendieck A)) ⋙ (GroupoidalGrothendieck.forget) ⋙ (Up_uni Γ)))
  (ofCat.map (PGrpd.forgetPoint))
  (ofCat.map ((Down_uni Γ) ⋙ A)) := Functor.map_isPullback ofCat (PBasPB A)

end


end CategoryTheory
