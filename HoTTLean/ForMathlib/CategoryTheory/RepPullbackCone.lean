import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import HoTTLean.ForMathlib.CategoryTheory.WeakPullback

/-!
  This file builds API for showing that a presheaf diagram is a pullback
  by its universal property among representable cones.
-/

universe u v u₁ v₁ u₂ v₂

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

def repConeOfConeMap (s : Cone F) (c : C) (x' : yoneda.obj c ⟶ s.pt) : RepCone F :=
  { pt := c
    π := {app := λ j ↦ x' ≫ s.π.app j}}

namespace RepIsLimit

variable {t : Cone F} (P : RepIsLimit t) {s : Cone F}

def lift' (c : C) (x' : yoneda.obj c ⟶ s.pt) : yoneda.obj c ⟶ t.pt :=
  P.lift $ repConeOfConeMap s c x'

@[simp] lemma lift'_naturality {s : Cone F} {c d : C}
    (f : c ⟶ d) (x' : yoneda.obj d ⟶ s.pt) :
    lift' P c (yoneda.map f ≫ x') = yoneda.map f ≫ lift' P d x' := by
  apply Eq.symm
  apply P.uniq (repConeOfConeMap s c (yoneda.map f ≫ x')) (yoneda.map f ≫ lift' P d x')
  intro j
  have h := P.fac (repConeOfConeMap s d x') j
  dsimp[repConeOfConeMap]
  dsimp[repConeOfConeMap] at h
  rw[Category.assoc, Category.assoc, ← h]
  rfl

def lift''_app (s : Cone F) (c : C) :
    s.pt.obj (Opposite.op c) ⟶ t.pt.obj (Opposite.op c) :=
  ConcreteCategory.ofHom (TypeCat.Fun.mk (yonedaEquiv ∘ lift' P c ∘ yonedaEquiv.symm))

theorem lift''_app_naturality {c d : C} (f : c ⟶ d) :
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

theorem fac_ext (j : J) (c : C) (x) :
    (lift'' P s ≫ t.π.app j).app (Opposite.op c) x
    = (s.π.app j).app (Opposite.op c) x := by
  dsimp [lift'',lift', lift''_app, ← yonedaEquiv_comp]
  rw [P.fac (repConeOfConeMap s c (yonedaEquiv.symm x)) j]
  simp [repConeOfConeMap, yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv x]

theorem uniq_ext (m : s.pt ⟶ t.pt)
    (hm : ∀ (j : J), m ≫ t.π.app j = s.π.app j) (c : C) (x) :
    m.app (Opposite.op c) x
    = (P.lift'' s).app (Opposite.op c) x := by
  let x' := yonedaEquiv.symm x
  have hj : (∀ (j : J), (x' ≫ m) ≫ t.π.app j = x' ≫ s.π.app j) := by simp[hm]
  have h := P.uniq (repConeOfConeMap s c x') (x' ≫ m) hj
  dsimp [lift'', lift''_app, lift']
  rw [← h, yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv x]

def IsLimit {t : Cone F} (P : RepIsLimit t) : IsLimit t where
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

variable {W X Y Z : Cᵒᵖ ⥤ Type v₃}
  {f : X ⟶ Z} {g : Y ⟶ Z} (t : RepPullbackCone f g)

def mk (W : C) (fst : yoneda.obj W ⟶ X) (snd : yoneda.obj W ⟶ Y)
    (h : fst ≫ f = snd ≫ g) :
    RepPullbackCone f g :=
  repConeOfConeMap (PullbackCone.mk fst snd h) W (𝟙 _)

def pullbackCone : PullbackCone f g where
  pt := yoneda.obj t.pt
  π  := t.π

/-- The first projection of a pullback cone. -/
abbrev fst : yoneda.obj t.pt ⟶ X :=
  t.pullbackCone.fst

/-- The second projection of a pullback cone. -/
abbrev snd : yoneda.obj t.pt ⟶ Y :=
  t.pullbackCone.snd

@[simp]
lemma fst_mk (W : C) (fst : yoneda.obj W ⟶ X) (snd : yoneda.obj W ⟶ Y)
    (h : fst ≫ f = snd ≫ g) :
    (mk W fst snd h).pullbackCone.fst = fst :=
  rfl

@[simp]
lemma snd_mk (W : C) (fst : yoneda.obj W ⟶ X) (snd : yoneda.obj W ⟶ Y)
    (h : fst ≫ f = snd ≫ g) :
    (mk W fst snd h).pullbackCone.snd = snd :=
  rfl

@[reassoc]
theorem condition : t.fst ≫ f = t.snd ≫ g :=
  t.pullbackCone.condition

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom Limits.PullbackCone

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

/-- To show that a `PullbackCone` in a presheaf category constructed using `PullbackCone.mk` is a limit cone,
  it suffices to show its universal property among representable cones.
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

theorem is_pullback {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : RepPullbackCone f g, yoneda.obj s.pt ⟶ W)
    (fac_left : ∀ s : RepPullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : RepPullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : RepPullbackCone f g) (m : yoneda.obj s.pt ⟶ W)
      (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsPullback fst snd f g :=
  IsPullback.of_isLimit' ⟨ eq ⟩ (RepIsLimit.mk eq lift fac_left fac_right uniq)

namespace WeakPullback

variable {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : RepPullbackCone f g, yoneda.obj s.pt ⟶ W)
    (fac_left : ∀ s : RepPullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : RepPullbackCone f g, lift s ≫ snd = s.snd)
    (lift_naturality : ∀ (s : RepPullbackCone f g) {c} (σ : c ⟶ s.pt),
      yoneda.map σ ≫ lift s = lift (.mk c (yoneda.map σ ≫ s.fst) (yoneda.map σ ≫ s.snd)
      (by simp [s.condition])))

section
variable {G : Cᵒᵖ ⥤ Type v₃} (a : G ⟶ X) (b : G ⟶ Y) (hab : a ≫ f = b ≫ g)

open Opposite

def repPullbackCone (c : C) (x : G.obj (op c)) : RepPullbackCone f g :=
  .mk c (yonedaEquiv.symm $ a.app (op c) x) (yonedaEquiv.symm $ b.app (op c) x) (by
    simpa [yonedaEquiv_symm_naturality_right] using
      congrArg (fun η => (ConcreteCategory.hom η) x) (NatTrans.congr_app hab (op c)))

def lift'.app (c : C) : G.obj (op c) ⟶ W.obj (op c) :=
  ConcreteCategory.ofHom (TypeCat.Fun.mk (fun x =>
    yonedaEquiv (lift (repPullbackCone a b hab c x))))

include lift_naturality in
lemma lift'.naturality ⦃c d : C⦄ (σ : c ⟶ d) :
    G.map σ.op ≫ lift'.app lift a b hab c =
    lift'.app lift a b hab d ≫ W.map σ.op := by
  ext x
  change yonedaEquiv (lift (repPullbackCone a b hab c ((ConcreteCategory.hom (G.map σ.op)) x))) =
    (ConcreteCategory.hom (W.map σ.op)) (yonedaEquiv (lift (repPullbackCone a b hab d x)))
  rw [yonedaEquiv_naturality, lift_naturality (repPullbackCone a b hab d x) σ]
  dsimp only [repPullbackCone, π_app_left, fst_mk, π_app_right, snd_mk]
  congr 3
  · rw [yonedaEquiv_symm_naturality_left σ]
    simpa using congr_fun (a.naturality σ.op) x
  · rw [yonedaEquiv_symm_naturality_left σ]
    simpa using congr_fun (b.naturality σ.op) x

include lift_naturality in
def lift' : G ⟶ W where
  app c := lift'.app lift a b hab c.unop
  naturality _ _ σ := lift'.naturality lift lift_naturality a b hab σ.unop

end

def mk : WeakPullback fst snd f g where
  w := eq
  lift a b hab := WeakPullback.lift' lift lift_naturality a b hab
  lift_fst' a b hab := by
    ext c x
    dsimp [lift', lift'.app]
    have h := fac_left (repPullbackCone a b hab (c.unop) x)
    simp only [π_app_left, π_app_right, repPullbackCone, Opposite.op_unop, fst_mk] at *
    erw [Equiv.eq_symm_apply] at h
    exact h
  lift_snd' a b hab := by
    ext c x
    dsimp [lift', lift'.app]
    have h := fac_right (repPullbackCone a b hab (c.unop) x)
    simp only [π_app_left, π_app_right, repPullbackCone, Opposite.op_unop, snd_mk] at *
    erw [Equiv.eq_symm_apply] at h
    exact h

end WeakPullback

open WeakPullback

end RepPullbackCone

end Limits
