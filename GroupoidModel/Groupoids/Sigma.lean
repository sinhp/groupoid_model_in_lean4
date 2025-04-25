import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma
import SEq.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

namespace CategoryTheory

namespace Grpd

@[simp] theorem id_obj {C : Grpd} (X : C) :
    (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp] theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E)
    (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

variable {Γ : Type u} [Category.{v} Γ] (F : Γ ⥤ Grpd.{v₁,u₁})

@[simp] theorem map_eqToHom_obj {x y : Γ} (h : x = y) (t) :
    (F.map (eqToHom h)).obj t = cast (by rw [h]) t := by
  subst h
  simp

-- set_option pp.proofs true
@[simp] theorem map_eqToHom_map {x y : Γ} (h : x = y) {t s} (f : t ⟶ s) :
    (F.map (eqToHom h)).map f =
    eqToHom (Functor.congr_obj (eqToHom_map _ _) t)
    ≫ cast (Grpd.eqToHom_hom_aux t s (by rw [h])) f
    ≫ eqToHom (Eq.symm (Functor.congr_obj (eqToHom_map _ _) s)) := by
  have h1 : F.map (eqToHom h) = eqToHom (by rw [h]) := eqToHom_map _ _
  rw [Functor.congr_hom h1, Grpd.eqToHom_hom]

end Grpd

end CategoryTheory

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

notation:max "@(" Γ ")" => Ctx.toGrpd.obj Γ

namespace FunctorOperation

/--
For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd`
-/
abbrev sigmaObj {Γ : Grpd.{v₂,u₂}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ) := ∫(ι A x ⋙ B)

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
def sigmaMap {Γ : Grpd.{v₂,u₂}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) {x y : Γ} (f : x ⟶ y) :
    sigmaObj B x ⥤ sigmaObj B y :=
  map (whiskerRight (ιNatTrans f) B) ⋙ pre (ι A y ⋙ B) (A.map f)

def sigma_map_id {Γ : Grpd.{v₂,u₂}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {B : ∫(A) ⥤ Grpd.{v₁,u₁}} (x : Γ) :
    (sigmaMap B) (CategoryStruct.id x) = Functor.id _ := by
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
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp only [Functor.comp_map, Functor.id_map]
      apply Grothendieck.Groupoidal.ext
      · simp only [pre_map_fiber, map_map_fiber, whiskerRight_app, eqToHom_trans_assoc, comp_fiber, eqToHom_fiber, eqToHom_map]
        -- NOTE rw! much faster here for map_eqToHom_map and Functor.congr_hom
        rw! [Functor.congr_hom (h p2.base) f.fiber, eqToHom_base,
          Grpd.map_eqToHom_map, Grpd.eqToHom_hom]
        -- NOTE ι_obj, ι_map really unhelpful when there is an eqToHom
        simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      · simp [Grpd.map_id_map]
    · intro p
      simp only [Functor.comp_obj, map_obj, Functor.id_obj]
      apply obj_ext_hEq
      · rw [pre_obj_base, Grpd.map_id_obj]
      · simp

-- TODO: Fix performance issue.
set_option maxHeartbeats 0 in
/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.

  For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd` -/
@[simps] def sigma {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : Γ ⥤ Grpd.{v₁,u₁} where
  -- NOTE using Grpd.of here instead of earlier speeds things up
  obj x := Grpd.of $ sigmaObj B x
  map := sigmaMap B
  map_id := sigma_map_id
  map_comp := by sorry
--     intro x y z f g
--     have h (a : A.obj x) : B.map ((Grothendieck.ιNatTrans (f ≫ g)).app a)
--         = B.map ((Grothendieck.ιNatTrans f).app a)
--         ⋙ B.map (eqToHom (by
--           simp [Grpd.forgetToCat]))
--         ⋙ B.map ((Grothendieck.ιNatTrans g).app ((A.map f).obj a))
--         ⋙ B.map (eqToHom (by
--           simp [Grpd.forgetToCat, Grpd.comp_eq_comp])) := by
--       simp only [Grothendieck.ιNatTrans_comp_app, Functor.map_comp,
--         eqToHom_map, CategoryTheory.Functor.map_id]
--       rfl
--     simp only [Grothendieck.Groupoidal.pre, Grothendieck.pre]
--     apply CategoryTheory.Functor.ext
--     · sorry
--     · intro p
--       simp only [Grpd.coe_of, Functor.comp_obj, Functor.comp_map]
--       congr 1
--       · rw [Grpd.map_comp_obj]
--         rfl
--       · simp [map, Grpd.forgetToCat, Functor.congr_obj (h p.base) p.fiber,
--         eqToHom_refl, eqToHom_map, Grpd.eqToHom_obj, Grpd.id_eq_id, Functor.id_obj]

#exit
section

variable {Δ Γ: Grpd.{v₂,u₂}} (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{v₁,u₁})


theorem sigmaBeckChevalley (B : ∫(A) ⥤ Grpd.{v₁,u₁})
    : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . intros x
    dsimp only [Functor.comp_obj, sigma_obj]
    rw [← Grothendieck.Groupoidal.ιCompPre σ A x]
    rfl
  . intros x y f
    sorry -- this goal might be improved by adding API for Groupoidal.ι and Groupoidal.pre
end

-- TODO replaced with Grothendieck.eqToHom_eq
-- def eqToHomGrdik {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{v₁,v₂}} {X Y : Grothendieck F} {h : X = Y} :
--   eqToHom h = {base := eqToHom (congrArg (fun(x) => x.base) h), fiber := (eqToHom (by cases h; simp) )} := by
--   rcases h
--   simp[CategoryStruct.id,Grothendieck.id]

set_option maxHeartbeats 0 in
def pairSection {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B)
    : Γ ⥤ ∫(sigma (α ⋙ PGrpd.forgetToGrpd) B) where
    obj x := ⟨ x, (α.obj x).str.pt, PGrpd.compForgetToGrpdObjPt h x ⟩
    map {x y} f :=
      have := by
        dsimp only [Functor.comp_obj, ι, Grpd.forgetToCat,
          Functor.comp_map, sigma_map, id_eq, Grothendieck.ιNatTrans, map, Grothendieck.Groupoidal.pre,
          Grothendieck.pre_obj_fiber, Grothendieck.map_obj_fiber, whiskerRight_app]
        simp only [← Grpd.map_comp_obj, CategoryStruct.comp, Grothendieck.comp]
        apply Functor.congr_obj
        congr 2
        · simp
        · simp [Grpd.forgetToCat, Grothendieck.IsMegaPullback.point]
    ⟨ f, (α.map f).point, eqToHom this ≫ PGrpd.compForgetToGrpdMapPoint h f ⟩
    map_id x := by
      fapply Grothendieck.ext
      . rfl
      . simp only [eqToHom_refl, Category.id_comp, CategoryStruct.id, Grothendieck.id]
        rw [Grothendieck.eqToHom_eq]
        fapply Grothendieck.ext
        . refine Eq.trans (PointedFunctor.congr_point (α.map_id x)) ?_
          simp [CategoryStruct.id]
        . simp [PGrpd.compForgetToGrpdMapPoint, PointedFunctor.congr_point (β.map_id x), eqToHom_map]
    map_comp f g := by
      fapply Grothendieck.ext
      . rfl
      . dsimp
        simp only [Category.id_comp]
        · apply Grothendieck.ext
          . -- simp only [ι, Grpd.forgetToCat, Functor.comp_obj, Grothendieck.ι_obj, Cat.of_α, Grpd.coe_of, id_eq,
            --   Grothendieck.ιNatTrans, PGrpd.forgetToGrpd_obj, Functor.comp_map,
            --   PGrpd.forgetToGrpd_map, map, whiskerRight_twice,
            --   Grothendieck.Groupoidal.pre, Grothendieck.pre_obj_base, Grothendieck.map_obj_base, Grothendieck.ι_map,
            --   Grothendieck.pre_obj_fiber, Grothendieck.map_obj_fiber, whiskerRight_app, Grpd.forgetToGrpdMapPoint,
            --   Grothendieck.comp_base, Grothendieck.pre_map_base, Grothendieck.map_map_base, eqToHom_trans_assoc,
            --   Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom, eqToHom_map, Grothendieck.pre_map_fiber,
            --   Grothendieck.map_map_fiber, Functor.map_comp, Category.assoc]
            -- have h3 : β.map (f ≫ g) = _ := Functor.map_comp _ _ _
            -- have h4 : Grpd.homOf (β.map g).toFunctor = _ := Functor.congr_hom h g
            -- simp only [Grpd.homOf] at h4
            -- simp only [PointedFunctor.congr_point h3, PGrpd.comp_toFunctor, Functor.comp_obj, PGrpd.comp_point,
            --   Category.assoc]
            -- rw [Functor.congr_hom h4 (β.map f).point]
            -- simp only [Grpd.comp_eq_comp, Functor.map_comp]
            -- simp only [eqToHom_map]
            -- simp only [Grothendieck.Groupoidal.sec, IsMegaPullback.lift,
            --   Grothendieck.IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift_map]
            sorry
          . simp [Grpd.forgetToCat, Grothendieck.Groupoidal.pre, map, PGrpd.map_comp_point]

theorem pairSection_comp_forget {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B) :
     (pairSection α β B h) ⋙ Grothendieck.forget _ = Functor.id Γ := rfl

def pair {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B)
    : Γ ⥤ PGrpd.{v₁,u₁} := pairSection α β B h ⋙ toPGrpd _

theorem pair_comp_forget {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : ∫(α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B) :
    pair α β B h ⋙ PGrpd.forgetToGrpd = sigma (α ⋙ PGrpd.forgetToGrpd) B := by
  unfold pair
  rw [Functor.assoc]
  exact rfl

def fstAux {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : sigma A B ⟶ A where
  app x := Grpd.homOf (Grothendieck.forget _)

def fst {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : ∫(sigma A B) ⥤ ∫(A) :=
  map (fstAux B)

-- def fst {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
--     (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁}) :
--   Grothendieck.Groupoidal (sigma A B) ⥤  Grothendieck.Groupoidal A where
--   obj x := ⟨x.base,x.fiber.base⟩
--   map {x y} f := ⟨f.base, f.fiber.base⟩
--   map_id x := by
--     fapply Grothendieck.ext
--     . simp
--     . simp only [Grothendieck.id_fiber, eqToHom_refl, Category.id_comp]
--       rw [Grothendieck.eqToHom_eq]
--   map_comp f g := by
--     fapply Grothendieck.ext
--     · simp
--     · simp only [Functor.comp_obj, sigma_obj, Functor.comp_map, sigma_map, Grpd.coe_of, Grothendieck.comp_base,
--   Grothendieck.comp_fiber, Cat.comp_obj, eqToHom_refl, Category.id_comp]
--       sorry

def snd {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : ∫(sigma A B) ⥤ PGrpd := sorry

-- NOTE this is false using (toPGrpd (sigma A B)) instead of `snd`
lemma snd_forgetToGrpd {Γ : Grpd}
    {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}} {B : ∫(A) ⥤ Grpd.{v₁,u₁}} :
    snd B ⋙ PGrpd.forgetToGrpd = fst B ⋙ B := by
  unfold fst

  sorry

-- JH: changed name from `snd` to `assoc`
-- maybe we should use `Grothendieck.functorFrom`
def assoc {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) :
    ∫(sigma A B) ⥤ ∫(B) :=
  IsMegaPullback.lift (snd B) (fst B)
    snd_forgetToGrpd

-- set_option maxHeartbeats 0 in
-- def snd {Γ : Grpd} (A : Γ ⥤ Cat.of Grpd.{v₁,u₁})
--     (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁}) :
--   Grothendieck.Groupoidal (sigma A B) ⥤  Grothendieck.Groupoidal B where
--   obj x := by
--     rcases x with ⟨base,fiber,fiberfiber⟩
--     fconstructor
--     fconstructor
--     . exact base
--     . exact fiber
--     . exact fiberfiber
--   map {x y} f := by
--     rcases f with ⟨base,fiber,fiberfiber⟩
--     fconstructor
--     fconstructor
--     . exact base
--     . exact fiber
--     . refine eqToHom ?_ ≫ fiberfiber
--       . simp[Grpd.forgetToCat,Grothendieck.Groupoidal.pre,whiskerRight,map]
--         set I := ((ι A y.base).map fiber)
--         set J := (@Grothendieck.ιNatTrans (↑Γ) Groupoid.toCategory (Groupoid.compForgetToCat A) x.base y.base base).app x.fiber.base
--         have eq1 : (B.map I).obj ((B.map J).obj x.fiber.fiber) = (B.map J ≫ B.map I).obj x.fiber.fiber := rfl
--         rw [eq1,<- B.map_comp J I]
--         simp[J,I,CategoryStruct.comp,Grothendieck.comp,ι]
--         refine Functor.congr_obj ?_ x.fiber.fiber
--         refine congrArg B.map ?_
--         apply Grothendieck.ext
--         . simp
--         . simp
--   map_id := by
--     intro x
--     simp[Grothendieck.Hom.rec,Grothendieck.Hom.rec]
--     sorry
--   map_comp := sorry

def ABToAlpha {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) :
  ∫(sigma A B) ⥤ PGrpd :=
  fst B ⋙ toPGrpd A

def ABToB {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) :
    ∫(ABToAlpha B ⋙ PGrpd.forgetToGrpd) ⥤ Grpd := by
  refine ?_ ⋙ fst B ⋙ B
  exact Grothendieck.forget (Groupoid.compForgetToCat (ABToAlpha B ⋙ PGrpd.forgetToGrpd))

def ABToBeta {Γ : Grpd} {A : Γ ⥤ Cat.of Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ (Grothendieck.Groupoidal.toPGrpd B)

end FunctorOperation

open FunctorOperation

/-- The formation rule for Σ-types for the ambient natural model `base` -/
def baseSig : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun p =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv p
    yonedaEquiv (yonedaCatEquiv.symm (sigma A B))
  naturality := sorry -- do not attempt

def basePair : base.uvPolyTp.compDom base.uvPolyTp ⟶ base.Tm where
  app Γ := fun ε =>
    let ⟨α,B,β,h⟩ := baseUvPolyTpCompDomEquiv ε
    yonedaEquiv (yonedaCatEquiv.symm (pair α β B h))
  naturality := by sorry

def Sigma_Comm : basePair ≫ base.tp = (base.uvPolyTp.comp base.uvPolyTp).p ≫ baseSig := by sorry

def PairUP' {Γ : Ctx.{u}} (AB : yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty) :
    yoneda.obj (base.ext (AB ≫ baseSig)) ⟶ base.uvPolyTp.compDom base.uvPolyTp := by
  -- sorry
  refine yonedaEquiv.invFun ?_
  refine baseUvPolyTpCompDomEquiv.invFun ?_
  let AB' := baseUvPolyTpEquiv (yonedaEquiv.toFun AB)
  exact ⟨ABToAlpha AB'.snd, ABToB AB'.snd, ABToBeta AB'.snd, by
    -- simp
    sorry
  ⟩

-- NOTE this has been refactored through sec'
-- def GammaToSigma {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
--     (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
--     (h : top ≫ base.tp = left ≫ baseSig) :
--     (yoneda.obj Γ) ⟶ yoneda.obj (base.ext (left ≫ baseSig)) :=
--   (base.disp_pullback (left ≫ baseSig)).lift top (𝟙 _) (by rw[Category.id_comp,h])

-- def GammaToSigmaInv_disp {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : (base.sec' top _ h) ≫ (yoneda.map (base.disp (left ≫ baseSig))) = 𝟙 (yoneda.obj Γ) := by
--   simp [sec']

def PairUP {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
    (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
    (h : top ≫ base.tp = left ≫ baseSig) :
    (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp :=
  base.sec' h ≫ (PairUP' left)

namespace SigmaPullback

def somethingEquiv' {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
  (A : (Ctx.toGrpd.obj Γ) ⥤ Grpd.{u,u})
  (B : ∫(A) ⥤ Grpd.{u,u})
  (sigAB : ↑(Ctx.toGrpd.obj Γ) ⥤ Grpd.{u,u})
  (ab : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
  (h : ab ⋙ PGrpd.forgetToGrpd = sigAB) :
  (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u}) ×'
  (α ⋙ PGrpd.forgetToGrpd = A) := sorry

theorem yonedaCatEquiv_baseSig {Γ : Ctx} {A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}}
    {B : ∫(A) ⥤ Grpd.{u,u}} :
    yonedaCatEquiv ((baseUvPolyTpEquiv'.symm ⟨A,B⟩) ≫ baseSig) = sigma A B
    := by
  simp only [yonedaCatEquiv, Equiv.trans_apply, yonedaEquiv_comp, baseSig, Equiv.symm_trans_apply, Equiv.toFun_as_coe, baseUvPolyTpEquiv]
  rw [yonedaCatEquivAux.apply_eq_iff_eq_symm_apply,
    yonedaEquiv.apply_eq_iff_eq_symm_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  congr

def somethingEquiv {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
    {AB : y(Γ) ⟶ base.Ptp.obj base.{u}.Ty}
    (h : ab ≫ base.tp = AB ≫ baseSig)
    : (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u})
    × (α : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    × (B : ∫(A) ⥤ Grpd.{u,u})
    × (β : Ctx.toGrpd.obj Γ ⥤ PGrpd.{u,u})
    ×' (h : α ⋙ PGrpd.forgetToGrpd = A)
    ×' β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ Grothendieck.Groupoidal.map (eqToHom h) ⋙ B :=
  let AB' := baseUvPolyTpEquiv (yonedaEquiv AB)
  let A := AB'.1
  let B := AB'.2
  let h1 := baseTmEquiv ⟨AB ≫ baseSig,ab,h⟩
  let sigAB := h1.1
  let ab' := h1.2.1
  let hab := h1.2.2
  have h2 : ab' ⋙ PGrpd.forgetToGrpd = sigma AB'.fst B := by
      rw [hab, baseTmEquiv_fst, ← yonedaCatEquiv_baseSig, Sigma.eta]
      simp [AB', baseUvPolyTpEquiv]
  let α := sec ab' ⋙ map (eqToHom h2) ⋙ fst B ⋙ toPGrpd A
  ⟨ A,
    α,
    B,
    sorry,
    sorry,
    sorry ⟩

-- strategy: want to first show that cones of the diagram
-- correspond to some functor data,
-- then do the functor constructions
def lift {Γ : Ctx} {ab : y(Γ) ⟶ base.Tm}
    {AB : y(Γ) ⟶ base.Ptp.obj base.{u}.Ty}
    (h : ab ≫ base.tp = AB ≫ baseSig) :
    (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp :=
  yonedaEquiv.invFun $
  baseUvPolyTpCompDomEquiv'.invFun
  (somethingEquiv h)

end SigmaPullback

theorem PairUP_Comm1' {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : PairUP' left ≫ basePair = (yoneda.map (base.disp (left ≫ baseSig))) ≫ top := by
  sorry

theorem PairUP_Comm1 {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : (PairUP top left h) ≫ basePair = top := by
  unfold PairUP
  rw[Category.assoc,PairUP_Comm1' top left h,<- Category.assoc,
    sec'_disp,Category.id_comp]

theorem PairUP_Comm2' {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm) (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty) (h : top ≫ base.tp = left ≫ baseSig) : PairUP' left ≫ (base.uvPolyTp.comp base.uvPolyTp).p = (yoneda.map (base.disp (left ≫ baseSig))) ≫ left := by
  sorry

theorem PairUP_Comm2 {Γ : Ctx} (top : (yoneda.obj Γ) ⟶ base.Tm)
    (left : (yoneda.obj Γ) ⟶ base.Ptp.obj base.{u}.Ty)
    (h : top ≫ base.tp = left ≫ baseSig) :
    (PairUP top left h) ≫ (base.uvPolyTp.comp base.uvPolyTp).p = left
    := by
  unfold PairUP
  rw[Category.assoc,PairUP_Comm2' top left h,<- Category.assoc,
    sec'_disp,Category.id_comp]

theorem PairUP_Uniqueness {Γ : Ctx}
    (f : (yoneda.obj Γ) ⟶ base.uvPolyTp.compDom base.uvPolyTp) :
    f = (PairUP (f ≫  basePair)
      (f ≫ (base.uvPolyTp.comp base.uvPolyTp).p)
      (by rw[Category.assoc,Category.assoc]; congr 1; exact Sigma_Comm))     := by
  unfold PairUP
  refine (base.uvPolyTpCompDomEquiv Γ).injective ?_
  refine Sigma.ext ?_ ?_
  . sorry
  . sorry

def is_pb : IsPullback basePair (base.uvPolyTp.comp base.uvPolyTp).p base.tp baseSig := by
  sorry

def baseSigma : NaturalModelSigma base where
  Sig := baseSig
  pair := basePair
  Sig_pullback := is_pb

def smallUSigma : NaturalModelSigma smallU := sorry

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma
  | 1 => smallUSigma
  | 2 => smallUSigma
  | 3 => baseSigma
  | (n+4) => by omega

end GroupoidModel
end
