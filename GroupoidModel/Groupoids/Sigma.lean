import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

set_option maxHeartbeats 0

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther



end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

namespace FunctorOperation

-- TODO: Fix performance issue.
set_option maxHeartbeats 0 in
/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.

  For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd` -/
@[simps] def sigma {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁})
    : Γ ⥤ Grpd.{v₁,u₁} where
  obj x := Grpd.of (Grothendieck.Groupoidal ((ι _ x) ⋙ B))
  map {x y} f := map (whiskerRight (Grothendieck.ιNatTrans f) B)
    ⋙ pre (ι A y ⋙ B) (A.map f)
  map_id x := by
    let t := @Grothendieck.ιNatTrans _ _
        (A ⋙ Grpd.forgetToCat) _ _ (CategoryStruct.id x)
    have h (a : A.obj x) : B.map (t.app a) =
        eqToHom (by simp [Functor.map_id]) :=
      calc
        B.map (t.app a)
        _ = B.map (eqToHom (by simp [Functor.map_id])) := by
          rw [Grothendieck.ιNatTrans_id_app]
        _ = eqToHom (by simp [Functor.map_id]) := by
          simp [eqToHom_map]
    simp only [map, Grothendieck.Groupoidal.pre, Grpd.id_eq_id, Grothendieck.pre]
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp only [Grpd.coe_of, Functor.comp_obj, Functor.comp_map, whiskerRight_twice,
        Grothendieck.map_obj_base, Grothendieck.map_obj_fiber, whiskerRight_app,
        Grothendieck.ι_obj, Grothendieck.map_map_base,
        Grothendieck.map_map_fiber, Functor.id_obj, Functor.id_map]
      congr 1
      · simp only [Grpd.map_id_map, Grothendieck.base_eqToHom,
          Grothendieck.comp_base]
      · simp only [Grpd.forgetToCat, id_eq, Functor.comp_map, whiskerRight_twice,
          Grothendieck.map_obj_base, Grothendieck.map_obj_fiber, whiskerRight_app,
          Grothendieck.ι_obj, Grothendieck.fiber_eqToHom, Grothendieck.comp_fiber]
        rw [Functor.congr_hom (h p2.base) f.fiber]
        simp only [Grpd.eqToHom_hom, eqToHom_map, heq_eqToHom_comp_iff,
          eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        generalize_proofs _ _ h1
        have h2 : B.map ((ι A x).map (eqToHom h1).base) =
            eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl) := by
          rw [Grothendieck.eqToHom_base, eqToHom_map, eqToHom_map]
        rw [Functor.congr_hom h2, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
        simp only [heq_eq_eq, Grpd.eqToHom_hom]
    · intro p
      simp only [Functor.comp_obj, Grothendieck.map_obj]
      congr 1
      · exact Grpd.map_id_obj
      · simp only [Grpd.forgetToCat, id_eq, whiskerRight_app,
          Functor.comp_map]
        rw [Functor.congr_obj (h p.base) p.fiber]
        simp [Grpd.eqToHom_obj]
  map_comp := by
    intro x y z f g
    have h (a : A.obj x) : B.map ((Grothendieck.ιNatTrans (f ≫ g)).app a)
        = B.map ((Grothendieck.ιNatTrans f).app a)
        ⋙ B.map (eqToHom (by
          simp [Grpd.forgetToCat]))
        ⋙ B.map ((Grothendieck.ιNatTrans g).app ((A.map f).obj a))
        ⋙ B.map (eqToHom (by
          simp [Grpd.forgetToCat, Grpd.comp_eq_comp])) := by
      simp only [Grothendieck.ιNatTrans_comp_app, Functor.map_comp,
        eqToHom_map, CategoryTheory.Functor.map_id]
      rfl
    simp only [Grothendieck.Groupoidal.pre, Grothendieck.pre]
    apply CategoryTheory.Functor.ext
    · sorry
    · intro p
      simp only [Grpd.coe_of, Functor.comp_obj, Functor.comp_map]
      congr 1
      · rw [Grpd.map_comp_obj]
        rfl
      · simp [map, Grpd.forgetToCat, Functor.congr_obj (h p.base) p.fiber,
        eqToHom_refl, eqToHom_map, Grpd.eqToHom_obj, Grpd.id_eq_id, Functor.id_obj]

section

variable {Δ Γ: Grpd.{v₂,u₂}} (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{v₁,u₁})


theorem sigmaBeckChevalley (B : (Grothendieck.Groupoidal A) ⥤ Grpd.{v₁,u₁})
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

def pairSection {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = sec α ⋙ B)
    : Γ ⥤ (Grothendieck.Groupoidal (sigma (α ⋙ PGrpd.forgetToGrpd) B)) where
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

theorem pairSection_isSection {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B) :
     (pairSection α β B h) ⋙ Grothendieck.forget _ = Functor.id Γ := rfl

def pair {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B)
    : Γ ⥤ PGrpd.{v₁,u₁} := pairSection α β B h ⋙ Grothendieck.Groupoidal.toPGrpd _

def sigma_is_forgetToGrpd_after_pair {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B) :
    pair α β B h ⋙ PGrpd.forgetToGrpd = sigma (α ⋙ PGrpd.forgetToGrpd) B := by
  unfold pair
  rw [Functor.assoc]
  exact rfl



def GrotSigmaToA {Γ : Grpd} (A : Γ ⥤ Cat.of Grpd.{v₁,u₁}) (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁}) : Grothendieck.Groupoidal (sigma A B) ⥤  Grothendieck.Groupoidal A where
  obj x := ⟨x.base,x.fiber.base⟩
  map {x y} f := {base := f.base, fiber := f.fiber.base}
  map_id x := by
    simp[CategoryStruct.id,Grothendieck.id]
    fapply Grothendieck.ext
    . simp
    . simp
      rw [Grothendieck.eqToHom_eq]
  map_comp := sorry

def SectionGrotSigmaToA {Γ : Grpd}(A : Γ ⥤ Cat.of Grpd.{v₁,u₁})(B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁})(sec : Γ ⥤ Grothendieck.Groupoidal (sigma A B)) : Γ ⥤ Grothendieck.Groupoidal A := (sec ⋙ (GrotSigmaToA A B))

def SectionGrotSigmaToB {Γ : Grpd}(A : Γ ⥤ Cat.of Grpd.{v₁,u₁})(B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁})(sec : Γ ⥤ Grothendieck.Groupoidal (sigma A B)) : Γ ⥤ (Grothendieck.Groupoidal ((SectionGrotSigmaToA A B sec)⋙ B)) where
  obj x := by
    let ab := sec.obj x
    let x'' := ab.fiber.fiber
    simp [ι] at x''
    refine ⟨x,?_⟩
    dsimp[SectionGrotSigmaToA]
    have alpha := B.obj ((SectionGrotSigmaToA A B sec).obj x)
    simp[GrotSigmaToA]
    exact ab.fiber.fiber
  map {x y} f := by sorry


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

def ExtFunctorial {Γ : Ctx} {F G : (yoneda.obj Γ) ⟶  base.Ty} (n : (yonedaCatEquiv.toFun F) ⟶ (yonedaCatEquiv.toFun G)) : base.ext F ⟶ base.ext G := by
  dsimp [NaturalModelBase.ext, ext,Grpd.of,Grothendieck.Groupoidal]
  refine AsSmall.up.map ?_
  exact map n

def Sigma_UP_Elim (Γ : Ctx) (F : yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty) : (α : yoneda.obj Γ ⟶ base.Ty) × (yoneda.obj (base.ext α) ⟶ base.Ty) := by
  unfold Ptp at F
  have r := base.uvPolyTp.polyPair F
  rcases r with ⟨α, B⟩
  refine ⟨α,?_⟩
  let B' : y(base.ext α) ⟶ base.Ty := by
    refine ?_ ≫ B
    have iso :y(base.ext α) ≅ (Limits.pullback α base.uvPolyTp.p) := by
      exact (base.pullbackIsoExt α).symm
    exact (id iso.symm).inv
  exact B'

def Sigma_UP_Intro (Γ : Ctx) (α : yoneda.obj Γ ⟶ base.Ty) (B : yoneda.obj (base.ext α) ⟶ base.Ty) :  yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty := base.uvPolyTp.pairPoly α ( (Iso.hom (base.pullbackIsoExt α)) ≫ B)




-- def pair_UP_Elim (Γ : Ctx.{u}) (F : yoneda.obj Γ ⟶ base.{u}.uvPolyTp.compDom base.{u}.uvPolyTp) : (α : yoneda.obj Γ ⟶ base.{u}.Tm) × (β : yoneda.obj Γ ⟶ base.{u}.Tm) × (B : yoneda.obj (base.{u}.ext (α ≫ base.{u}.tp)) ⟶ base.{u}.Ty) ×' (β ≫ base.{u}.tp = (yoneda.map (base.{u}.sec α)) ≫ B ) := by
--   unfold UvPoly.compDom at F
--   let F.fst := F ≫ Limits.pullback.fst _ _
--   let F.snd := F ≫ Limits.pullback.snd _ _
--   have F.h := Limits.pullback.condition (f := base.uvPolyTp.p) (g := (UvPoly.genPb.u₂ base.uvPolyTp base.Ty))
--   have sigma : (α : yoneda.obj Γ ⟶ base.Ty) × (yoneda.obj (base.ext α) ⟶ base.Ty) := by
--     refine Sigma_UP_Elim Γ ?_
--     refine F.snd ≫ ?_
--     exact
--       UvPoly.genPb.fst base.uvPolyTp
--         ((AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op ⋙ yoneda.obj (Cat.of Grpd))
--   refine ⟨?_ , F.fst , ?_, ?_⟩

--   refine ⟨?_ , F.fst , ?_ , ?_ ⟩
--   . refine F.snd ≫ ?_
--     unfold UvPoly.genPb
--     refine Limits.pullback.snd _ _
--   . refine (base.var _) ≫ base.tp
--   . unfold F.fst
--     have help : base.tp = base.uvPolyTp.p := by rfl
--     have help2 : Limits.pullback.fst base.uvPolyTp.p (UvPoly.genPb.u₂ base.uvPolyTp base.Ty) = Limits.pullback.fst base.tp (UvPoly.genPb.u₂ base.uvPolyTp base.Ty) := by
--       simp [help]
--       exact rfl
--     rewrite [<- help] at F.h
--     rw [Category.assoc,help2, F.h]
--     simp [base.var]
--     have help3 : base.var ((F.snd ≫ id (Limits.pullback.snd (base.uvPolyTp.proj base.Ty) base.uvPolyTp.p)) ≫ base.tp) ≫ base.tp =

-- def pair_UP_Intro (Γ : Ctx) (α β : yoneda.obj Γ ⟶ base.Tm) (B : yoneda.obj (base.ext (α ≫ base.tp)) ⟶ base.Ty) (h : β ≫ base.tp = (yoneda.map (base.sec α)) ≫ B ) :  yoneda.obj Γ ⟶ base.uvPolyTp.compDom base.uvPolyTp := by

def baseSigma : NaturalModelSigma base where
  Sig := baseSig
  pair := basePair
  Sig_pullback := sorry -- should prove using the `IsMegaPullback` strategy

def smallUSigma : NaturalModelSigma smallU := sorry

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma
  | 1 => smallUSigma
  | 2 => smallUSigma
  | 3 => baseSigma
  | (n+4) => by omega

def uHomSeqSigmas : UHomSeqSigmas Ctx := {
  uHomSeq with
  Sigmas' := uHomSeqSigmas' }

end GroupoidModel

end
