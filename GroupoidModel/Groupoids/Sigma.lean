import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

open CategoryTheory

theorem Grpd.map_id_obj {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {x : Γ} {a : A.obj x} :
    (A.map (𝟙 x)).obj a = a := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_obj this a

theorem Grpd.map_id_map {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {x : Γ} {a b : A.obj x} {f : a ⟶ b} :
    (A.map (𝟙 x)).map f = eqToHom Grpd.map_id_obj
      ≫ f ≫ eqToHom Grpd.map_id_obj.symm := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_hom this f

/-- This is the proof of equality used in the eqToHom in `Cat.eqToHom_hom` -/
theorem Grpd.eqToHom_hom_aux {C1 C2 : Grpd.{v,u}} (x y: C1) (eq : C1 = C2) :
    (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem Grpd.eqToHom_hom {C1 C2 : Grpd.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (Grpd.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ Cat.{v₂, u₂}}

theorem CategoryTheory.Grothendieck.eqToHom_eq_right {x : C} {y z : F.obj x} (h : y = z) :
  eqToHom (by simp[h] : ( ⟨x,y⟩ : Grothendieck F) = ⟨x,z⟩) =
  ({ base := 𝟙 x, fiber := eqToHom (by simp[h]) } : (⟨x,y⟩ : Grothendieck F) ⟶ ⟨x,z⟩)
    := by
  apply Grothendieck.ext
  · simp
  · simp [Grothendieck.eqToHom_base]

theorem CategoryTheory.Grpd.eqToHom_obj
  {C1 C2 : Grpd.{v,u}} (x : C1) (eq : C1 = C2) :
    (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

set_option maxHeartbeats 0
/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.

  For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd` -/
def sigma {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{v₁,u₁})
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
          = B.map ⟨CategoryStruct.id x , eqToHom rfl⟩ := rfl
        _ = B.map (eqToHom (by simp [Functor.map_id])) := by
          simp [Grothendieck.eqToHom_eq_right]
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
    · intro pair
      simp only [Functor.comp_obj, Grothendieck.map_obj]
      rcases pair with ⟨ a , f ⟩
      congr 1
      · exact Grpd.map_id_obj
      · simp only [Grpd.forgetToCat, id_eq, whiskerRight_app,
          Functor.comp_map]
        rw [Functor.congr_obj (h a) f]
        simp [Grpd.eqToHom_obj]
  map_comp := by
    sorry

/-- The formation rule for Σ-types for the ambient natural model `base` -/
def baseSigmaSig : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun pair =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv pair
    yonedaEquiv (yonedaCatEquiv.symm (sigma A B))
  naturality := sorry

def baseSigma : NaturalModelSigma base where
  Sig := baseSigmaSig
  pair := sorry
  Sig_pullback := sorry

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
