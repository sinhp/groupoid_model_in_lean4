import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

open CategoryTheory

theorem Grpd.map_id_obj {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {x : Γ} {y : A.obj x} :
    (A.map (𝟙 x)).obj y = y := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_obj this y

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
    dsimp
    apply CategoryTheory.Functor.ext
    · sorry
    · intro pair
      simp only [Functor.comp_obj, map, Grothendieck.map_obj,
        Grothendieck.Groupoidal.pre, Grpd.id_eq_id,
        CategoryTheory.Functor.id_obj, Grothendieck.pre]
      rcases pair with ⟨ a , f ⟩
      congr 1
      · exact Grpd.map_id_obj
      · simp [Grpd.forgetToCat]
        let NT := @Grothendieck.ιNatTrans _ _
          (A ⋙ Grpd.forgetToCat) _ _ (CategoryStruct.id x)
        have : B.map (NT.app a) =
            eqToHom (by simp [Functor.map_id]) :=
        calc
          B.map (NT.app a) = B.map ⟨CategoryStruct.id x , eqToHom rfl⟩ := rfl
          _ = B.map (eqToHom (by simp [Functor.map_id])) := by
            simp [Grothendieck.eqToHom_eq_right]
          _ = eqToHom (by simp [Functor.map_id]) := by
            simp [eqToHom_map]
        rw [Functor.congr_obj this f]
        simp [Grpd.eqToHom_obj]
  map_comp := by
    -- intro X Y Z f g
    -- simp[Grpd.forgetToCat]
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
