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

theorem Grpd.map_comp_obj {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a : A.obj x} :
    (A.map (f ≫ g)).obj a = (A.map g).obj ((A.map f).obj a) := by
  have : A.map (f ≫ g) = A.map f ⋙ A.map g := by
    simp [Grpd.comp_eq_comp]
  have h := Functor.congr_obj this a
  simp only [Functor.comp_obj] at h
  exact h

theorem Grpd.map_comp_map {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{v₁,u₁}}
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map (f ≫ g)).map φ
    = eqToHom Grpd.map_comp_obj ≫ (A.map g).map ((A.map f).map φ)
    ≫ eqToHom Grpd.map_comp_obj.symm := by
  have : A.map (f ≫ g) = A.map f ≫ A.map g := by simp
  exact Functor.congr_hom this φ

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

namespace CategoryTheory.Grothendieck

theorem ιNatTrans_id_app {X : C} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (CategoryStruct.id X)).app a =
    eqToHom (by simp) := by
  apply ext
  · simp
  · simp [eqToHom_base]

theorem ιNatTrans_comp_app {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) := by
  apply Grothendieck.ext
  · simp
  · simp

end CategoryTheory.Grothendieck
-- theorem CategoryTheory.Grothendieck.fiber_id_comp {x y z : C} {a : F.obj x}
--     {b : F.obj z}
--     {f : x ⟶ y} {g : y ⟶ z} (h : (F.map g).obj ((F.map f).obj a) = b) :
--   (⟨f, CategoryStruct.id _⟩ : (⟨x,a⟩ : Grothendieck F) ⟶ ⟨y,(F.map f).obj a⟩)
--     ≫ (⟨ g , eqToHom h ⟩ : (⟨y,(F.map f).obj a⟩ : Grothendieck F) ⟶ ⟨z, b⟩) =
--   (⟨f ≫ g, CategoryStruct.id  ⟩ : (⟨x,a⟩ : Grothendieck F) ⟶ ⟨z,b⟩)
--     := by
--   apply Grothendieck.ext
--   · simp
--   · simp [Grothendieck.eqToHom_base]

-- theorem {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (d)

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
      · simp [Grpd.forgetToCat, Functor.congr_obj (h p.base) p.fiber,
        eqToHom_refl, eqToHom_map, Grpd.eqToHom_obj, Grpd.id_eq_id, Functor.id_obj]

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
