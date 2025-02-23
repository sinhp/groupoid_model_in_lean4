import GroupoidModel.Groupoids.RussellNaturalModel

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck Limits NaturalModelBase

variable {c : Cat.{max u (v+2), max u (v+2)}}
  {fst : c ⥤ PGrpd.{v+1,v+1}}
  {snd : c ⥤ Grpd.{v,v}}
  (condition : fst ⋙ PGrpd.forgetToGrpd.{v+1,v+1}
    = snd ⋙ Grpd.asSmallFunctor.{v+1, v, v})

abbrev pt' (x : c) := (fst.obj x).str.pt

/- This is an explicit natural transformation for the commuting condition -/
abbrev ε : fst ⋙ PGrpd.forgetToGrpd.{v+1,v+1} ⟶
    snd ⋙ Grpd.asSmallFunctor.{v+1, v, v} :=
  eqToHom condition

abbrev εApp
    (x : c)
    : (fst ⋙ PGrpd.forgetToGrpd.{v+1,v+1}).obj x
    ⟶ (snd ⋙ Grpd.asSmallFunctor.{v+1}).obj x := (ε condition).app x

abbrev εNaturality {x y : c} (f : x ⟶ y) :
     (fst ⋙ PGrpd.forgetToGrpd).map f ⋙ (ε condition).app y = (ε condition).app x ⋙ (snd ⋙ Grpd.asSmallFunctor).map f
  := (ε condition).naturality f

abbrev point' {x y : c} (f : x ⟶ y) :
    (PGrpd.forgetToGrpd.map (fst.map f)).obj (pt' x) ⟶ pt' y :=
  (fst.map f).point

@[simp] def lift_obj (x : c) : PGrpd.{v,v} :=
  PGrpd.ofGrpd
    (snd.obj x)
    (AsSmall.down.obj.{v,v,v+1} $ (εApp condition x).obj (pt' x))

@[simp] def lift_map {x y : c} (f : x ⟶ y) :
    lift_obj condition x ⟶ lift_obj condition y :=
  PGrpd.homOf {
    toFunctor := snd.map f
    point :=
      let m1 := (εApp condition y).map (point' f)
      let m2 := (eqToHom (εNaturality condition f).symm).app (pt' x)
      AsSmall.down.map.{v,v,v+1} (m2 ≫ m1)
}

theorem AsSmall.down_comp {C : Type u} [Category.{v} C]
    {x y z : AsSmall.{w} C} (h : x ⟶ y) (k : y ⟶ z) :
    AsSmall.down.map (h ≫ k) = (AsSmall.down.map h) ≫ AsSmall.down.map k :=
  rfl

theorem PGrpd.map_id_point {C : Type u} [Category.{v} C] {F : C ⥤ PGrpd} {x : C} :
    (F.map (CategoryStruct.id x)).point =
    eqToHom (by simp : (F.map (CategoryStruct.id x)).obj (F.obj x).str.pt = (F.obj x).str.pt) := by
  have : (CategoryStruct.id (F.obj x)).point = _ := PGrpd.id_point
  convert this
  · simp
  · simp
  · refine HEq.symm (heq_of_eqRec_eq ?_ rfl)
    · symm; assumption

open Functor

namespace PGrpd
/-- This is the proof of equality used in the eqToHom in `PointedFunctor.eqToHom_point` -/
theorem eqToHom_point_aux {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).obj PointedCategory.pt = PointedCategory.pt := by
  cases eq
  simp [CategoryStruct.id]

/-- This shows that the point of an eqToHom in PCat is an eqToHom-/
theorem eqToHom_point {P1 P2 : PGrpd.{v,u}} (eq : P1 = P2) :
    (eqToHom eq).point = (eqToHom (eqToHom_point_aux eq)) := by
  cases eq
  simp[PointedFunctor.id, CategoryStruct.id, PCat.forgetToCat,Cat.of,Bundled.of]

end PGrpd

def CategoryTheory.AsSmall.up_map_comp_down_map
    {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) :
  AsSmall.down.map (AsSmall.up.map f) = f := rfl

set_option maxHeartbeats 0
def lift :
    c ⥤ PGrpd.{v,v} := {
    obj := lift_obj condition
    map := lift_map condition
    map_id x := by sorry
      -- apply PointedFunctor.ext
      -- · simp only [εApp, ε, lift_map, PGrpd.homOf, PGrpd.map_id_point]
      --   generalize_proofs _ pf2
      --   simp [Functor.congr_hom (eqToHom_app condition x) (eqToHom pf2),
      --     eqToHom_map]
      -- · simp only [lift_map, PGrpd.homOf, CategoryTheory.Functor.map_id]
      --   rfl
    map_comp {x y z} f g := by
      apply PointedFunctor.ext
      · 
        have h' := PointedFunctor.congr_point (fst.map_comp f g)
        have h'' := Functor.congr_hom (εNaturality condition g) (fst.map f).point
        simp only [comp_obj, PGrpd.forgetToGrpd_obj, Grpd.coe_of, Functor.comp_map, PGrpd.forgetToGrpd_map, ε] at h''
        rw [Functor.congr_hom (eqToHom_app condition z) ((fst.map g).map (fst.map f).point),
          eqToHom_comp_iff, comp_eqToHom_iff] at h''
        simp only [lift_obj, comp_obj, PGrpd.forgetToGrpd_obj,
          Grpd.coe_of, εApp, ε, lift_map, PGrpd.homOf,
          PGrpd.forgetToGrpd_map, eqToHom_app,
          PGrpd.comp_toFunctor, PGrpd.comp_point, point']
        -- generalize_proofs pf1 pf2 pf3 pf4 pf5
        rw [Functor.congr_hom (eqToHom_app condition y) (point' f),
          Functor.congr_hom
            (eqToHom_app condition z) (point' g),
          Functor.congr_hom
            (eqToHom_app condition z) (point' (f ≫ g))]
        simp only [Functor.comp_map, comp_obj, PGrpd.forgetToGrpd_obj,
  Grpd.coe_of, point', h', PGrpd.comp_toFunctor, PGrpd.comp_point, map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_map]
        rw [h'']
        simp only [Grpd.asSmallFunctor, Grpd.coe_of, comp_obj, PGrpd.forgetToGrpd_obj,
  Functor.comp_map, ← Category.assoc, eqToHom_trans, PGrpd.forgetToGrpd_map, Functor.map_comp, eqToHom_map]
        congr 2
        simp only [Category.assoc, eqToHom_trans,
          AsSmall.up_map_comp_down_map]
        rw [Functor.congr_hom (eqToHom_app condition y) (fst.map f).point]
        generalize_proofs pf1 pf2 pf3 pf4 pf5 pf6 pf7
        have h3 : (snd.map g).map (AsSmall.down.map (eqToHom pf4 ≫ (eqToHom pf3).map (fst.map f).point ≫ eqToHom pf5)) =
        (snd.map g).map (AsSmall.down.map (eqToHom pf4)) ≫ (snd.map g).map (AsSmall.down.map ((eqToHom pf3).map (fst.map f).point)) ≫ (snd.map g).map (AsSmall.down.map (eqToHom pf5)) := by simp only [Functor.map_comp]
        rw [h3]
        simp [eqToHom_map]
      · simp only [lift_map, PGrpd.homOf, CategoryTheory.Functor.map_comp]
        rfl
}
