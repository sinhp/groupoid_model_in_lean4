import GroupoidModel.Groupoids.RussellNaturalModel

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck Limits NaturalModelBase Functor

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


set_option maxHeartbeats 0
def lift :
    c ⥤ PGrpd.{v,v} := {
    obj := lift_obj condition
    map := lift_map condition
    map_id x := by
      apply PointedFunctor.ext
      · simp only [εApp, ε, lift_map, PGrpd.homOf, PGrpd.map_id_point]
        generalize_proofs _ pf2
        simp [Functor.congr_hom (eqToHom_app condition x) (eqToHom pf2),
          eqToHom_map]
      · simp only [lift_map, PGrpd.homOf, CategoryTheory.Functor.map_id]
        rfl
    map_comp {x y z} f g := by
      apply PointedFunctor.ext
      · have h := Functor.congr_hom (εNaturality condition g) (fst.map f).point
        simp only [comp_obj, Functor.comp_map, PGrpd.forgetToGrpd_map,
          Functor.congr_hom (eqToHom_app condition z)
            ((fst.map g).map (fst.map f).point),
          eqToHom_comp_iff, comp_eqToHom_iff] at h
        simp only [lift_obj, comp_obj,
          lift_map, PGrpd.homOf,
          eqToHom_app,
          PGrpd.comp_toFunctor, PGrpd.comp_point, point',
          Functor.congr_hom (eqToHom_app condition y) (point' f),
          Functor.congr_hom
            (eqToHom_app condition z) (point' g),
          Functor.congr_hom
            (eqToHom_app condition z) (point' (f ≫ g))]
        simp only [PointedFunctor.congr_point (fst.map_comp f g),
          PGrpd.comp_toFunctor, PGrpd.comp_point, map_comp,
          Category.assoc]
        simp only [h, Grpd.asSmallFunctor, Functor.comp_map,
          Functor.congr_hom (eqToHom_app condition y) (fst.map f).point,
          ← Category.assoc, Functor.map_comp, eqToHom_map]
        simp only [eqToHom_trans, AsSmall.up_map_comp_down_map]
      · simp only [lift_map, PGrpd.homOf, Functor.map_comp]
        rfl}
