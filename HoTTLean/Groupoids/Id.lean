import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.Model.Unstructured.Hurewicz
import HoTTLean.Groupoids.ClovenIsofibration

import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

universe w v u v₁ u₁ v₂ u₂

noncomputable section

open CategoryTheory

namespace FunctorOperation

variable {Γ : Type u} [Groupoid.{v} Γ] {Δ : Type u₂} [Groupoid.{v₂} Δ] (σ : Δ ⥤ Γ)
  {A : Γ ⥤ Grpd.{v₁,u₁}} {a0 a1 : Γ ⥤ PGrpd.{v₁,u₁}}
  (a0_tp : a0 ⋙ PGrpd.forgetToGrpd = A) (a1_tp : a1 ⋙ PGrpd.forgetToGrpd = A)

/-- The identity type former takes a (family of) groupoid(s) `A` with two points `a0 a1`
to the (family of) set(s) of isomorphisms
between its two given points `A(a0,a1)`. -/
def IdObj (x : Γ) : Grpd :=
  Grpd.of <| Discrete <| PGrpd.objFiber' a0_tp x ⟶ PGrpd.objFiber' a1_tp x

def IdMap {x y : Γ} (f : x ⟶ y) : IdObj a0_tp a1_tp x ⥤ IdObj a0_tp a1_tp y :=
  Discrete.functor <| fun g =>
  ⟨inv (PGrpd.mapFiber' a0_tp f) ≫ (A.map f).map g ≫ PGrpd.mapFiber' a1_tp f⟩

lemma IdMap_id (X : Γ) : IdMap a0_tp a1_tp (𝟙 X) = 𝟙 (IdObj a0_tp a1_tp X) := by
  apply Discrete.functor_ext
  intro g
  apply Discrete.ext
  simp [IdMap]

lemma IdMap_comp {X Y Z : Γ} (f1 : X ⟶ Y) (f2 : Y ⟶ Z) : IdMap a0_tp a1_tp (f1 ≫ f2) =
    IdMap a0_tp a1_tp f1 ⋙ IdMap a0_tp a1_tp f2 := by
  subst a0_tp
  apply Discrete.functor_ext
  intro g
  apply Discrete.ext
  simp only [Functor.comp_obj, Functor.Grothendieck.forget_obj, PGrpd.objFiber'_rfl, IdMap,
    Functor.comp_map, Functor.Grothendieck.forget_map, PGrpd.mapFiber'_rfl,
    Discrete.functor_obj_eq_as, Functor.map_comp, Functor.map_inv,
    Category.assoc, IsIso.eq_inv_comp]
  simp only [PGrpd.mapFiber, PGrpd.map_comp_fiber, Functor.Grothendieck.forget_obj,
    Functor.Grothendieck.forget_map, ← Category.assoc, IsIso.inv_comp, inv_eqToHom,
    PGrpd.mapFiber', Functor.comp_obj, Functor.comp_map, PGrpd.objFiber'EqToHom,
    PGrpd.mapFiber'EqToHom, Functor.map_comp, eqToHom_map, eqToHom_trans, IsIso.hom_inv_id,
    Category.id_comp, Functor.Grothendieck.Hom.comp_base, Grpd.comp_eq_comp, eqToHom_naturality,
    Category.comp_id, ← heq_eq_eq]
  congr 1
  rw! [Functor.map_comp]
  simp only [Functor.Grothendieck.Hom.comp_base, Grpd.comp_eq_comp, Functor.comp_obj,
    eqToHom_refl, Functor.comp_map, Category.id_comp, Category.assoc, ← heq_eq_eq]
  congr 1
  have h := Functor.congr_hom a1_tp f2
  simp only [Functor.comp_obj, Functor.Grothendieck.forget_obj, Functor.comp_map,
    Functor.Grothendieck.forget_map, Grpd.comp_eq_comp] at h
  rw! [h]
  simp only [← Grpd.comp_eq_comp, Grpd.comp_obj, ← Functor.comp_map, ← heq_eq_eq,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff, eqToHom_comp_heq_iff]
  simp [Grpd.eqToHom_hom]

@[simps!]
def Id : Γ ⥤ Grpd where
  obj := IdObj a0_tp a1_tp
  map := IdMap a0_tp a1_tp
  map_id := IdMap_id a0_tp a1_tp
  map_comp := IdMap_comp a0_tp a1_tp

lemma Id_comp : Id (A := σ ⋙ A) (a0 := σ ⋙ a0) (a1 := σ ⋙ a1)
    (by simp[Functor.assoc, a0_tp]) (by simp[Functor.assoc, a1_tp]) =
    σ ⋙ Id a0_tp a1_tp :=
  rfl

namespace Path

open CategoryTheory.Prod

section

variable (p : Grpd.Interval × Γ ⥤ PGrpd)

abbrev ff (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.false⟩⟩, x⟩
abbrev ffm {x y : Γ} (f : x ⟶ y) : ff x ⟶ ff y := ⟨𝟙 _, f⟩
abbrev tt (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.true⟩⟩, x⟩
abbrev ttm {x y : Γ} (f : x ⟶ y) : tt x ⟶ tt y := ⟨𝟙 _, f⟩
abbrev ft (x : Γ) : ff x ⟶ tt x := ⟨⟨⟨⟩⟩, 𝟙 x⟩
abbrev tf (x : Γ) : tt x ⟶ ff x := ⟨⟨⟨⟩⟩, 𝟙 x⟩

abbrev path0 : Γ ⥤ PGrpd := sectR ⟨⟨.false⟩⟩ _ ⋙ p

abbrev path1 : Γ ⥤ PGrpd := sectR ⟨⟨.true⟩⟩ _ ⋙ p

variable {p} (p_tp : p ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A)

include p_tp in
@[simp]
lemma path0_comp_forgetToGrpd : path0 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

include p_tp in
@[simp]
lemma path1_comp_forgetToGrpd : path1 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

lemma objFiber'_path0 (x) : PGrpd.objFiber' (path0_comp_forgetToGrpd p_tp) x =
    PGrpd.objFiber' p_tp (ff x) := by
  dsimp [PGrpd.objFiber', PGrpd.objFiber]

@[simp]
abbrev pathId : Γ ⥤ Grpd :=
  Id (A := A) (a0 := path0 p) (a1 := path1 p)
  (path0_comp_forgetToGrpd p_tp) (path1_comp_forgetToGrpd p_tp)

@[simps!]
def pathFibObj (x : Γ) : @IdObj _ _ A (path0 p) (path1 p) (path0_comp_forgetToGrpd p_tp)
    (path1_comp_forgetToGrpd p_tp) x :=
  ⟨eqToHom (by simp [objFiber'_path0 p_tp]) ≫ PGrpd.mapFiber' p_tp (ft x)⟩

lemma pathFibObj_comp (x : Δ) : pathFibObj (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
    (by simp [Functor.assoc, p_tp]; rfl) x = pathFibObj p_tp (σ.obj x) := by
  apply Discrete.ext
  simp only [Functor.comp_obj, pathFibObj_as, Functor.comp_map, PGrpd.mapFiber', snd_obj, snd_map,
    Functor.prod_obj, Functor.id_obj, Functor.Grothendieck.forget_obj, PGrpd.objFiber'EqToHom,
    Functor.prod_map, Functor.id_map, PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc]
  rw! [CategoryTheory.Functor.map_id]

lemma IdMap_path {x y} (f : x ⟶ y) :
    ((IdMap (path0_comp_forgetToGrpd p_tp) (path1_comp_forgetToGrpd p_tp) f).obj
      (pathFibObj p_tp x)).as = (pathFibObj p_tp y).as := by
  dsimp [IdMap]
  have comm : ft x ≫ ttm f = ffm f ≫ ft y := by ext; rfl; simp
  have h1 := (PGrpd.mapFiber'_comp' p_tp (ft x) (ttm f)).symm
  rw! [comm, PGrpd.mapFiber'_comp' p_tp (ffm f) (ft y)] at h1
  simp only [Functor.comp_obj, snd_obj, prod_comp, Functor.comp_map, snd_map, Grpd.map_id_map,
    Category.assoc, eqToHom_trans_assoc, ← heq_eq_eq, heq_eqToHom_comp_iff,
    eqToHom_comp_heq_iff] at h1
  simp only [PGrpd.mapFiber'_naturality p_tp (sectR ⟨⟨.false⟩⟩ _), sectR_obj, sectR_map,
    Functor.map_comp, eqToHom_map, PGrpd.mapFiber'_naturality p_tp (sectR ⟨⟨.true⟩⟩ _),
    Category.assoc, IsIso.inv_comp_eq]
  rw! [h1]
  simp

def pathFibMap {x y : Γ} (f : x ⟶ y) :
    (IdMap (path0_comp_forgetToGrpd p_tp) (path1_comp_forgetToGrpd p_tp) f).obj
    (pathFibObj p_tp x) ⟶ pathFibObj p_tp y :=
  ⟨⟨IdMap_path ..⟩⟩

lemma pathFibMap_id (x : Γ) : pathFibMap p_tp (𝟙 x) = eqToHom (by simp [IdMap_id]) := by
  aesop_cat

lemma pathFibMap_comp {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z) :
    pathFibMap p_tp (f1 ≫ f2) =
    eqToHom (by simp only [IdMap_comp]; rfl) ≫
    ((pathId p_tp).map f2).map (pathFibMap p_tp f1) ≫ pathFibMap p_tp f2 := by
  aesop_cat

def path : Γ ⥤ PGrpd :=
  PGrpd.functorTo (pathId p_tp) (pathFibObj p_tp) (pathFibMap p_tp)
    (pathFibMap_id p_tp) (fun f1 f2 => by dsimp only; aesop_cat)

lemma path_comp : path (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
    (by simp [Functor.assoc, p_tp]; rfl) = σ ⋙ path p_tp := by
  -- rw [PGrpd.functorTo]
  apply PGrpd.Functor.hext
  · rfl
  · intro x
    simp only [path, Functor.comp_obj, heq_eq_eq]
    -- rw [PGrpd.functorTo_obj_fiber] --FIXME why timeout?
    convert_to pathFibObj (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
      (by simp [Functor.assoc, p_tp]; rfl) x =
      pathFibObj (A := A) (p := p) p_tp (σ.obj x)
    rw [pathFibObj_comp]
  · intro x y f
    simp only [path, Functor.comp_map]
    -- rw [PGrpd.functorTo_map_fiber]
    convert_to pathFibMap (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
      (by simp [Functor.assoc, p_tp]; rfl) f ≍
      pathFibMap (A := A) (p := p) p_tp (σ.map f)
    rw! (castMode := .all) [pathFibObj_comp _ p_tp]
    rw! (castMode := .all) [pathFibObj_comp _ p_tp]
    rfl

@[simp]
lemma path_comp_forgetToGrpd : path p_tp ⋙ PGrpd.forgetToGrpd =
    Id (a0 := path0 p) (a1 := path1 p) (path0_comp_forgetToGrpd p_tp)
    (path1_comp_forgetToGrpd p_tp) :=
  rfl

end

section

variable {p : Γ ⥤ PGrpd}
  (p_tp : p ⋙ PGrpd.forgetToGrpd = FunctorOperation.Id a0_tp a1_tp)

def unpathFibObj : (x : Grpd.Interval × Γ) → A.obj x.2
| ⟨⟨⟨.false⟩⟩, x2⟩ => PGrpd.objFiber' a0_tp x2
| ⟨⟨⟨.true⟩⟩, x2⟩ => PGrpd.objFiber' a1_tp x2

def unpathFibMap : {x y : Grpd.Interval × Γ} → (f : x ⟶ y) →
    ((A.map f.2).obj (unpathFibObj a0_tp a1_tp x) ⟶ unpathFibObj a0_tp a1_tp y)
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, _⟩, f => PGrpd.mapFiber' a0_tp f.2
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => (PGrpd.mapFiber' a0_tp f.2) ≫ (PGrpd.objFiber' p_tp y2).1
| ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, y2⟩, f =>
  (PGrpd.mapFiber' a1_tp f.2) ≫ inv (PGrpd.objFiber' p_tp y2).1
| ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, _⟩, f => PGrpd.mapFiber' a1_tp f.2

lemma unpathFibMap_id (x : Grpd.Interval × Γ) : unpathFibMap a0_tp a1_tp p_tp (𝟙 x) =
    eqToHom (by simp) := by
  rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩ <;> simp [unpathFibMap]

open PGrpd in
lemma map_objFiber'_mapFiber' {x y} (f : x ⟶ y) :
    (A.map f).map (objFiber' p_tp x).as ≫ mapFiber' a1_tp f =
    mapFiber' a0_tp f ≫ (objFiber' p_tp y).as := by
  simpa using (mapFiber' p_tp f).1.1

open PGrpd in
lemma map_objFiber'_mapFiber'_inv_objFiber' {x y} (f : x ⟶ y) :
    (A.map f).map (objFiber' p_tp x).as ≫ mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as =
    mapFiber' a0_tp f := by
  slice_lhs 1 2 => rw [map_objFiber'_mapFiber']
  simp

open PGrpd in
lemma mapFiber'_inv_objFiber' {x y} (f : x ⟶ y) : mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as =
    inv ((A.map f).map (objFiber' p_tp x).as) ≫ mapFiber' a0_tp f := by
  rw [IsIso.eq_inv_comp]
  slice_lhs 1 2 => rw [map_objFiber'_mapFiber']
  simp

attribute [simp] unpathFibMap unpathFibObj PGrpd.mapFiber'_comp' Grpd.forgetToCat in
lemma unpathFibMap_comp {x y z : Grpd.Interval × Γ} (f : x ⟶ y) (g : y ⟶ z) :
    unpathFibMap a0_tp a1_tp p_tp (f ≫ g) =
    eqToHom (by simp) ≫ (A.map g.2).map (unpathFibMap a0_tp a1_tp p_tp f) ≫
    unpathFibMap a0_tp a1_tp p_tp g := by
  rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp [map_objFiber'_mapFiber'_inv_objFiber',
        map_objFiber'_mapFiber']
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
      · simp; simp [mapFiber'_inv_objFiber']
      · simp only [prod_comp, unpathFibObj, unpathFibMap, PGrpd.mapFiber'_comp', Functor.map_comp,
          Functor.map_inv, Category.assoc]
        slice_rhs 3 4 => rw [← mapFiber'_inv_objFiber']
        simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp

def unpath : Grpd.Interval × Γ ⥤ PGrpd :=
  Functor.Grothendieck.functorTo (snd _ _ ⋙ A) (unpathFibObj a0_tp a1_tp)
    (unpathFibMap a0_tp a1_tp p_tp) (unpathFibMap_id a0_tp a1_tp p_tp)
    (unpathFibMap_comp a0_tp a1_tp p_tp)

@[simp]
lemma unpath_comp_forgetToGrpd : unpath a0_tp a1_tp p_tp ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A := by
  rfl

@[simp]
lemma sectR_false_comp_unpath : sectR ⟨⟨.false⟩⟩ _ ⋙ unpath a0_tp a1_tp p_tp = a0 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, unpath, Functor.Grothendieck.functorTo_forget, ← Functor.assoc,
      sectR_comp_snd, a0_tp, Functor.id_comp]
  · intro x
    simp [unpath, PGrpd.objFiber', PGrpd.objFiber, Grpd.eqToHom_obj]
  · intro x y f
    simp [unpath, PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    simp

@[simp]
lemma sectR_true_comp_unpath : sectR ⟨⟨.true⟩⟩ _ ⋙ unpath a0_tp a1_tp p_tp = a1 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, unpath, Functor.Grothendieck.functorTo_forget, ← Functor.assoc,
      sectR_comp_snd, a1_tp, Functor.id_comp]
  · intro x
    simp [unpath, PGrpd.objFiber', PGrpd.objFiber, Grpd.eqToHom_obj]
  · intro x y f
    simp [unpath, PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    simp

lemma path0_unpath : path0 (unpath a0_tp a1_tp p_tp) = a0 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp
  · intro x
    simpa [unpath] using PGrpd.objFiber'_heq a0_tp
  · intro x y f
    simpa [unpath] using PGrpd.mapFiber'_heq a0_tp f

lemma path1_unpath : path1 (unpath a0_tp a1_tp p_tp) = a1 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp
  · intro x
    simpa [unpath] using PGrpd.objFiber'_heq a1_tp
  · intro x y f
    simpa [unpath] using PGrpd.mapFiber'_heq a1_tp f

lemma pathFibObj_unpath (x) : pathFibObj (unpath_comp_forgetToGrpd a0_tp a1_tp p_tp) x =
    PGrpd.objFiber' p_tp x := by
  dsimp only [pathFibObj]
  apply Discrete.ext
  simp [PGrpd.mapFiber, unpath]

lemma mapFiber_unpath_ft (x) : PGrpd.mapFiber (unpath a0_tp a1_tp p_tp) (ft x) =
    eqToHom (by simp [PGrpd.mapObjFiber, unpath, PGrpd.objFiber]) ≫
    (PGrpd.objFiber' p_tp x).as := by
  dsimp [unpath, PGrpd.mapFiber]
  simp

lemma path_unpath : path (A := A) (unpath_comp_forgetToGrpd a0_tp a1_tp p_tp) = p := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [path_comp_forgetToGrpd, p_tp]
    rw! [path0_unpath, path1_unpath]
  · intro x
    exact heq_of_eq_of_heq (pathFibObj_unpath ..) (PGrpd.objFiber'_heq p_tp)
  · intro x y f
    dsimp only [path]
    apply heq_of_eq_of_heq (PGrpd.functorTo_map_fiber _ _ _ _ (pathFibMap_comp _) _)
    dsimp only [pathFibMap]
    apply HEq.trans _ (PGrpd.mapFiber'_heq p_tp f)
    apply Discrete.Hom.hext
    · simp
    · simp only [heq_eq_eq]
      ext
      simp [IdMap_path, map_objFiber'_mapFiber', mapFiber_unpath_ft]
    · simp [pathFibObj_unpath]

end

section

variable {p : Grpd.Interval × Γ ⥤ PGrpd} (p_tp : p ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A)
    (δ0_p : path0 p = a0) (δ1_p : path1 p = a1)

include δ0_p p_tp in
lemma a0_comp_forgetToGrpd : a0 ⋙ PGrpd.forgetToGrpd = A := by
  rw [← δ0_p, path0, Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

include δ1_p p_tp in
lemma a1_comp_forgetToGrpd : a1 ⋙ PGrpd.forgetToGrpd = A := by
  rw [← δ1_p, path1, Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

lemma obj_ff_fiber (x) : (p.obj (ff x)).fiber ≍
    PGrpd.objFiber' (a0_comp_forgetToGrpd p_tp δ0_p) x := by
  symm
  convert PGrpd.objFiber'_heq (path0_comp_forgetToGrpd p_tp) (x := x)
  rw [← δ0_p]

lemma obj_tt_fiber (x) : (p.obj (tt x)).fiber ≍
    PGrpd.objFiber' (a1_comp_forgetToGrpd p_tp δ1_p) x := by
  symm
  convert PGrpd.objFiber'_heq (path1_comp_forgetToGrpd p_tp) (x := x)
  rw [← δ1_p]

lemma map_ff_fiber {x y : Γ} (f : ff x ⟶ ff y) : (p.map f).fiber ≍
    PGrpd.mapFiber' (a0_comp_forgetToGrpd p_tp δ0_p) f.2 := by
  symm
  convert PGrpd.mapFiber'_heq p_tp f
  · rw! [← obj_ff_fiber p_tp δ0_p x]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← obj_ff_fiber p_tp δ0_p y]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← δ0_p, path0, PGrpd.mapFiber'_naturality p_tp (sectR { down := { as := false } } Γ)]
    rw! [PGrpd.mapFiber'_heq p_tp]
    rw! [PGrpd.mapFiber'_heq p_tp f]
    rfl

lemma map_tt_fiber {x y : Γ} (f : tt x ⟶ tt y) : (p.map f).fiber ≍
    PGrpd.mapFiber' (a1_comp_forgetToGrpd p_tp δ1_p) f.2 := by
  symm
  convert PGrpd.mapFiber'_heq p_tp f
  · rw! [← obj_tt_fiber p_tp δ1_p x]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← obj_tt_fiber p_tp δ1_p y]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← δ1_p, path1, PGrpd.mapFiber'_naturality p_tp (sectR { down := { as := true } } Γ)]
    rw! [PGrpd.mapFiber'_heq p_tp]
    rw! [PGrpd.mapFiber'_heq p_tp f]
    rfl

lemma mapFiber'_ffm {x y : Γ} (f : x ⟶ y) : PGrpd.mapFiber' p_tp (ffm f) ≍
    PGrpd.mapFiber' (a0_comp_forgetToGrpd p_tp δ0_p) f := by
  rw! [← δ0_p, PGrpd.mapFiber'_naturality p_tp (sectR ..)]
  simp

lemma mapFiber'_ttm {x y : Γ} (f : x ⟶ y) : PGrpd.mapFiber' p_tp (ttm f) ≍
    PGrpd.mapFiber' (a1_comp_forgetToGrpd p_tp δ1_p) f := by
  rw! [← δ1_p, PGrpd.mapFiber'_naturality p_tp (sectR ..)]
  simp

@[simp]
lemma objFiber_path (x) : PGrpd.objFiber (path p_tp) x = pathFibObj p_tp x :=
  rfl

lemma objFiber'_path_as (x) : (PGrpd.objFiber' (path_comp_forgetToGrpd p_tp) x).as =
    eqToHom (by simp [objFiber'_path0 p_tp]) ≫ PGrpd.mapFiber' p_tp (ft x) := by
  rfl

lemma mapFiber_ft (x) : PGrpd.mapFiber p (ft x) ≍
    (PGrpd.objFiber' (path_comp_forgetToGrpd p_tp) x).as := by
  symm
  rw [objFiber'_path_as]
  simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, PGrpd.mapFiber',
    Grpd.forgetToCat, Functor.Grothendieck.forget_obj, PGrpd.objFiber'EqToHom,
    PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc, PGrpd.mapFiber]
  apply HEq.trans (eqToHom_comp_heq ..)
  simp

include p_tp in
lemma map_ft_base (x) : (p.map (ft x)).base = eqToHom (by
    have h0 := Functor.congr_obj p_tp (ff x)
    have h1 := Functor.congr_obj p_tp (tt x)
    simp at *
    rw [h0, h1]) := by
  simpa using Functor.congr_hom p_tp (ft x)

include p_tp in
lemma map_tf_base (x) : (p.map (tf x)).base = eqToHom (by
    have h0 := Functor.congr_obj p_tp (ff x)
    have h1 := Functor.congr_obj p_tp (tt x)
    simp at *
    rw [h0, h1]) := by
  simpa using Functor.congr_hom p_tp (tf x)

include p_tp in
lemma inv_mapFiber_tf_heq (y : Γ) :
    inv (PGrpd.mapFiber p (tf y)) ≍ PGrpd.mapFiber p (ft y) := by
  have : inv (tf y : tt y ⟶ (ff y : Grpd.Interval × Γ)) = ft y := by
    apply IsIso.inv_eq_of_hom_inv_id
    aesop_cat
  rw [← this]
  rw [PGrpd.mapFiber_inv]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  rw! [PGrpd.inv_mapFiber_heq]
  simp only [Grpd.forgetToCat, Functor.Grothendieck.forget_obj, Functor.comp_obj, Functor.comp_map,
    Functor.Grothendieck.forget_map, Cat.of_α, id_eq, cast_heq_iff_heq]
  rw! [map_tf_base p_tp, Grpd.eqToHom_hom]
  simp only [Grpd.forgetToCat, PGrpd.mapFiber, cast_heq_iff_heq]
  rw! (castMode := .all) [Functor.map_inv]
  simp

open PGrpd in
lemma unpath_map_ft_fiber {x y} (f : ff x ⟶ tt y) :
    ((unpath (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.path p_tp)
    (by rw [path_comp_forgetToGrpd]; congr)).map f).fiber ≍ (p.map f).fiber := by
  simp only [Grpd.forgetToCat, unpath, Functor.Grothendieck.functorTo_obj_base,
    Functor.comp_obj, snd_obj, Cat.of_α, Functor.Grothendieck.functorTo_map_base,
    Functor.comp_map, snd_map, id_eq, Functor.Grothendieck.functorTo_obj_fiber, unpathFibObj,
    Functor.Grothendieck.functorTo_map_fiber, unpathFibMap]
  -- have hf : f = ttm f.2 ≫ ft y := by aesop_cat
  -- TODO: mwe and report: this should not type check
  have hf : f = ffm f.2 ≫ ft y := by aesop_cat
  conv => rhs; rw! (castMode := .all) [hf]
  simp only [heq_eqRec_iff_heq]
  convert_to _ ≍ mapFiber _ _
  erw [mapFiber_comp]
  rw! [← mapFiber'_ffm p_tp δ0_p]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  apply Grpd.comp_heq_comp
  · erw [Functor.congr_obj p_tp (tt y)]
    simp
  · have H := Functor.congr_hom p_tp (ffm f.2)
    simp only [Grpd.forgetToCat, Functor.comp_obj, Functor.Grothendieck.forget_obj,
      Functor.comp_map, Functor.Grothendieck.forget_map, snd_obj, snd_map,
      Grpd.comp_eq_comp] at H
    erw [Functor.congr_hom p_tp (ft y)]
    rw! [← δ0_p, path0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [mapObjFiber, Grpd.eqToHom_obj, objFiber, Functor.congr_obj H,
      Grpd.eqToHom_obj]
  · simp only [Functor.Grothendieck.forget_map]
    rw! [← δ0_p, path0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq,
      map_ft_base p_tp, Grpd.eqToHom_obj]
    simp [objFiber]
  · rw! [← δ1_p, path1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [objFiber]
  · simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, Grpd.forgetToCat,
      Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map, cast_heq_iff_heq]
    rw! [map_ft_base p_tp, mapFiber'_heq]
    simp [Grpd.eqToHom_hom, mapFiber]
  · rw! [mapFiber_ft p_tp y]
    simp only [Grpd.forgetToCat, Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map,
      objFiber'_rfl, heq_cast_iff_heq]
    apply Discrete.as_heq_as
    · congr
      · symm; assumption
      · symm; assumption
    · apply (objFiber'_heq ..).trans
      simp [objFiber]

open PGrpd in
lemma unpath_map_tf_fiber {x y} (f : tt x ⟶ ff y) :
    ((unpath (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.path p_tp)
    (by rw [path_comp_forgetToGrpd]; congr)).map f).fiber ≍ (p.map f).fiber := by
  simp only [Grpd.forgetToCat, unpath, Functor.Grothendieck.functorTo_obj_base, Functor.comp_obj,
    snd_obj, Cat.of_α, Functor.Grothendieck.functorTo_map_base, Functor.comp_map, snd_map, id_eq,
    Functor.Grothendieck.functorTo_obj_fiber, unpathFibObj, Functor.Grothendieck.functorTo_map_fiber,
    unpathFibMap]
  have hf : f = ttm f.2 ≫ tf y := by aesop_cat
  conv => rhs; rw! (castMode := .all) [hf]
  simp only [heq_eqRec_iff_heq]
  convert_to _ ≍ mapFiber _ _
  erw [mapFiber_comp]
  rw! [← mapFiber'_ttm p_tp δ1_p f.2]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  have : A.obj y ≍ forgetToGrpd.obj (p.obj (ff y)) := by erw [Functor.congr_obj p_tp (ff y)]; simp
  have : objFiber' (a0_comp_forgetToGrpd p_tp δ0_p) y ≍ objFiber p (ff y) := by
    rw! [← δ0_p, path0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [objFiber]
  apply Grpd.comp_heq_comp
  · assumption
  · have H := Functor.congr_hom p_tp (ttm f.2)
    simp only [Grpd.forgetToCat, Functor.comp_obj, Functor.Grothendieck.forget_obj,
      Functor.comp_map, Functor.Grothendieck.forget_map, snd_obj, snd_map,
      Grpd.comp_eq_comp] at H
    erw [Functor.congr_hom p_tp (tf y)]
    rw! [← δ1_p, path1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [mapObjFiber, Grpd.eqToHom_obj, objFiber, Functor.congr_obj H,
      Grpd.eqToHom_obj]
  · simp only [Functor.Grothendieck.forget_map]
    rw! [← δ1_p, path1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq,
      map_tf_base p_tp, Grpd.eqToHom_obj]
    simp [objFiber]
  · assumption
  · simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, Grpd.forgetToCat,
      Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map, cast_heq_iff_heq]
    rw! [map_tf_base p_tp, mapFiber'_heq]
    simp [Grpd.eqToHom_hom, mapFiber]
  · apply Grpd.inv_heq_of_heq_inv
    · assumption
    · assumption
    · rw! [← obj_tt_fiber p_tp δ1_p]
      simp [mapObjFiber, objFiber, map_tf_base p_tp, Grpd.eqToHom_obj]
    · simp [objFiber', Grpd.eqToHom_obj]
      apply HEq.trans (b := (pathFibObj p_tp y).as)
      · apply Discrete.as_heq_as
        · congr 1
          · rw! [← δ0_p]
            simp [path0, objFiber_naturality, Grpd.eqToHom_obj, objFiber']
          · rw! [← δ1_p]
            simp [path1, objFiber_naturality, Grpd.eqToHom_obj, objFiber']
        · simp
      · simp
        apply HEq.trans (eqToHom_comp_heq ..)
        rw! [inv_mapFiber_tf_heq p_tp, mapFiber'_heq]
        simp [mapFiber]

lemma unpath_path : unpath (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.path p_tp) (by rw [path_comp_forgetToGrpd]; congr) = p := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp only [unpath, Functor.Grothendieck.functorTo_forget, p_tp]
  · intro x
    rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
    · simpa [unpath] using (obj_ff_fiber p_tp δ0_p x).symm
    · simpa [unpath] using (obj_tt_fiber p_tp δ1_p x).symm
  · intro x y f
    rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
    · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
      · simpa [unpath] using (map_ff_fiber p_tp δ0_p f).symm
      · exact unpath_map_ft_fiber p_tp δ0_p δ1_p f
    · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
      · exact unpath_map_tf_fiber p_tp δ0_p δ1_p f
      · simpa [unpath] using (map_tt_fiber p_tp δ1_p f).symm

end

end Path

end FunctorOperation

namespace GroupoidModel

open Grpd Model.UnstructuredUniverse

def cylinder : Cylinder Grpd := .ofCartesianMonoidalCategoryLeft Interval δ0 δ1

namespace UId

variable {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A)

include a0_tp in
lemma pt_tp : toCoreAsSmallEquiv a0 ⋙ PGrpd.forgetToGrpd = toCoreAsSmallEquiv A := by
  rw [← a0_tp, Grpd.comp_eq_comp, U.tp, toCoreAsSmallEquiv_apply_comp_right]

def Id : Γ ⟶ U.{v}.Ty :=
  toCoreAsSmallEquiv.symm (FunctorOperation.Id (A := toCoreAsSmallEquiv A)
    (a0 := toCoreAsSmallEquiv a0) (a1 := toCoreAsSmallEquiv a1)
    (pt_tp a0 a0_tp)
    (pt_tp a1 a1_tp))

lemma Id_comp :
    UId.Id (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp only [Category.assoc, a0_tp, U_Ty])
      (by simp only [Category.assoc, a1_tp, U_Ty]) = σ ≫ UId.Id a0 a1 a0_tp a1_tp := by
  dsimp only [U_Ty, comp_eq_comp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.Id_comp]

section

variable (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A)

def path : Γ ⟶ U.{v}.Tm := toCoreAsSmallEquiv.symm <|
  FunctorOperation.Path.path (A := toCoreAsSmallEquiv A) (p := toCoreAsSmallEquiv p) (by
    rw [← toCoreAsSmallEquiv_apply_comp_left]
    rw [← toCoreAsSmallEquiv_apply_comp_right,
      EmbeddingLike.apply_eq_iff_eq]
    exact p_tp)

lemma path_comp : path (A := σ ≫ A) (cylinder.I.map σ ≫ p) (by rw [Category.assoc, p_tp,
    ← Category.assoc, cylinder.π.naturality, Category.assoc, Functor.id_map]) =
    σ ≫ path p p_tp := by
  dsimp [path]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.Path.path_comp]

lemma path_tp (δ0_p : cylinder.δ0.app Γ ≫ p = a0) (δ1_p : cylinder.δ1.app Γ ≫ p = a1) :
    path p p_tp ≫ U.tp = UId.Id (A := A) a0 a1
    (by rw [← δ0_p, Category.assoc, p_tp, Cylinder.δ0_π'_app_assoc])
    (by rw [← δ1_p, Category.assoc, p_tp, Cylinder.δ1_π'_app_assoc]) := by
  dsimp [path, U.tp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, FunctorOperation.Path.path_comp_forgetToGrpd]
  congr 2
  · rw [← δ0_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl
  · rw [← δ1_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl

end

section

variable (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = UId.Id a0 a1 a0_tp a1_tp)

def unpath : cylinder.I.obj Γ ⟶ U.{v}.Tm :=
  have p_tp' : toCoreAsSmallEquiv p ⋙ PGrpd.forgetToGrpd =
      FunctorOperation.Id (pt_tp a0 a0_tp) (pt_tp a1 a1_tp) := by
    dsimp [U.tp, Id] at p_tp
    rw [← toCoreAsSmallEquiv_apply_comp_right, p_tp, Equiv.apply_symm_apply]
  toCoreAsSmallEquiv.symm <| FunctorOperation.Path.unpath _ _ p_tp'

lemma unpath_tp : unpath a0 a1 a0_tp a1_tp p p_tp ≫ U.tp = cylinder.π.app Γ ≫ A := by
  dsimp [unpath, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, toCoreAsSmallEquiv.symm_apply_eq,
    toCoreAsSmallEquiv_apply_comp_left, FunctorOperation.Path.unpath_comp_forgetToGrpd]
  rfl

lemma δ0_unpath : cylinder.δ0.app Γ ≫ unpath a0 a1 a0_tp a1_tp p p_tp = a0 := by
  dsimp [unpath]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, toCoreAsSmallEquiv.symm_apply_eq]
  apply FunctorOperation.Path.sectR_false_comp_unpath

lemma δ1_unpath : cylinder.δ1.app Γ ≫ unpath a0 a1 a0_tp a1_tp p p_tp = a1 := by
  dsimp [unpath]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, toCoreAsSmallEquiv.symm_apply_eq]
  apply FunctorOperation.Path.sectR_true_comp_unpath

lemma path_unpath : path (A := A) (unpath a0 a1 a0_tp a1_tp p p_tp) (unpath_tp ..) = p := by
  dsimp [path, unpath]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  rw! (transparency := .default) [toCoreAsSmallEquiv.apply_symm_apply]
  apply FunctorOperation.Path.path_unpath

end

lemma unpath_path (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A)
    (δ0_p : cylinder.δ0.app Γ ≫ p = a0) (δ1_p : cylinder.δ1.app Γ ≫ p = a1) :
    unpath (A := A) a0 a1 (by simp [← δ0_p, - Grpd.comp_eq_comp, p_tp])
    (by simp [← δ1_p, - Grpd.comp_eq_comp, p_tp]) (path p p_tp)
    (path_tp a0 a1 p p_tp δ0_p δ1_p) = p := by
  dsimp [unpath, path]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  rw! (transparency := .default) [toCoreAsSmallEquiv.apply_symm_apply]
  apply FunctorOperation.Path.unpath_path
  · simp [FunctorOperation.Path.path0, ← toCoreAsSmallEquiv_apply_comp_left, ← δ0_p]
    rfl
  · simp [FunctorOperation.Path.path1, ← toCoreAsSmallEquiv_apply_comp_left, ← δ1_p]
    rfl

namespace hurewiczUTp

attribute [local irreducible] tpClovenIsofibration

variable (σ : Δ ⟶ Γ) (p0 : Γ ⟶ U.{v}.Tm) (p : cylinder.I.obj Γ ⟶ U.Ty)
    (p0_tp : p0 ≫ U.tp = cylinder.δ0.app Γ ≫ p)

@[simp]
def liftObj : Grpd.Interval × Γ → U.{v}.Tm
| ⟨⟨⟨.false⟩⟩, x2⟩ => p0.obj x2
| ⟨⟨⟨.true⟩⟩, x2⟩ => tpClovenIsofibration.liftObj (p.map (FunctorOperation.Path.ft x2))
    (Functor.congr_obj p0_tp x2)

@[simp]
abbrev liftMap0 {x2 : Γ} {y : Grpd.Interval × Γ} (f : FunctorOperation.Path.ff x2 ⟶ y) :=
  tpClovenIsofibration.liftIso (X' := p0.obj x2) (p.map f) (Functor.congr_obj p0_tp x2)

open FunctorOperation.Path

@[simp]
def liftMap : {x y : Grpd.Interval × Γ} → (f : x ⟶ y) →
    liftObj p0 p p0_tp x ⟶ liftObj p0 p p0_tp y
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, _⟩, f => p0.map f.2
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => p0.map f.2 ≫ liftMap0 p0 p p0_tp (ft y2)
| ⟨⟨⟨.true⟩⟩, x2⟩, ⟨⟨⟨.false⟩⟩, _⟩, f => inv (liftMap0 p0 p p0_tp (ft x2)) ≫ p0.map f.2
| ⟨⟨⟨.true⟩⟩, x2⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => inv (liftMap0 p0 p p0_tp (ft x2)) ≫
  p0.map f.2 ≫ liftMap0 p0 p p0_tp (ft y2)

lemma liftMap_id (x) : liftMap p0 p p0_tp (𝟙 x) = 𝟙 (liftObj p0 p p0_tp x) := by
  rcases x with ⟨⟨⟨_|_⟩⟩, _⟩ <;> simp

lemma liftMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    liftMap p0 p p0_tp (f ≫ g) = liftMap p0 p p0_tp f ≫ liftMap p0 p p0_tp g := by
  rcases x with ⟨⟨⟨_|_⟩⟩, _⟩
  all_goals rcases y with ⟨⟨⟨_|_⟩⟩, _⟩
  all_goals rcases z with ⟨⟨⟨_|_⟩⟩, _⟩
  all_goals simp [liftMap]

@[simps]
def lift : cylinder.I.obj Γ ⟶ U.{v}.Tm where
  obj := liftObj p0 p p0_tp
  map := liftMap p0 p p0_tp
  map_id := liftMap_id p0 p p0_tp
  map_comp := liftMap_comp p0 p p0_tp

lemma lift_comp_tp :
    hurewiczUTp.lift p0 p p0_tp ≫ U.tp = p := by
  fapply CategoryTheory.Functor.ext
  · intro x
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · simpa using Functor.congr_obj p0_tp x
    · simp
  · intro x y f
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · erw [Functor.congr_hom p0_tp f.2]
        simp
        rfl
      · simp only [U_Tm, comp_eq_comp, Functor.comp_obj, lift_obj, liftObj, U_Ty, U_tp,
          Functor.comp_map, lift_map, liftMap, liftMap0, Functor.map_comp]
        erw [Functor.congr_hom p0_tp f.2]
        simp only [U_Tm, comp_eq_comp, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Category.assoc]
        have : f = ffm f.2 ≫ ft y := by aesop
        conv => rhs; rw [this]
        rw [Functor.map_comp]
        rw [Functor.ClovenIsofibration.map_liftIso']
        simp [← Category.assoc]
        rfl
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · simp only [U_Tm, comp_eq_comp, Functor.comp_obj, lift_obj, liftObj, U_Ty, U_tp,
          Functor.comp_map, lift_map, liftMap, liftMap0, Functor.map_comp, Functor.map_inv,
          IsIso.inv_comp_eq]
        erw [Functor.congr_hom p0_tp f.2]
        have : f = tf x ≫ ffm f.2 := by aesop
        slice_rhs 2 3 => rw [this]
        rw [Functor.ClovenIsofibration.map_liftIso', Functor.map_comp]
        simp only [U_Tm, comp_eq_comp, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        have : ft x ≫ tf x = 𝟙 _ := by aesop
        slice_rhs 2 3 => rw [← Functor.map_comp, this, CategoryTheory.Functor.map_id]
        rfl
      · simp only [U_Tm, comp_eq_comp, Functor.comp_obj, lift_obj, liftObj, U_Ty, U_tp,
          Functor.comp_map, lift_map, liftMap, liftMap0, Functor.map_comp, Functor.map_inv,
          IsIso.inv_comp_eq]
        erw [Functor.congr_hom p0_tp f.2]
        rw [Functor.ClovenIsofibration.map_liftIso', Functor.ClovenIsofibration.map_liftIso']
        simp only [U_Tm, comp_eq_comp, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          ← Category.assoc, ← heq_eq_eq, heq_comp_eqToHom_iff, comp_eqToHom_heq_iff]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
          ← Functor.map_comp, heq_eq_eq]
        have : ft x ≫ f = ffm f.2 ≫ ft y := by aesop
        conv => rhs; rw [this]
        rfl

lemma δ0_comp_lift : cylinder.δ0.app Γ ≫ hurewiczUTp.lift p0 p p0_tp = p0 := by
  fapply CategoryTheory.Functor.ext
  · intro x
    convert_to (lift p0 p p0_tp).obj ⟨⟨⟨.false⟩⟩, x⟩ = _
    simp
  · intro x y f
    convert_to (lift p0 p p0_tp).map (ffm f) = _
    simp

@[simp]
lemma I_map_obj_ff (x : Δ) : (cylinder.I.map σ).obj ({ down := { as := false } }, x) =
    ({ down := { as := false } }, σ.obj x) := by
  rfl

lemma lift_map_ffm {x y : Δ} (f : x ⟶ y) : (lift p0 p p0_tp).map (ffm (σ.map f)) =
    p0.map (σ.map f) := by
  simp [liftMap]

lemma lift_map_ft (x : Δ) : (lift p0 p p0_tp).map (ft (σ.obj x)) =
    tpClovenIsofibration.liftIso (p.map (ft (σ.obj x)))
    (by simpa using Functor.congr_obj p0_tp (σ.obj x)) := by
  simp [liftObj, liftMap]

lemma lift_map_ft' (x : Δ) : (lift p0 p p0_tp).map (ft (σ.obj x)) =
    tpClovenIsofibration.liftIso (p.map (⟨⟨⟨⟩⟩, σ.map (𝟙 _)⟩ : ff (σ.obj x) ⟶ tt (σ.obj x)))
    (by simpa using Functor.congr_obj p0_tp (σ.obj x)) ≫ eqToHom (by simp) := by
  simp only [U_Tm, lift_obj, liftObj, U_Ty, U_tp, ft, lift_map, liftMap,
    CategoryTheory.Functor.map_id, liftMap0, Category.id_comp, ← heq_eq_eq, heq_comp_eqToHom_iff]
  rw! (castMode := .all) [← CategoryTheory.Functor.map_id]
  rfl

lemma lift_map_tf (x : Δ) : (lift p0 p p0_tp).map (tf (σ.obj x)) =
    eqToHom (by simp; rfl) ≫ inv (tpClovenIsofibration.liftIso (p.map (ft (σ.obj x)))
      (by simpa using Functor.congr_obj p0_tp (σ.obj x))) := by
  simp [liftMap]

lemma lift_map_tf' (x : Δ) : (lift p0 p p0_tp).map (tf (σ.obj x)) =
    eqToHom (by simp [ft]; rfl) ≫
    inv (tpClovenIsofibration.liftIso (p.map (⟨⟨⟨⟩⟩, σ.map (𝟙 _)⟩ : ff (σ.obj x) ⟶ tt (σ.obj x)))
    (by simpa using Functor.congr_obj p0_tp (σ.obj x))) := by
  simp only [U_Tm, lift_obj, liftObj, U_Ty, U_tp, ft, tf, lift_map, liftMap, liftMap0,
    CategoryTheory.Functor.map_id, Category.comp_id, ← heq_eq_eq, heq_eqToHom_comp_iff]
  rw! (castMode := .all) [← CategoryTheory.Functor.map_id]
  rfl

lemma lift_comp : lift (σ ≫ p0) (cylinder.I.map σ ≫ p)
    (by simp [p0_tp, - Grpd.comp_eq_comp, ← cylinder.δ0.naturality_assoc]) =
    cylinder.I.map σ ≫ lift p0 p p0_tp := by
  fapply CategoryTheory.Functor.ext
  · intro x
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · convert_to _ = (lift p0 p p0_tp).obj (ff (σ.obj x))
      simp
    · convert_to _ = (lift p0 p p0_tp).obj (tt (σ.obj x))
      simp only [U_Tm, comp_eq_comp, lift_obj, liftObj, U_Ty, U_tp, Functor.comp_obj,
        Functor.comp_map]
      congr
      conv => rhs; rw [ft, ← CategoryTheory.Functor.map_id]
      rfl
  · intro x y f
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · have : (cylinder.I.map σ).map f = ffm (σ.map f.2) := by aesop
        slice_rhs 2 3 => simp only [Grpd.comp_eq_comp, Functor.comp_map, this, lift_map_ffm]
        simp
      · have : (cylinder.I.map σ).map f = ffm (σ.map f.2) ≫ ft (σ.obj y) := by aesop
        slice_rhs 2 3 => simp only [Grpd.comp_eq_comp, Functor.comp_map, this, Functor.map_comp,
          lift_map_ffm, lift_map_ft']
        simp [ft]
        rfl
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · have : (cylinder.I.map σ).map f = tf (σ.obj x) ≫ ffm (σ.map f.2) := by aesop
        slice_rhs 2 3 => simp only [Grpd.comp_eq_comp, Functor.comp_map, this, Functor.map_comp,
          lift_map_ffm, lift_map_tf']
        simp [← heq_eq_eq]
        rfl
      · have : (cylinder.I.map σ).map f = tf (σ.obj x) ≫ ffm (σ.map f.2) ≫ ft (σ.obj y) := by aesop
        slice_rhs 2 3 => simp only [Grpd.comp_eq_comp, Functor.comp_map, this, Functor.map_comp,
          lift_map_ffm, lift_map_tf', lift_map_ft']
        simp only [U_Tm, comp_eq_comp, lift_obj, liftObj, U_Ty, U_tp, Functor.comp_obj, ft,
          Functor.comp_map, lift_map, liftMap, liftMap0, Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp, IsIso.eq_inv_comp]
        erw [IsIso.hom_inv_id_assoc]
        rfl

open Functor.ClovenIsofibration.IsSplit in
lemma isNormal (A : Γ ⟶ U.Ty) (π_A : p = CategoryTheory.Prod.snd _ Γ ≫ A) :
    lift p0 p p0_tp = CategoryTheory.Prod.snd _ Γ ≫ p0 := by
  have : tpClovenIsofibration.IsSplit := inferInstance -- FIXME
  subst π_A
  fapply CategoryTheory.Functor.ext
  · intro x
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · simp
    · simp [ft]
      rw [liftObj_id]
  · intro x y f
    rcases x with ⟨⟨⟨_|_⟩⟩, x⟩
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · simp
      · simp only [U_Tm, comp_eq_comp, lift_obj, liftObj, U_Ty, U_tp, Functor.comp_obj,
          Prod.snd_obj, Functor.comp_map, Prod.snd_map, lift_map, liftMap, liftMap0,
          eqToHom_refl, Category.id_comp]
        rw! [CategoryTheory.Functor.map_id, liftIso_id]
    · rcases y with ⟨⟨⟨_|_⟩⟩, y⟩
      · simp only [U_Tm, comp_eq_comp, lift_obj, liftObj, U_Ty, U_tp, Functor.comp_obj,
          Prod.snd_obj, Functor.comp_map, Prod.snd_map, lift_map, liftMap, liftMap0,
          eqToHom_refl, Category.comp_id, IsIso.inv_comp_eq]
        rw! [CategoryTheory.Functor.map_id, liftIso_id]
        simp
      · simp
        rw! [CategoryTheory.Functor.map_id, liftIso_id]
        slice_rhs 1 2 => rw! [CategoryTheory.Functor.map_id, liftIso_id]
        simp

end hurewiczUTp

end UId

open UId hurewiczUTp

def UPath : GroupoidModel.U.{v}.PathType cylinder where
  Path := Id
  Path_comp := Id_comp
  path := path
  path_comp := path_comp
  path_tp := path_tp
  unpath := unpath
  unpath_tp := unpath_tp
  δ0_unpath := δ0_unpath
  δ1_unpath := δ1_unpath
  unpath_path := unpath_path
  path_unpath := path_unpath

def hurewiczUTp : cylinder.Hurewicz U.{v}.tp where
  lift := lift
  lift_comp_self := lift_comp_tp
  δ0_comp_lift := δ0_comp_lift

instance : hurewiczUTp.IsUniform where
  lift_comp := lift_comp

instance : hurewiczUTp.IsNormal where
  isNormal := isNormal

def UId : GroupoidModel.U.{v,max u (v+1) (v₁+1)}.PolymorphicIdElim UPath.polymorphicIdIntro
    GroupoidModel.U.{v₁, max u (v+1) (v₁+1)} :=
  @UPath.polymorphicIdElim _ _ _ _ hurewiczUTp _ _ _ hurewiczUTp _ _

end GroupoidModel
