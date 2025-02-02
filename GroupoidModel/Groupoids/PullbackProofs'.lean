import GroupoidModel.Groupoids.PullBackProofs
universe u v u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

namespace ULift

@[simp] theorem upFunctor_downFunctor {C : Type u} [Category.{v} C]
    : upFunctor.{v,u,u₁} ⋙ downFunctor.{v,u,u₁} = Functor.id C := rfl

@[simp] theorem downFunctor_upFunctor {C : Type u} [Category.{v} C] :
    downFunctor.{v,u,u₁} ⋙ upFunctor.{v,u,u₁}
    = Functor.id (ULift.{u₁, u} C) := rfl

end ULift

namespace Cat

/- This is general, but requires universe level annotations -/
def uLift : Cat.{v,u} ⥤ Cat.{v,max u u₁} where
  obj x := Cat.of (ULift.{u₁, u} x)
  map {x y} f := ULift.downFunctor.{v,u,u₁} ⋙ f ⋙ ULift.upFunctor.{v,u,u₁}

@[simp] theorem uLift.id {C : Cat.{v,u}} (x : uLift.obj.{u,v,u₁} C) :
    CategoryStruct.id x  = CategoryStruct.id x.down := rfl

@[simp] theorem uLift.comp {C : Cat.{v,u}} {x y z : uLift.obj.{u,v,u₁} C}
    (f : x ⟶ y) (g : y ⟶ z) : f ≫ g
    = (f : x.down ⟶ y.down) ≫ (g : y.down ⟶ z.down) := rfl

end Cat

/-- This turns the object part of eqToHom functors into casts -/
theorem eqToHom_obj {C1 C2 : Cat.{u,v}}(x : C1)(eq : C1 = C2): (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

namespace Grothendieck

variable {Γ : Cat.{u,u}} (A : Γ ⥤ Cat.{u,u})

def toPCat : Grothendieck A ⥤ PCat where
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
    · simp [A.map_comp, Cat.comp_eq_comp]

theorem toPCat_obj_fiber_inj {x y : Grothendieck A}
    (h : HEq ((toPCat A).obj x).str.pt ((toPCat A).obj y).str.pt) : HEq x.fiber y.fiber := h

-- theorem toPCat_map_fiber_inj {x y w z: Grothendieck A} {f : x ⟶ y} {g : w ⟶ z}
--     (h : HEq ((toPCat A).map f).point ((toPCat A).map g).point) : HEq f.fiber g.fiber := h

-- example {α}{β : α → Type*}(p q : Sigma β) (h : p = q) : HEq p.2 q.2 := by exact?

-- theorem self_eq_mk {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Cat.{v₂,u₂}) {x : Grothendieck A} :
--     x = Grothendieck.mk x.base x.fiber := rfl

theorem obj_ext_hEq {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₂,u₂}} {x y : Grothendieck A}
    (hbase : x.base = y.base) (hfiber : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨xbase, xfiber⟩
  subst hbase
  subst hfiber
  rfl

theorem obj_ext_cast {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Cat.{v₂,u₂}) {x y : Grothendieck A}
    (hbase : x.base = y.base)
    (hfiber : cast (congrArg (λ x ↦ (A.obj x).α) hbase) x.fiber = y.fiber)
    : x = y := obj_ext_hEq hbase (heq_of_cast_eq (by simp[hbase]) (by simp[hfiber]))

open Functor

/-
In this section we prove that the following square is a PullBack

  Grothendieck A ---- toPCat ------> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetPoint
        |                           |
        v                           v
        Γ--------------A----------->Cat
-/
variable {Γ : Cat.{u,u}} (A : Γ ⥤ Cat.{u,u}) 

def uLiftGrothendieck : Cat.{u, u+1} :=
  Cat.uLift.obj.{u,u,u+1} (Cat.of $ Grothendieck A)

def uLiftGrothendieckForget : uLiftGrothendieck A ⟶ Cat.uLift.obj.{u,u,u+1} Γ :=
  Cat.uLift.map.{u,u,u+1} (Grothendieck.forget A)

def catCat : Cat.{u,u+1} := Cat.of Cat.{u,u}

def catPCat : Cat.{u,u+1} := Cat.of PCat.{u,u}

abbrev catPCatForgetPoint : catPCat ⟶ catCat :=
  PCat.forgetPoint

def var' : uLiftGrothendieck A ⟶ catPCat :=
  ULift.downFunctor ⋙ Grothendieck.toPCat A

abbrev A' : Cat.uLift.obj.{u,u,u+1} Γ ⟶ catCat :=
  ULift.downFunctor ⋙ A

variable {A}

theorem comm_sq : var' A ≫ PCat.forgetPoint
    = uLiftGrothendieckForget A ≫ A' A := by
  apply Functor.ext
  · intro X Y f
    rfl
  · intro 
    rfl

variable (A)

open Limits PullbackCone ULift

def cone : Limits.PullbackCone catPCatForgetPoint (A' A)
  := Limits.PullbackCone.mk (var' A) (uLiftGrothendieckForget A) comm_sq

variable {A} 

abbrev conePCatPt {s : PullbackCone catPCatForgetPoint (A' A)}
    (x : s.pt) := (s.fst.obj x).str.pt

/- This is an explicit natural transformation for the commuting condition for cone s -/
abbrev ε (s : PullbackCone catPCatForgetPoint (A' A))
    : s.fst ⋙ PCat.forgetPoint ⟶ s.snd ⋙ A' A :=
  eqToHom s.condition

abbrev εApp
    {s : PullbackCone catPCatForgetPoint (A' A)} (x : s.pt)
    : (s.fst ⋙ catPCatForgetPoint).obj x
    ⟶ (s.snd ⋙ A' A).obj x := (ε s).app x

abbrev εNaturality
    {s : PullbackCone catPCatForgetPoint (A' A)} {x y : s.pt}
    (f : x ⟶ y) := (ε s).naturality f

abbrev point' {s : PullbackCone catPCatForgetPoint (A' A)}
    {x y : s.pt} (f : x ⟶ y) :
    (s.fst.map f).obj (conePCatPt x) ⟶ conePCatPt y :=
  (s.fst.map f).point

@[simp] def lift_obj {s : PullbackCone catPCatForgetPoint (A' A)}
  (x : s.pt) : Grothendieck A := 
  ⟨ (s.snd.obj x).down , (εApp x).obj (conePCatPt x) ⟩

def lift_map {s : PullbackCone catPCatForgetPoint (A' A)}
  {x y : s.pt} (f : x ⟶ y) : lift_obj x ⟶ lift_obj y := 
  ⟨ s.snd.map f ,
    let m1 := (εApp y).map (point' f)
    let m2 := (eqToHom (εNaturality f).symm).app (conePCatPt x)
    m2 ≫ m1 ⟩

@[simp] theorem lift_map_base  {s : PullbackCone catPCatForgetPoint (A' A)}
    {x y : s.pt} (f : x ⟶ y) : (lift_map f).base = s.snd.map f := rfl

theorem lift_map_fiber  {s : PullbackCone catPCatForgetPoint (A' A)}
    {x y : s.pt} (f : x ⟶ y) : (lift_map f).fiber =
    (eqToHom (εNaturality f).symm).app (conePCatPt x) ≫ (εApp y).map (point' f) := rfl

variable {s : PullbackCone catPCatForgetPoint (A' A)} {x y : s.pt} (f : x ⟶ y)

theorem lift_map_fiber_pf3 : Cat.of (s.fst.obj y).α = A.obj (s.snd.obj y).down :=
  Functor.congr_obj s.condition y

theorem lift_map_fiber_pf2 : (A.map (s.snd.map f)).obj ((εApp x).obj (conePCatPt x))
    = (eqToHom lift_map_fiber_pf3).obj ((s.fst.map f).obj (conePCatPt x)) := by
  have h0 := Functor.congr_obj (εNaturality f).symm (conePCatPt x)
  simp at *
  rw [h0]
  
#check eqToHom_obj
theorem lift_map_fiber_pf0 :
    (eqToHom lift_map_fiber_pf3).obj (conePCatPt y)
    = (εApp y).obj (conePCatPt y) := by simp


theorem lift_map_fiber' (pf1 : ((s.fst.map f).obj (conePCatPt x) ⟶ conePCatPt y) =
      ((eqToHom lift_map_fiber_pf3).obj ((s.fst.map f).obj (conePCatPt x))
      ⟶ (eqToHom lift_map_fiber_pf3).obj (conePCatPt y)))
 : (lift_map f).fiber =
    eqToHom (lift_map_fiber_pf2 f) ≫ cast pf1 (point' f) ≫ eqToHom lift_map_fiber_pf0 := by
  have hy := Functor.congr_hom (eqToHom_app s.condition y) (point' f)
  have hx := eqToHom_app (εNaturality f).symm (conePCatPt x)
  rw [lift_map_fiber, hy, hx, Cat.eqToHom_hom]
  generalize_proofs
  
  simp[Cat.eqToHom_hom]

-- ((lift s).map f).fiber

def lift (s : PullbackCone catPCatForgetPoint (A' A)) :
  s.pt ⥤ Grothendieck A where
  obj x := lift_obj x
  map {x y} f := lift_map f
  map_id x := by
    apply Grothendieck.ext
    · have h0 := eqToHom_app (εNaturality (CategoryStruct.id x)).symm
      have h1 := dcongr_arg PointedFunctor.point
        (Functor.map_id s.fst x)
      have h2 : (PCat.category.id (s.fst.obj x)).point = CategoryStruct.id _
        := rfl
      have h3 := Functor.map_id (εApp x) ((s.fst.obj x).str).pt
      have h4 {a} (f : a ⟶ _) :
          f ≫ CategoryStruct.id ((εApp x).obj (conePCatPt x)) = f
        := Category.comp_id f
      simp [eqToHom_map, h0, h1, h2, h3, h4, lift_map_fiber]
    · simp
  map_comp {x y z} f g := by
    dsimp [Grothendieck.comp]
    apply Grothendieck.ext
    · dsimp
      have h1 := dcongr_arg PointedFunctor.point
        (Functor.map_comp s.fst f g)
      have h2 : (s.fst.map f ≫ s.fst.map g).point =
        ((s.fst.map g).map (s.fst.map f).point) ≫ (s.fst.map g).point := rfl
      have hgNatNatF := (eqToHom (εNaturality g).symm).naturality (s.fst.map f).point
      -- have h5 : ((ε s).app y ≫ (s.snd ≫ A' A).map g).map F.point =
      --     ((ε s).app y ⋙ (s.snd ≫ A' A).map g).map F.point := rfl
      have h6 := congr_arg (λ x ↦ x ≫ (εApp z).map (s.fst.map g).point) hgNatNatF
      -- rw [h5] at h6
      dsimp at h6
      simp only [Category.assoc, eqToHom_app (εNaturality g).symm] at h6
      simp only [h1, h2, map_comp, comp_fiber, Category.assoc, lift_map_fiber,
        eqToHom_map (A.map (s.snd.map g)),
        eqToHom_app (εNaturality f).symm, 
        eqToHom_app (εNaturality (f ≫ g)).symm,
        eqToHom_app (εNaturality g).symm, eqToHom_map]
      rw [h6]
      simp
    · simp
      rfl -- TODO fix

def lift' (s : PullbackCone catPCatForgetPoint (A' A)) :
    s.pt ⟶ uLiftGrothendieck A := (lift s) ⋙ ULift.upFunctor

theorem fac_left_aux (s : PullbackCone catPCatForgetPoint (A' A)) :
    lift s ⋙ ULift.upFunctor ⋙ ULift.downFunctor ⋙ Grothendieck.toPCat A = s.fst := by
  apply Functor.ext
  · intro x y f
    simp [lift, toPCat]
    have h := Functor.congr_hom s.condition f
    unfold catPCatForgetPoint PCat.forgetPoint at h
    simp at h
    congr 1
    · simp [h, PointedFunctor.eqToHom_toFunctor, ← Cat.comp_eq_comp]
    · simp only [lift_map, lift_obj, comp_obj, PCat.forgetPoint_obj, Cat.of_α, downFunctor_obj, ε, Functor.comp_map,
        downFunctor_map, Cat.comp_obj, PCat.forgetPoint_map, Cat.eqToHom_app, upFunctor_obj_down, PCat.comp_toFunctor,
        PointedFunctor.eqToHom_point, eqToHom_map, PCat.comp_point, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
        eqToHom_comp_heq_iff]
      generalize_proofs
      rename_i h1 h2
      simp only [Functor.congr_hom (eqToHom_app h1 y) (point' f), comp_obj, downFunctor_obj, PCat.forgetPoint_obj,
        Cat.of_α, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      refine heq_of_cast_eq ?_ ?_
      · congr 1 <;> simp [PointedFunctor.eqToHom_toFunctor]
      · simp [Cat.eqToHom_hom,PCat.eqToHom_hom]
  · intro x
    simp only [toPCat, lift, lift_obj, comp_obj,
      downFunctor_obj, Cat.eqToHom_app, upFunctor_obj_down]
    have h := (Functor.congr_obj s.condition x).symm
    simp only [Cat.comp_obj, comp_obj, downFunctor_obj, PCat.forgetPoint_obj] at h
    congr 1
    · rw [h]
      rfl
    · congr 1
      · rw [h]
        rfl
      · refine heq_of_cast_eq ?_ ?_
        · rw [h]
          rfl
        · simp [eqToHom_app, eqToHom_obj]
      · rw [h]
        simp only [heq_eq_eq]
        rfl

theorem fac_left (s : PullbackCone catPCatForgetPoint (A' A)) :
    lift s ⋙ Grothendieck.toPCat A = s.fst := fac_left_aux.{u,u} s

theorem fac_right (s : PullbackCone catPCatForgetPoint (A' A)) :
    lift s ⋙ ULift.upFunctor ⋙ ULift.downFunctor ⋙ Grothendieck.forget A ⋙ ULift.upFunctor
    = s.snd := by
  apply Functor.ext
  · intro x y f
    simp [lift]
  · intro
    simp [lift, upFunctor]

@[simp]
theorem comp_point {C D E : Type u} [PointedCategory.{v} C]
    [PointedCategory.{v} D] [PointedCategory.{v} E]
    (F : PointedFunctor C D) (G : PointedFunctor D E) :
    PointedFunctor.point (PointedFunctor.comp F G) = G.map (F.point) ≫ G.point := rfl

theorem eqToHom_base' {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}} (g1 g2 : Grothendieck A)
  (eq : g1 = g2) : (eqToHom eq).base = (eqToHom (congrArg (Grothendieck.forget A).obj eq)) := by
    cases eq
    simp

-- theorem uniq (s : PullbackCone PCat.forgetPoint (A' A)) (m : s.pt ⟶ uLiftGrothendieck A)
--     (hl : m ⋙ var' A = s.fst) (hr : m ⋙ uLiftGrothendieckForget A = s.snd) :
--     m  ⋙ ULift.downFunctor = lift s := by
--   apply Functor.ext
--   · intro x y f
--     apply Grothendieck.ext
--     · have h0 := Functor.congr_hom hl f
--       -- have h1 := Functor.congr_hom (fac_left.{u,u} s) f
--       have h2 := PointedFunctor.congr_point h0
--       -- have h3 := PointedFunctor.congr_point h1
--       -- simp only [comp_point] at h2
      
--       simp [var', toPCat] at h2
--       simp 
--       rw [h2]
--       simp [PointedFunctor.eqToHom_point, PGrpd.comp_point, eqToHom_base, eqToHom_map]
--       have hhd := s.condition
--       generalize_proofs at h0

--       have h3 {a : (m ⋙ var' A).obj x ⟶ s.fst.obj x}
--         {b : s.fst.obj y ⟶ (m ⋙ var' A).obj y} : (a ≫ s.fst.map f ≫ b).point =
--         ((s.fst.map f ≫ b).map a.point) ≫ b.map (s.fst.map f).point ≫ b.point := rfl
--       rw [h3]
--       -- rename_i pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 
--       -- have h := comp_point (eqToHom pf3) (s.fst.map f ≫ eqToHom pf4)
       
--       simp [eqToHom_map, PointedFunctor.eqToHom_point,
--         Grothendieck.eqToHom_fiber, CastFunc,Cat.equivOfIso, map_comp, comp_fiber, Category.assoc, CategoryStruct.comp,
--         lift_map_fiber, point']
--       -- simp [CategoryStruct.comp, PCat.comp, comp_point dd (ff ≫ ee)] at h2
--       have hh : ∀{G1 G2 : Grothendieck A}(eq : G1 = G2), A.map (eqToHom eq).base = eqToHom (by congr) := by
--         simp[Grothendieck.eqToHom_base,eqToHom_map]
--       simp [Functor.congr_hom (hh _), εApp, ε, eqToHom_app]
--       -- have hhh : (εApp y).map (s.fst.map f).point = eqToHom (by congr) := by sorry 

--       sorry
--     · simp only [lift, Cat.of_α, comp_base, eqToHom_base]
--       exact Functor.congr_hom hr f
--   · intro x
--     apply Grothendieck.obj_ext_hEq
--     · unfold lift
--       simp [← Functor.congr_obj hr x, uLiftGrothendieckForget, Cat.uLift]
--     · apply toPCat_obj_fiber_inj
--       have h0 := Functor.congr_obj hl x
--       have h1 := Functor.congr_obj (fac_left.{u,u} s) x
--       simp [congr_arg_heq (λ x : PCat ↦ x.str.pt) (h0.trans h1.symm)]

theorem uniq (s : PullbackCone catPCatForgetPoint (A' A)) (m : s.pt ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = s.fst) (hr : m ⋙ Grothendieck.forget A = s.snd ⋙ downFunctor) :
    m = lift s := by
  apply Functor.ext
  · intro x y f
    apply Grothendieck.ext
    · have h0 := Functor.congr_hom hl f
      have h2 := PointedFunctor.congr_point h0
      have h4 := PointedFunctor.congr_func h0
      simp [toPCat] at h2 h4
      simp only [comp_base, comp_fiber, ← Functor.comp_map]
      -- generalize_proofs
      -- rename_i p1 p2 p3 p4 p5
      -- have h := Functor.map_comp A ((lift s).map f).base (eqToHom p2).base
      -- have dshf : (A.map (((lift s).map f).base ≫ (eqToHom p2).base)).map (eqToHom p1).fiber =
      --   _ := Functor.congr_hom h (eqToHom p1).fiber
      -- rw [dshf]
      -- simp [eqToHom_fiber]
      congr 1
      · congr 1
        · dsimp [lift, lift_map]
          have h := Functor.congr_obj hr x
          dsimp only [comp_obj, forget_obj, downFunctor_obj] at h
          rw [h]
        · 
          
          sorry
        · sorry
        · sorry
      · refine heq_of_cast_eq ?_ ?_
        · simp
          sorry
        · congr 1
          · sorry
          · sorry
          · sorry
        -- rw [h4]
      -- have h2 := congr_arg Functor.map h

      -- rw [h]
      -- have h5 : A.map (((lift s).map f).base ≫ (eqToHom p2).base) = _ := congr_arg (λ F ↦ F ≫ (eqToHom p2).base) h4
      -- rw [h2, h3, h4]
      -- convert_to _ =
      --   eqToHom _ ≫ (A.map (((lift s).map f).base ≫ (eqToHom _).base)).map (eqToHom _).fiber ≫
      --   _
      

      sorry
    · sorry
    -- · simp only [comp_base, eqToHom_base, Functor.congr_hom hr f]
      -- exact (Functor.congr_hom hr f).symm
  · intro x
    apply Grothendieck.obj_ext_hEq
    · exact Functor.congr_obj hr x
    · apply toPCat_obj_fiber_inj
      have h0 := Functor.congr_obj hl x
      have h1 := Functor.congr_obj (fac_left.{u} s) x
      simp [congr_arg_heq (λ x : PCat ↦ x.str.pt) (h0.trans h1.symm)]

theorem uniq' (s : PullbackCone catPCatForgetPoint (A' A)) (m : s.pt ⟶ uLiftGrothendieck A)
    (hl : m ≫ var' A = s.fst) (hr : m ≫ uLiftGrothendieckForget A = s.snd) :
    m = lift' s := by
  unfold lift'
  rw [← uniq s (m ⋙ downFunctor) hl
    (by simp [← hr, uLiftGrothendieckForget, Functor.assoc, Cat.comp_eq_comp, Cat.uLift, Functor.comp_id])]
  aesop_cat

variable (A)

def isLimit : IsLimit (cone A) :=
  IsLimit.mk comm_sq lift' fac_left.{u} fac_right.{u,u} uniq'.{u}

theorem is_pullback :
    IsPullback (var' A) (uLiftGrothendieckForget A)
    (PCat.forgetPoint) (A' A) := 
    IsPullback.of_isLimit (isLimit A)

end Grothendieck

end CategoryTheory
