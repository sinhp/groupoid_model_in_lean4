import GroupoidModel.Groupoids.PullBackProofs
universe u v u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

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
    · simp [A.map_comp]; rfl

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

def catULift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := ULift.downFunctor ⋙ f ⋙ ULift.upFunctor

def catULiftGrothendieck : Cat.{u, u+1} :=
  catULift.obj (Cat.of $ Grothendieck A)

def uLiftGrothendieckForget :
  catULiftGrothendieck A ⟶ catULift.obj Γ :=
  catULift.map (Grothendieck.forget A)

def catCat : Cat.{u,u+1} := Cat.of Cat.{u,u}

def catPCat : Cat.{u,u+1} := Cat.of PCat.{u,u}

def catPCatForgetPoint : catPCat ⟶ catCat :=
  PCat.forgetPoint

def var' : catULiftGrothendieck A ⟶ catPCat :=
  ULift.downFunctor ⋙ Grothendieck.toPCat A

def A' : catULift.obj Γ ⟶ catCat :=
  ULift.downFunctor ⋙ A

variable {A}

lemma comm_sq : var' A ≫ PCat.forgetPoint
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

-- abbrev fstStr := (s.fst.obj x).str.toCategory

abbrev conePCatPt {s : PullbackCone catPCatForgetPoint (A' A)}
    (x : s.pt) := (s.fst.obj x).str.pt

-- abbrev s_comm_sq := s.condition

/- This is an explicit natural transformation for the commuting condition for cone s -/
abbrev ε (s : PullbackCone catPCatForgetPoint (A' A))
    : s.fst ≫ catPCatForgetPoint
    ⟶ s.snd ≫ A' A := eqToHom s.condition

abbrev εApp
    {s : PullbackCone catPCatForgetPoint (A' A)} (x : s.pt)
    : (s.fst ≫ catPCatForgetPoint).obj x
    ⟶ (s.snd ≫ A' A).obj x := (ε s).app x

abbrev εNaturality
    {s : PullbackCone catPCatForgetPoint (A' A)} {x y : s.pt}
    (f : x ⟶ y) := (ε s).naturality f

-- abbrev F {s : PullbackCone catPCatForgetPoint (A' A)}
--     {x y : s.pt} (f : x ⟶ y) := (s.fst.map f).toFunctor

abbrev conePCatPoint {s : PullbackCone catPCatForgetPoint (A' A)}
    {x y : s.pt} (f : x ⟶ y) :
    (s.fst.map f).obj (conePCatPt x) ⟶ conePCatPt y :=
  (s.fst.map f).point

-- #check Category.Id

-- lemma d {s : PullbackCone catPCatForgetPoint (A' A)} (x : s.pt) :
--  conePCatPoint (CategoryStruct.id x) = CategoryStruct.id _ := sorry


-- #check Fpoint
-- abbrev pointt := (outerSqEqToHom x).obj (fstPt x)
-- lemma sdfj {s : PullbackCone catPCatForgetPoint (A' A)} {x y : s.pt}
--     (f : x ⟶ y) :
--     (s.fst ≫ catPCatForgetPoint).map f ≫ (ε s).app y
--     = (εApp y).obj ((s.fst.map f).obj PointedCategory.pt) := sorry

def lift' (s : PullbackCone catPCatForgetPoint (A' A)) :
  s.pt ⥤ Grothendieck A where
  obj x := ⟨ (s.snd.obj x).down ,
    (εApp x).obj (conePCatPt x) ⟩
  map {x y} f := ⟨ s.snd.map f ,
    let m1 := (εApp y).map (conePCatPoint f)
    let m2 := (eqToHom (εNaturality f).symm).app (conePCatPt x)
    m2 ≫ m1 ⟩
  map_id x := by
    dsimp [Grothendieck.id]
    apply Grothendieck.ext
    · rw [eqToHom_app (εNaturality (CategoryStruct.id x)).symm]
      have h1 := CategoryTheory.Functor.map_id s.fst x
      have h2 : (PCat.category.id (s.fst.obj x)).point = eqToHom rfl := rfl
      have h3 := CategoryTheory.Functor.map_id (εApp x) ((s.fst.obj x).str).pt
      have h4 {a} (f : a ⟶ _) :
          f ≫ CategoryStruct.id ((εApp x).obj (conePCatPt x)) = f
        := Category.comp_id f
      simp [dcongr_arg PointedFunctor.point h1, eqToHom_map, h2, h3, h4]
    · simp
      rfl
      -- aesop_cat
  map_comp := sorry

lemma PointedFunctor.id.point_eq {C : Type*} [PointedCategory C] :
  (PCat.category.id (PCat.of C)).point = eqToHom rfl := rfl

def lift (s : PullbackCone catPCatForgetPoint (A' A)) :
  s.pt ⟶ catULiftGrothendieck A := by
  dsimp [catULiftGrothendieck]
  
  -- let hd := Cat.Hom
  -- exact lift' s
  sorry

#exit

variable (A)

def isLimit : IsLimit (cone A) :=
  IsLimit.mk comm_sq sorry sorry sorry sorry

theorem is_pullback :
    IsPullback (var' A) (uLiftGrothendieckForget A)
    (PCat.forgetPoint) (A' A) := 
    IsPullback.of_isLimit (isLimit A)

end Grothendieck

end CategoryTheory
