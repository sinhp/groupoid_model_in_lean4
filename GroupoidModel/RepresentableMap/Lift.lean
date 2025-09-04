import GroupoidModel.RepresentableMap.Universe
import GroupoidModel.ForMathlib
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import GroupoidModel.ForPoly

/-! Morphisms of natural models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory MorphismProperty.Universe

namespace MorphismProperty
namespace Universe

variable {Ctx : Type u} [Category.{v} Ctx] [HasFiniteLimits Ctx]
  {CwR : MorphismProperty Ctx} [CwR.RepresentableMap]

macro "by>" s:tacticSeq : term => `(by as_aux_lemma => $s)

structure Hom (M N : CwR.Universe) where
  mapTm : M.Tm ⟶ N.Tm
  mapTy : M.Ty ⟶ N.Ty
  pb : IsPullback M.tp mapTm mapTy N.tp

def Hom.id (M : CwR.Universe) : Hom M M where
  mapTm := 𝟙 _
  mapTy := 𝟙 _
  pb := IsPullback.of_id_snd

def Hom.comp {M N O : CwR.Universe} (α : Hom M N) (β : Hom N O) : Hom M O where
  mapTm := α.mapTm ≫ β.mapTm
  mapTy := α.mapTy ≫ β.mapTy
  pb := α.pb.paste_vert β.pb

def Hom.comp_assoc {M N O P : CwR.Universe} (α : Hom M N) (β : Hom N O) (γ : Hom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp]

/-- Morphism into the representable natural transformation `M`
from the pullback of `M` along a type. -/
protected def pullbackHom (M : CwR.Universe) {Γ : Ctx} (A : Γ ⟶ M.Ty) :
    Hom (M.pullback A) M where
  mapTm := M.var A
  mapTy := A
  pb := M.disp_pullback A

/-- Given `M : NaturalModel`, a semantic type `A : Γ ⟶ M.Ty`,
and a substitution `σ : Δ ⟶ Γ`, construct a Hom for the substitution `A[σ]`.
-/
def Hom.subst (M : CwR.Universe)
    {Γ Δ : Ctx} (A : Γ ⟶ M.Ty) (σ : Δ ⟶ Γ) :
    Hom (M.pullback (σ ≫ A)) (M.pullback A) :=
  let Aσ := σ ≫ A
  { mapTm :=
    (M.disp_pullback A).lift (M.disp Aσ ≫ σ) (M.var Aσ) (by aesop_cat)
    mapTy := σ
    pb := IsPullback.of_bot' (M.disp_pullback Aσ) (M.disp_pullback A)}

def Hom.cartesianNatTrans {M N : CwR.Universe} (h : Hom M N) :
    M.Ptp ⟶ N.Ptp :=
  M.uvPolyTp.cartesianNatTrans N.uvPolyTp h.mapTy h.mapTm h.pb

@[simp] def Hom.extIsoExt {M N : CwR.Universe} (h : Hom M N)
    {Γ} (A : Γ ⟶ M.Ty) : N.ext (A ≫ h.mapTy) ≅ M.ext A :=
  IsPullback.isoIsPullback Γ N.Tm (N.disp_pullback (A ≫ h.mapTy))
  (IsPullback.paste_vert (M.disp_pullback A) h.pb)

@[reassoc]
theorem Hom.mk_comp_cartesianNatTrans {M N : CwR.Universe} (h : Hom M N)
    {Γ X} (A : Γ ⟶ M.Ty) (B : M.ext A ⟶ X) :
    PtpEquiv.mk M A B ≫ h.cartesianNatTrans.app X =
    PtpEquiv.mk N (A ≫ h.mapTy) ((h.extIsoExt A).hom ≫ B) := by
  simp [PtpEquiv.mk]
  have := UvPoly.Equiv.mk'_comp_cartesianNatTrans_app M.uvPolyTp (P' := N.uvPolyTp)
    A _ _ _ (M.disp_pullback _) B h.mapTm h.mapTy h.pb
  refine this.trans ?_
  simp [UvPoly.Equiv.mk']; congr 1
  rw [← Category.assoc]; congr 1
  generalize_proofs _ h1
  apply h1.hom_ext <;> simp

/- We have a 'nice', specific terminal object in `Ctx`,
and this instance allows use to use it directly
rather than through an isomorphism with `Limits.terminal`.
`ChosenTerminal` would suffice but is not defined in mathlib,
so we use `ChosenFiniteProducts`. -/
variable [CartesianMonoidalCategory Ctx]

/-- A Russell universe embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `Lift.id M` would essentially be `Type : Type` in `M`.

Note this doesn't need to extend `Hom` as none of its fields are used;
it's just convenient to pack up the data. -/
structure Lift (M N : CwR.Universe) extends Hom M N where
  U : 𝟙_ Ctx ⟶ N.Ty
  asTm : M.Ty ⟶ N.Tm
  U_pb : IsPullback ((IsTerminal.ofUnique (𝟙_ Ctx)).from M.Ty) asTm U N.tp

def Lift.ofTyIsoExt
    {M N : CwR.Universe}
    (H : Hom M N) {U : 𝟙_ Ctx ⟶ N.Ty} (i : M.Ty ≅ N.ext U) :
    Lift M N where
  __ := H
  U := U
  asTm := i.hom ≫ N.var U
  U_pb := by
    convert IsPullback.of_iso_isPullback (N.disp_pullback _) i
    apply (IsTerminal.ofUnique (𝟙_ Ctx)).hom_ext

def Lift.comp {M N O : CwR.Universe} (α : Lift M N) (β : Lift N O) : Lift M O where
  __ := Hom.comp α.toHom β.toHom
  U := α.U ≫ β.mapTy
  asTm := α.asTm ≫ β.mapTm
  U_pb := α.U_pb.paste_vert β.pb

def Lift.comp_assoc {M N O P : CwR.Universe} (α : Lift M N) (β : Lift N O) (γ : Lift O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def Lift.wkU {M N : CwR.Universe} (Γ : Ctx) (α : Lift M N) : Γ ⟶ N.Ty :=
  (IsTerminal.ofUnique (𝟙_ Ctx)).from Γ ≫ α.U

@[reassoc (attr := simp)]
theorem Lift.comp_wkU {M N : CwR.Universe} {Δ Γ : Ctx} (α : Lift M N) (f : Δ ⟶ Γ) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `Lift` into a natural model with a Tarski universe. -/
def Lift.ofTarskiU (M : CwR.Universe) (U : 𝟙_ Ctx ⟶ M.Ty) (El : M.ext U ⟶ M.Ty) :
    Lift (M.pullback El) M where
  __ := Universe.pullbackHom M El
  U
  asTm := M.var U
  U_pb := (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      ((IsTerminal.ofUnique (𝟙_ Ctx)).hom_ext ..)
      (by simp) (by simp) (by simp)

/-! ## Universe embeddings -/

variable (CwR) in
/-- A sequence of Russell universe embeddings. -/
structure LiftSeq [CartesianMonoidalCategory Ctx] where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs (i : Nat) (h : i < length + 1) : CwR.Universe
  homSucc' (i : Nat) (h : i < length) : Lift (objs i <| by omega) (objs (i + 1) <| by omega)

namespace LiftSeq

variable (s : LiftSeq CwR)

instance : GetElem (LiftSeq CwR) Nat (CwR.Universe) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs i h

def homSucc (i : Nat) (h : i < s.length := by get_elem_tactic) : Lift s[i] s[i+1] :=
  s.homSucc' i h

/-- Composition of embeddings between `i` and `j` in the chain. -/
def hom (s : LiftSeq CwR) (i j : Nat) (ij : i < j := by omega)
    (jlen : j < s.length + 1 := by get_elem_tactic) : Lift s[i] s[j] :=
  if h : i + 1 = j then
    h ▸ s.homSucc i
  else
    (s.homSucc i).comp <| s.hom (i+1) j
termination_by s.length - i

/- It is useful to be able to talk about the underlying sequence of Homs in a LiftSeq.
  For such a sequence, we can loosen the condition i < j to i <= j
  without creating Type in Type.
  This is helpful for defining `s[i] → s[max i j]` for Pi and Sigma below.
-/
def homOfLe (i j : Nat) (ij : i <= j := by omega)
    (jlen : j < s.length + 1 := by get_elem_tactic) : Hom s[i] s[j] :=
  if h : i = j then h ▸ Hom.id s[i]
  else
    (s.hom i j (by omega) _).toHom

/-- For `i ≤ j` and a term `t` at level `j`,
if the type of `t` is lifted from level `i`,
then `t` is a lift of a term at level `i`. -/
def unlift (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : Γ ⟶ (s[i]'(ij.trans_lt jlen)).Ty) (t : Γ ⟶ s[j].Tm)
    (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    Γ ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  (s.homOfLe i j).pb.lift A t eq.symm

@[simp]
theorem unlift_tp {i j ij jlen Γ A}
    {t : Γ ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s[i]'(ij.trans_lt jlen)).tp = A := by
  simp [unlift]

@[simp]
theorem unlift_lift {i j ij jlen Γ A}
    {t : Γ ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s.homOfLe i j).mapTm = t := by
  simp [unlift]

def unliftVar (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : Γ ⟶ (s[i]'(ij.trans_lt jlen)).Ty)
    {A' : Γ ⟶ s[j].Ty} (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    (s[j].ext A') ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  s.unlift i j ij jlen (s[j].disp _ ≫ A) (s[j].var _) (by simp [eq])

@[simp]
theorem unliftVar_tp {i j ij jlen Γ A} {A' : Γ ⟶ s[j].Ty}
    (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    s.unliftVar i j ij jlen A eq ≫ (s[i]'(ij.trans_lt jlen)).tp = s[j].disp _ ≫ A := by
  simp [unliftVar]

-- theorem substCons_unliftVar {i j ij jlen Γ A} {A' : Γ ⟶ s[j].Ty}
--     {eq : A ≫ (s.homOfLe i j).mapTy = A'}
--     {Δ} {σ : Δ ⟶ Γ} {t : Δ ⟶ s[i].Tm}
--     (t_tp : t ≫ (s[i]'(ij.trans_lt jlen)).tp = σ ≫ A) :
--     (s[j].substCons σ A' (t ≫ (s.homOfLe i j ij jlen).mapTm) (by
--       simp [*]
--       -- conv_lhs => rhs; apply (s.homOfLe i j).pb.w
--       -- subst A'; rw [← Category.assoc, ← Category.assoc, ← t_tp])
--       sorry
--       ))
--     ≫ s.unliftVar i j ij jlen A eq = t := by
--   simp [unlift, unliftVar]; apply (s.homOfLe i j).pb.hom_ext <;> simp [*]

/--
If `s` is a sequence of universe homomorphisms then for `i ≤ j` we get a polynomial endofunctor
natural transformation `s[i].Ptp ⟶ s[j].Ptp`.
-/
def cartesianNatTrans (i j : Nat)
    (ij : i ≤ j := by get_elem_tactic) (jlen : j < s.length + 1 := by get_elem_tactic) :
    s[i].Ptp ⟶ s[j].Ptp :=
  (s.homOfLe i j).cartesianNatTrans

@[reassoc]
theorem mk_comp_cartesianNatTrans {i j} (ij : i ≤ j := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ X} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ X) :
    PtpEquiv.mk s[i] A B ≫ (s.cartesianNatTrans i j).app X =
    PtpEquiv.mk s[j] (A ≫ (s.homOfLe i j).mapTy)
    ((substCons _ _ (s[j].disp _) (s.unliftVar i j ij jlen A rfl) (by simp)) ≫ B) := by
  convert Hom.mk_comp_cartesianNatTrans _ _ _
  apply (IsPullback.paste_vert (s[i].disp_pullback _) (s.homOfLe i j).pb).hom_ext
  · simp
  · simp [unliftVar]

theorem cartesianNatTrans_fstProj {i j ij jlen X} :
    (s.cartesianNatTrans i j ij jlen).app X ≫ s[j].uvPolyTp.fstProj X =
    s[i].uvPolyTp.fstProj X ≫ (s.homOfLe i j ij jlen).mapTy := by
  unfold cartesianNatTrans
  apply UvPoly.cartesianNatTrans_fstProj

/--
This is one side of the commutative square
```
s[i0].Ptp.obj s[j0].Tm ⟶ s[i1].Ptp.obj s[j1].Tm
  |                           |
  |                           |
  |                           |
  |                           |
  V                           V
s[i0].Ptp.obj s[j0].Tm ⟶ s[i1].Ptp.obj s[j0].Tm
```
Given `i0 ≤ i1` and `j0 ≤ j1`
-/
@[reducible]
def cartesianNatTransTm (i0 i1 j0 j1 : Nat)
    (ii : i0 ≤ i1 := by get_elem_tactic) (ilen : i1 < s.length + 1 := by get_elem_tactic)
    (jj : j0 ≤ j1 := by get_elem_tactic) (jlen : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Tm ⟶ s[i1].Ptp.obj s[j1].Tm :=
  (s.cartesianNatTrans i0 i1).app s[j0].Tm ≫
  s[i1].Ptp.map (s.homOfLe j0 j1).mapTm

theorem mk_comp_cartesianNatTransTm {i0 i1 j0 j1 ii ilen jj jlen}
    {Γ X} (A : Γ ⟶ s[i0].Ty) (B : (s[i0].ext A) ⟶ s[j0].Tm)
    : PtpEquiv.mk s[i0] A B ≫ s.cartesianNatTransTm i0 i1 j0 j1 ii ilen jj jlen =
      PtpEquiv.mk s[i1] (A ≫ (s.homOfLe i0 i1).mapTy)
        ((substCons _ _ (s[i1].disp _) (s.unliftVar i0 i1 ii ilen A rfl) (by simp))
          ≫ B ≫ (s.homOfLe j0 j1).mapTm) := by
  simp [cartesianNatTransTm, mk_comp_cartesianNatTrans_assoc, PtpEquiv.mk_map]

theorem cartesianNatTransTm_fstProj {i0 i1 j0 j1 ii ilen jj jlen} :
    s.cartesianNatTransTm i0 i1 j0 j1 ii ilen jj jlen ≫ s[i1].uvPolyTp.fstProj s[j1].Tm =
    s[i0].uvPolyTp.fstProj s[j0].Tm ≫ (s.homOfLe i0 i1).mapTy := by
  simp [cartesianNatTransTm]
  slice_lhs 2 3 => apply UvPoly.map_fstProj
  apply cartesianNatTrans_fstProj

@[reducible]
def cartesianNatTransTy (i0 i1 j0 j1 : Nat)
    (i0len : i0 ≤ i1 := by get_elem_tactic) (i1len : i1 < s.length + 1 := by get_elem_tactic)
    (j0len : j0 ≤ j1 := by get_elem_tactic) (j1len : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Ty ⟶ s[i1].Ptp.obj s[j1].Ty :=
  (s.cartesianNatTrans i0 i1).app s[j0].Ty ≫
  s[i1].Ptp.map (s.homOfLe j0 j1).mapTy

theorem mk_comp_cartesianNatTransTy {i0 i1 j0 j1 ii ilen jj jlen}
    {Γ X} (A : Γ ⟶ s[i0].Ty) (B : (s[i0].ext A) ⟶ s[j0].Ty)
    : PtpEquiv.mk s[i0] A B ≫ s.cartesianNatTransTy i0 i1 j0 j1 ii ilen jj jlen =
      PtpEquiv.mk s[i1] (A ≫ (s.homOfLe i0 i1).mapTy)
        ((substCons _ _ (s[i1].disp _) (s.unliftVar i0 i1 ii ilen A rfl) (by simp))
          ≫ B ≫ (s.homOfLe j0 j1).mapTy) := by
  simp [cartesianNatTransTy, mk_comp_cartesianNatTrans_assoc, PtpEquiv.mk_map]

theorem cartesianNatTransTy_fstProj {i0 i1 j0 j1 ii ilen jj jlen} :
    s.cartesianNatTransTy i0 i1 j0 j1 ii ilen jj jlen ≫ s[i1].uvPolyTp.fstProj s[j1].Ty =
    s[i0].uvPolyTp.fstProj s[j0].Ty ≫ (s.homOfLe i0 i1).mapTy := by
  simp only [cartesianNatTransTy]
  slice_lhs 2 3 => apply UvPoly.map_fstProj
  apply cartesianNatTrans_fstProj

theorem hom_comp_trans (s : LiftSeq CwR) (i j k : Nat) (ij : i < j) (jk : j < k)
    (klen : k < s.length + 1) :
    (s.hom i j ij).comp (s.hom j k jk) = s.hom i k (ij.trans jk) := by
  conv_rhs => unfold hom
  conv in s.hom i j _ => unfold hom
  split_ifs
  all_goals try omega
  . rename_i h _
    cases h
    simp
  . rw [Lift.comp_assoc, hom_comp_trans]
termination_by s.length - i

/--
TODO: Consider generalising to just Lift?
Convert a map into the `i`th type classifier into a a term of the
`i+1`th term classifier, that is a term of the `i`th universe.
It is defined by composition with the first projection of the pullback square
               v
     s[i].Ty ----> s[i+1].Tm
     ^    |          |
  A /     |   p.b.   |
   /      |          |
  /       V          V
Γ ---> 1 -----> s[i+1].Ty
              U_i
-/
def code {Γ : Ctx} {i : Nat} (s : LiftSeq CwR) (ilen : i < s.length) (A : Γ ⟶ s[i].Ty) :
    Γ ⟶ s[i+1].Tm :=
  A ≫ (s.homSucc i).asTm

@[simp]
theorem code_tp {Γ : Ctx} {i : Nat} (s : LiftSeq CwR) (ilen : i < s.length) (A : Γ ⟶ s[i].Ty) :
    s.code ilen A ≫ s[i+1].tp = (s.homSucc i).wkU Γ := by
  simp [code, ← (s.homSucc i).U_pb.w, Lift.wkU]

@[reassoc]
theorem comp_code {Δ Γ : Ctx} {i : Nat} (s : LiftSeq CwR) (ilen : i < s.length)
    (σ : (Δ) ⟶ Γ) (A : Γ ⟶ s[i].Ty) :
    σ ≫ s.code ilen A = s.code ilen (σ ≫ A) := by
  simp [code]

/--
TODO: Consider generalising to just Lift?
Convert a a term of the `i`th universe (it is a `i+1` level term) into
a map into the `i`th type classifier.
It is the unique map into the pullback
             a
Γ -----------------¬
‖  -->          v     V
‖    s[i].Ty ----> s[i+1].Tm
‖         |          |
‖         |   p.b.   |
‖         |          |
‖         V          V
Γ ---> 1 -----> s[i+1].Ty
              U_i
-/
def el (s : LiftSeq CwR) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : Γ ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    Γ ⟶ s[i].Ty :=
  (s.homSucc i).U_pb.lift ((IsTerminal.ofUnique (𝟙_ Ctx)).from Γ) a (by rw [a_tp, Lift.wkU])

@[reassoc]
theorem comp_el (s : LiftSeq CwR) {Δ Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (σ : (Δ) ⟶ Γ) (a : Γ ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    σ ≫ s.el ilen a a_tp = s.el ilen (σ ≫ a) (by simp [a_tp]) :=
  (s.homSucc i).U_pb.hom_ext (by simp) (by simp [el])

@[simp]
lemma el_code {Γ : Ctx} {i : Nat} (s : LiftSeq CwR) (ilen : i < s.length) (A : Γ ⟶ s[i].Ty) :
    el s ilen (code s ilen A) (code_tp _ _ _) = A :=
  (s.homSucc i).U_pb.hom_ext (by simp) (by simp [el, code])

@[simp]
lemma code_el (s : LiftSeq CwR) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : Γ ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    code s ilen (el s ilen a a_tp) = a := by
  simp [code, el]

-- Sadly, we have to spell out `ilen` and `jlen` due to
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
variable {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)

/-! ## Pi -/

/-- The data of `Pi` and `lam` formers at each universe `s[i].tp`.

This data is universe-monomorphic,
but we can use it to construct universe-polymorphic formation
in a model-independent manner.
For example, universe-monomorphic `Pi`
```
Γ ⊢ᵢ A type  Γ.A ⊢ᵢ B type
--------------------------
Γ ⊢ᵢ ΠA. B type
```
can be extended to
```
Γ ⊢ᵢ A type  Γ.A ⊢ⱼ B type
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B type
``` -/
protected class PiSeq (s : LiftSeq CwR) where
  nmPi (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
  MorphismProperty.Universe.Pi s[i]

section Pi
open PiSeq

variable [s.PiSeq]

def Pi : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  s.cartesianNatTransTy i (max i j) j (max i j) ≫ (nmPi (max i j)).Pi

def lam : s[i].Ptp.obj s[j].Tm ⟶ s[max i j].Tm :=
  s.cartesianNatTransTm i (max i j) j (max i j) ≫ (nmPi (max i j)).lam

def Pi_pb :
    IsPullback (s[i].Ptp.map s[j].tp) (s.lam ilen jlen) (s.Pi ilen jlen) s[max i j].tp := by
  have p1 : NatTrans.IsCartesian (s.cartesianNatTrans i (max i j)) := by
   dsimp only [LiftSeq.cartesianNatTrans]
   apply UvPoly.isCartesian_cartesianNatTrans
  let pbB : IsPullback
      (s[max i j].Ptp.map s[j].tp)
      (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTm)
      (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTy)
      (s[max i j].Ptp.map s[max i j].tp) :=
    CategoryTheory.UvPoly.preservesPullbacks s[max i j].uvPolyTp _ _ _ _
    (s.homOfLe j (max i j)).pb
  have q := IsPullback.paste_vert pbB (nmPi (max i j)).Pi_pullback
  convert CategoryTheory.IsPullback.paste_vert (p1 s[j].tp) q
  · simp [lam]
  · simp [Pi]

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B
``` -/
def mkPi {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty) : Γ ⟶ s[max i j].Ty :=
  PtpEquiv.mk s[i] A B ≫ s.Pi ilen jlen

theorem comp_mkPi {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (σA) (eq : σ ≫ A = σA)
    (B : (s[i].ext A) ⟶ s[j].Ty) :
    σ ≫ s.mkPi ilen jlen A B = s.mkPi ilen jlen σA ((s[i].substWk A σ _ eq) ≫ B) := by
  simp [mkPi, ← Category.assoc, PtpEquiv.mk_comp_left (eq := eq)]

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ t : B
-------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. t : ΠA. B
``` -/
def mkLam {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (t : (s[i].ext A) ⟶ s[j].Tm) : Γ ⟶ s[max i j].Tm :=
  PtpEquiv.mk s[i] A t ≫ s.lam ilen jlen

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : (s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B) :
    s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B := by
  simp [mkLam, mkPi, ← (s.Pi_pb ilen jlen).w, PtpEquiv.mk_map_assoc, t_tp]

theorem comp_mkLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (σA) (eq : σ ≫ A = σA) (t : (s[i].ext A) ⟶ s[j].Tm) :
    σ ≫ s.mkLam ilen jlen A t = s.mkLam ilen jlen σA ((s[i].substWk A σ _ eq) ≫ t) := by
  simp [mkLam, ← Category.assoc, PtpEquiv.mk_comp_left (eq := eq)]


/--
```
Γ ⊢ᵢ A  Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B
-----------------------------
Γ.A ⊢ⱼ unlam f : B
``` -/
def unLam {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    (s[i].ext A) ⟶ s[j].Tm := by
  let total : Γ ⟶ s[i].Ptp.obj s[j].Tm :=
    (s.Pi_pb ilen jlen).lift (PtpEquiv.mk s[i] A B) f f_tp.symm
  refine PtpEquiv.snd s[i] total _ ?_
  have eq : total ≫ s[i].Ptp.map s[j].tp = PtpEquiv.mk s[i] A B :=
    (s.Pi_pb ilen jlen).lift_fst ..
  apply_fun PtpEquiv.fst s[i] at eq
  rw [PtpEquiv.fst_comp_right] at eq
  simpa using eq

@[simp]
theorem unLam_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B f f_tp ≫ s[j].tp = B := by
  rw [unLam, ← PtpEquiv.snd_comp_right]
  convert PtpEquiv.snd_mk s[i] A B using 2; simp

theorem comp_unLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (σA) (eq : σ ≫ A = σA) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    (s[i].substWk A σ _ eq) ≫ s.unLam ilen jlen A B f f_tp =
      s.unLam ilen jlen σA ((s[i].substWk A σ _ eq) ≫ B)
        (σ ≫ f) (by simp [eq, f_tp, comp_mkPi]) := by
  simp [unLam]
  rw [← PtpEquiv.snd_comp_left]
  simp [PtpEquiv.snd, UvPoly.Equiv.snd'_eq]; congr 1
  apply pullback.hom_ext <;> simp; congr 1
  apply (s.Pi_pb ilen jlen).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_left]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B  Γ ⊢ᵢ a : A
---------------------------------
Γ ⊢ⱼ f a : B[id.a]
``` -/
def mkApp {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : Γ ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) : Γ ⟶ s[j].Tm :=
  (s[i].sec A a a_tp) ≫ s.unLam ilen jlen A B f f_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : Γ ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    s.mkApp ilen jlen A B f f_tp a a_tp ≫ s[j].tp = (s[i].sec A a a_tp) ≫ B := by
  simp [mkApp]

theorem comp_mkApp {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (σA) (eq : σ ≫ A = σA) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : Γ ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    σ ≫ s.mkApp ilen jlen A B f f_tp a a_tp =
      s.mkApp ilen jlen σA ((s[i].substWk A σ _ eq) ≫ B)
        (σ ≫ f) (by simp [f_tp, comp_mkPi (eq := eq)])
        (σ ≫ a) (by simp [a_tp, eq]) := by
  unfold mkApp; rw [← Category.assoc, comp_sec, Category.assoc, comp_unLam]

@[simp]
theorem mkLam_unLam {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.mkLam ilen jlen A (s.unLam ilen jlen A B f f_tp) = f := by
  let total : Γ ⟶ s[i].Ptp.obj s[j].Tm :=
    (s.Pi_pb ilen jlen).lift (PtpEquiv.mk s[i] A B) f f_tp.symm
  simp [mkLam, unLam]
  have : PtpEquiv.fst s[i] total = A := by
    simp [total, PtpEquiv.fst, UvPoly.Equiv.fst]
    rw [← s[i].uvPolyTp.map_fstProj s[j].tp]
    slice_lhs 1 2 => apply (s.Pi_pb ilen jlen).lift_fst
    apply PtpEquiv.fst_mk
  slice_lhs 1 1 => equals total =>
    apply PtpEquiv.ext _ (A := A) (by simp) (by simp [this]) (by simp [total])
  apply (s.Pi_pb ilen jlen).lift_snd

@[simp]
theorem unLam_mkLam {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : (s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B)
    (lam_tp : s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B (s.mkLam ilen jlen A t) lam_tp = t := by
  simp [mkLam, unLam]
  convert PtpEquiv.snd_mk s[i] A t using 2
  apply (s.Pi_pb ilen jlen).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_right, t_tp]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B
--------------------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. f[↑] v₀ : ΠA. B
```
-/
def etaExpand {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    Γ ⟶ s[max i j].Tm :=
  s.mkLam ilen jlen A <|
    s.mkApp ilen jlen
      ((s[i].disp A) ≫ A) ((s[i].substWk ..) ≫ B) ((s[i].disp A) ≫ f)
        (by simp [f_tp, comp_mkPi])
      (s[i].var A) (s[i].var_tp A)

theorem etaExpand_eq {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (f : Γ ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.etaExpand ilen jlen A B f f_tp = f := by
  simp [etaExpand]
  convert s.mkLam_unLam ilen jlen A B f f_tp using 2
  simp [mkApp]; rw [← comp_unLam (f_tp := f_tp), ← Category.assoc]
  conv_rhs => rw [← Category.id_comp (s.unLam ..)]
  congr 2
  apply (s[i].disp_pullback A).hom_ext <;> simp
  simp [substWk]

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ t : B  Γ ⊢ᵢ a : A
--------------------------------
Γ.A ⊢ⱼ (λA. t) a ≡ t[a] : B[a]
``` -/
@[simp]
theorem mkApp_mkLam {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : (s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B)
    (lam_tp : s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : Γ ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    s.mkApp ilen jlen A B (s.mkLam ilen jlen A t) lam_tp a a_tp = (s[i].sec A a a_tp) ≫ t := by
  rw [mkApp, unLam_mkLam]
  assumption

end Pi

/-! ## Sigma -/

/-- The data of `Sig` and `pair` formers at each universe `s[i].tp`. -/
class SigSeq (s : LiftSeq CwR) where
  nmSig (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
  MorphismProperty.Universe.Sigma s[i]

section Sigma
open SigSeq
variable [s.SigSeq]

def Sig : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  s.cartesianNatTransTy i (max i j) j (max i j) ≫ (nmSig (max i j)).Sig

def pair : UvPoly.compDom s[i].uvPolyTp s[j].uvPolyTp ⟶ s[max i j].Tm :=
  let l : s[i].uvPolyTp.compDom s[j].uvPolyTp ⟶ s[max i j].uvPolyTp.compDom s[max i j].uvPolyTp :=
    UvPoly.compDomMap
      (s.homOfLe i (max i j)).mapTm
      (s.homOfLe j (max i j)).mapTm
      (s.homOfLe i (max i j)).mapTy
      (s.homOfLe j (max i j)).mapTy
      (s.homOfLe i (max i j)).pb
      (s.homOfLe j (max i j)).pb
  l ≫ (nmSig (max i j)).pair

def Sig_pb : IsPullback (s[i].uvPolyTp.compP s[j].uvPolyTp) (s.pair ilen jlen)
    (s.Sig ilen jlen) s[max i j].tp :=
  (UvPoly.compDomMap_isPullback ..).paste_vert (nmSig (max i j)).Sig_pullback

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΣA. B
``` -/
def mkSig {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty) :
    Γ ⟶ s[max i j].Ty :=
  PtpEquiv.mk s[i] A B ≫ s.Sig ilen jlen

theorem comp_mkSig {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty) :
    σ ≫ s.mkSig ilen jlen A B =
      s.mkSig ilen jlen (σ ≫ A) ((s[i].substWk A σ) ≫ B) := by
  simp [mkSig, ← Category.assoc, PtpEquiv.mk_comp_left]

/--
```
Γ ⊢ᵢ t : A  Γ ⊢ⱼ u : B[t]
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ⟨t, u⟩ : ΣA. B
``` -/
def mkPair {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : Γ ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = (s[i].sec A t t_tp) ≫ B) :
    Γ ⟶ s[max i j].Tm :=
  compDomEquiv.mk t t_tp B u u_tp ≫ s.pair ilen jlen

theorem comp_mkPair {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : Γ ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = (s[i].sec A t t_tp) ≫ B) :
    σ ≫ s.mkPair ilen jlen A B t t_tp u u_tp =
      s.mkPair ilen jlen (σ ≫ A) ((s[i].substWk A σ) ≫ B)
        (σ ≫ t) (by simp [t_tp])
        (σ ≫ u) (by simp [u_tp, comp_sec_assoc]) := by
  simp only [← Category.assoc, mkPair]; rw [compDomEquiv.comp_mk]

@[simp]
theorem mkPair_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : Γ ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = (s[i].sec A t t_tp) ≫ B) :
    s.mkPair ilen jlen A B t t_tp u u_tp ≫ s[max i j].tp = s.mkSig ilen jlen A B := by
  simp [mkPair, mkSig, ← (s.Sig_pb ilen jlen).w, compDomEquiv.mk,
    UvPoly.compDomEquiv.mk, UvPoly.compP, PtpEquiv.mk, t_tp]

section

variable {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (p : Γ ⟶ s[max i j].Tm) (p_tp : s.mkSig ilen jlen A B = p ≫ s[max i j].tp)

def mkFst : Γ ⟶ s[i].Tm := compDomEquiv.fst ((s.Sig_pb ilen jlen).lift (PtpEquiv.mk _ A B) p p_tp)

@[simp]
theorem mkFst_tp : s.mkFst ilen jlen A B p p_tp ≫ s[i].tp = A := by
  simp [mkFst, UvPoly.compP, compDomEquiv.fst_tp]

theorem comp_mkFst : σ ≫ s.mkFst ilen jlen A B p p_tp = s.mkFst ilen jlen (σ ≫ A)
    ((s[i].substWk A σ) ≫ B) (σ ≫ p) (by simp [← p_tp, comp_mkSig]) := by
  simp only [mkFst, compDomEquiv.comp_fst]
  congr 1
  apply (s.Sig_pb ilen jlen).hom_ext <;> simp [PtpEquiv.mk_comp_left]

def mkSnd : Γ ⟶ s[j].Tm :=
  compDomEquiv.snd ((s.Sig_pb ilen jlen).lift (PtpEquiv.mk _ A B) p p_tp)

protected theorem dependent_eq :
    compDomEquiv.dependent ((s.Sig_pb ilen jlen).lift (PtpEquiv.mk s[i] A B) p p_tp) A
    (by simp [compDomEquiv.fst_tp]) = B := by
  simp only [compDomEquiv.dependent, UvPoly.compDomEquiv.dependent]
  convert PtpEquiv.snd_mk s[i] A B using 2
  simp
  sorry

@[simp]
theorem mkSnd_tp : s.mkSnd ilen jlen A B p p_tp ≫ s[j].tp =
    (s[i].sec A (s.mkFst ilen jlen A B p p_tp) (by simp)) ≫ B := by
  generalize_proofs h
  simp [mkSnd, compDomEquiv.snd_tp (eq := h), s.dependent_eq _ _ _ _ _ p_tp]; rfl

theorem comp_mkSnd : σ ≫ s.mkSnd ilen jlen A B p p_tp = s.mkSnd ilen jlen (σ ≫ A)
    ((s[i].substWk A σ) ≫ B) (σ ≫ p) (by simp [← p_tp, comp_mkSig]) := by
  simp [mkSnd, compDomEquiv.comp_snd]; congr 1
  apply (s.Sig_pb ilen jlen).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_left]

@[simp]
theorem mkPair_mkFst_mkSnd :
    s.mkPair ilen jlen A B
      (s.mkFst ilen jlen A B p p_tp) (by simp)
      (s.mkSnd ilen jlen A B p p_tp) (by simp) = p := by
  simp [mkFst, mkSnd, mkPair]
  have := compDomEquiv.eta ((s.Sig_pb ilen jlen).lift (PtpEquiv.mk _ A B) p p_tp)
    (eq := by rw [← mkFst.eq_def, mkFst_tp])
  conv at this => enter [1, 3]; apply s.dependent_eq _ _ _ _ _ p_tp
  simp [this]

end

@[simp]
theorem mkFst_mkPair {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : Γ ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = (s[i].sec A t t_tp) ≫ B) :
    s.mkFst ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = t := by
  simp [mkFst, mkPair]
  convert compDomEquiv.fst_mk t t_tp B u u_tp using 2
  apply (s.Sig_pb ilen jlen).hom_ext <;> simp; simp [compDomEquiv.mk, UvPoly.compP]
  sorry

@[simp]
theorem mkSnd_mkPair {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (B : (s[i].ext A) ⟶ s[j].Ty)
    (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : Γ ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = (s[i].sec A t t_tp) ≫ B) :
    s.mkSnd ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = u := by
  simp [mkSnd, mkPair]
  convert compDomEquiv.snd_mk t t_tp B u u_tp using 2
  apply (s.Sig_pb ilen jlen).hom_ext <;> simp; simp [compDomEquiv.mk, UvPoly.compP]
  sorry

end Sigma

-- /-! ## Identity types -/

-- class IdSeq (s : LiftSeq CwR) where
--   nmII (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) : RepMap.Universe.IdIntro s[i]
--   nmId (i j : Nat) (ilen : i < s.length + 1 := by get_elem_tactic)
--     (jlen : j < s.length + 1 := by get_elem_tactic) : NaturalModel.Id s[i] s[j] (nmII i ilen)

-- section Id
-- open IdSeq
-- variable [s.IdSeq]

-- /--
-- ```
-- Γ ⊢ᵢ A  Γ ⊢ᵢ a0, a1 : A
-- -----------------------
-- Γ ⊢ᵢ Id(A, a0, a1)
-- ``` -/
-- def mkId {Γ : Ctx} (A : Γ ⟶ s[i].Ty) (a0 a1 : Γ ⟶ s[i].Tm)
--     (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
--     Γ ⟶ s[i].Ty :=
--   (nmII i).mkId a0 a1 (a1_tp ▸ a0_tp)

-- theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
--     (A : Γ ⟶ s[i].Ty) (σA) (eq : σ ≫ A = σA)
--     (a0 a1 : Γ ⟶ s[i].Tm)
--     (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
--     σ ≫ s.mkId ilen A a0 a1 a0_tp a1_tp =
--       s.mkId ilen σA (σ ≫ a0) (σ ≫ a1)
--         (by simp [eq, a0_tp]) (by simp [eq, a1_tp]) := by
--   simp [mkId, IdIntro.mkId]
--   rw [← Category.assoc]; congr 1
--   apply (nmII i).isKernelPair.hom_ext <;> simp

-- /--
-- ```
-- Γ ⊢ᵢ t : A
-- -----------------------
-- Γ ⊢ᵢ refl(t) : Id(A, t, t)
-- ``` -/
-- def mkRefl {Γ : Ctx} (t : Γ ⟶ s[i].Tm) : Γ ⟶ s[i].Tm :=
--   (nmII i).mkRefl t

-- theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
--     (t : Γ ⟶ s[i].Tm) :
--     σ ≫ s.mkRefl ilen t = s.mkRefl ilen (σ ≫ t) := by
--   simp [mkRefl, IdIntro.mkRefl]

-- @[simp]
-- theorem mkRefl_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty)
--     (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A) :
--     s.mkRefl ilen t ≫ s[i].tp = s.mkId ilen A t t t_tp t_tp :=
--   (nmII i).mkRefl_tp t

-- /--
-- ```
-- Γ ⊢ᵢ t : A
-- -----------------------
-- Γ ⊢ᵢ idRec(t) : Id(A, t, t)
-- ``` -/
-- def mkIdRec {Γ : Ctx} (A : Γ ⟶ s[i].Ty)
--     (t : Γ ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
--     (B : (s[i].ext A) ⟶ s[i].Ty)
--     (B_eq : s.mkId ilen ((s[i].disp A) ≫ A)
--       ((s[i].disp A) ≫ t) (s[i].var A) (by> simp [*]) (var_tp ..) = B)
--     (M : (s[i].ext B) ⟶ s[j].Ty)
--     (r : Γ ⟶ s[j].Tm) (r_tp : r ≫ s[j].tp =
--       (substCons _ _ (s[i].sec A t t_tp) (s.mkRefl ilen t)
--         (by> simp [comp_mkId, t_tp, ← B_eq])) ≫ M)
--     (u : Γ ⟶ s[i].Tm) (u_tp : u ≫ s[i].tp = A)
--     (h : Γ ⟶ s[i].Tm) (h_tp : h ≫ s[i].tp = s.mkId ilen A t u t_tp u_tp) :
--     Γ ⟶ s[j].Tm := by
--   refine (nmId i j).mkJ t
--     ((substWk _ r (substWk _ _ (𝟙 _) _ (by simp [t_tp])) _ _ ?_) ≫ M)
--     ?_ u (t_tp ▸ u_tp) h ?_
--   · simp [← B_eq, comp_mkId, ← mkId.eq_def]; congr 1 <;> simp [t_tp, substWk]
--   · simp [r_tp]; rw [← Functor.map_comp_assoc]; congr 1
--     apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.reflSubst, mkRefl, substWk, sec]
--   · simp [h_tp, mkId, IdIntro.mkId]

-- theorem comp_mkIdRec {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
--     (A : Γ ⟶ s[i].Ty) (σA) (σA_eq : σ ≫ A = σA)
--     (t t_tp B B_eq σB) (σB_eq : (s[i].substWk _ σ _ σA_eq) ≫ B = σB)
--     (M) (r : Γ ⟶ (s[j]'jlen).Tm) (r_tp u u_tp h h_tp) :
--     σ ≫ s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp u u_tp h h_tp =
--     s.mkIdRec ilen jlen σA (σ ≫ t) (by> simp [t_tp, ← σA_eq])
--       σB (by>
--         simp [← σB_eq, ← B_eq]
--         rw [comp_mkId]; congr! 1
--         · rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, substWk_disp]
--         · simp
--         · rw [← Functor.map_comp_assoc, substWk_disp]; simp [σA_eq])
--       ((s[i].substWk _ (s[i].substWk σ _ _ σA_eq) _ σB_eq) ≫ M)
--       (σ ≫ r) (by>
--         simp [*]
--         simp only [← Functor.map_comp_assoc]; congr! 2
--         simp [comp_substCons, comp_sec, substWk, comp_mkRefl])
--       (σ ≫ u) (by> simp [*])
--       (σ ≫ h) (by> simp [*, comp_mkId]) := by
--   simp [mkIdRec, Id.mkJ]
--   change let σ' := _; _ = (σ') ≫ _; intro σ'
--   convert congr((σ') ≫ $((nmId i j).comp_j σ t ((_) ≫ M) r _)) using 1; swap
--   case convert_1 =>
--     exact s[i].substWk _ (s[i].substWk _ (𝟙 _) _ (by simp [t_tp])) _ (by
--       simp [← B_eq, comp_mkId, ← mkId.eq_def]
--       congr! 1 <;>
--       · subst t_tp; rw [substWk_disp_functor_map_assoc]; simp)
--   · congr 2; simp only [← Category.assoc]; congr 1
--     apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.motiveSubst]
--     apply (s[i].disp_pullback _).hom_ext <;> simp
--     · simp [substWk_disp_functor_map_assoc]
--     · simp [substWk_disp_functor_map, substWk_disp_functor_map_assoc]
--   · simp [← Category.assoc]; congr 1
--     apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.motiveSubst]
--     · dsimp [Id.endPtSubst, σ']
--       simp only [substCons_var]
--     · rw [substWk_disp_functor_map]
--       apply (s[i].disp_pullback _).hom_ext <;> simp [Id.endPtSubst, σ', substWk_disp_functor_map]
--   · simp [r_tp]
--     simp [← Category.assoc]; congr 1
--     apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.reflSubst]; rfl
--     rw [substWk_disp_functor_map, substCons_disp_functor_map_assoc]
--     apply (s[i].disp_pullback _).hom_ext <;> simp
--     simp [substWk_disp_functor_map]

-- @[simp]
-- theorem mkIdRec_tp {Γ : Ctx} (A : Γ ⟶ s[i].Ty)
--     (t t_tp B B_eq M) (r : Γ ⟶ s[j].Tm) (r_tp u u_tp h h_tp) :
--     s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp u u_tp h h_tp ≫ s[j].tp =
--       (substCons _ _ (s[i].sec _ u u_tp) h (by> simp [h_tp, comp_mkId, ← B_eq])) ≫ M := by
--   simp [mkIdRec, Id.mkJ_tp]; rw [← Functor.map_comp_assoc]; congr 1
--   apply (s[i].disp_pullback _).hom_ext <;> simp [Id.endPtSubst, sec, substWk]

-- @[simp]
-- theorem mkIdRec_mkRefl {Γ : Ctx} (A : Γ ⟶ s[i].Ty)
--     (t t_tp B B_eq M) (r : Γ ⟶ s[j].Tm) (r_tp) :
--     s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp t t_tp
--       (s.mkRefl ilen t) (s.mkRefl_tp ilen _ t t_tp) = r := by
--   simp [mkIdRec, mkRefl, Id.mkJ_refl]

-- end Id

end LiftSeq
end Universe
end MorphismProperty
