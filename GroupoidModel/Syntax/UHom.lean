import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import GroupoidModel.ForPoly

/-! Morphisms of natural models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory

namespace NaturalModel

variable {Ctx : Type u} [SmallCategory Ctx]

macro "by>" s:tacticSeq : term => `(by as_aux_lemma => $s)

structure Hom (M N : NaturalModel Ctx) where
  mapTm : M.Tm ⟶ N.Tm
  mapTy : M.Ty ⟶ N.Ty
  pb : IsPullback mapTm M.tp N.tp mapTy

def Hom.id (M : NaturalModel Ctx) : Hom M M where
  mapTm := 𝟙 _
  mapTy := 𝟙 _
  pb := IsPullback.of_id_fst

def Hom.comp {M N O : NaturalModel Ctx} (α : Hom M N) (β : Hom N O) : Hom M O where
  mapTm := α.mapTm ≫ β.mapTm
  mapTy := α.mapTy ≫ β.mapTy
  pb := α.pb.paste_horiz β.pb

def Hom.comp_assoc {M N O P : NaturalModel Ctx} (α : Hom M N) (β : Hom N O) (γ : Hom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp]

/-- Morphism into the representable natural transformation `M`
from the pullback of `M` along a type. -/
protected def pullbackHom (M : NaturalModel Ctx) {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
    Hom (M.pullback A) M where
  mapTm := M.var A
  mapTy := A
  pb := M.disp_pullback A

/-- Given `M : NaturalModel`, a semantic type `A : y(Γ) ⟶ M.Ty`,
and a substitution `σ : Δ ⟶ Γ`, construct a Hom for the substitution `A[σ]`.
-/
def Hom.subst (M : NaturalModel Ctx)
    {Γ Δ : Ctx} (A : y(Γ) ⟶ M.Ty) (σ : Δ ⟶ Γ) :
    Hom (M.pullback (ym(σ) ≫ A)) (M.pullback A) :=
  let Aσ := ym(σ) ≫ A
  { mapTm :=
    (M.disp_pullback A).lift (M.var Aσ) ym(M.disp Aσ ≫ σ) (by aesop_cat)
    mapTy := ym(σ)
    pb := by
      convert IsPullback.of_right' (M.disp_pullback Aσ) (M.disp_pullback A)
      simp }

def Hom.cartesianNatTrans {M N : NaturalModel Ctx} (h : Hom M N) :
    M.Ptp ⟶ N.Ptp :=
  M.uvPolyTp.cartesianNatTrans N.uvPolyTp h.mapTy h.mapTm h.pb.flip

@[simp] def Hom.extIsoExt {M N : NaturalModel Ctx} (h : Hom M N)
    {Γ} (A : y(Γ) ⟶ M.Ty) : y(N.ext (A ≫ h.mapTy)) ≅ y(M.ext A) :=
  IsPullback.isoIsPullback N.Tm y(Γ) (N.disp_pullback (A ≫ h.mapTy))
  (IsPullback.paste_horiz (M.disp_pullback A) h.pb)

@[reassoc]
theorem Hom.mk_comp_cartesianNatTrans {M N : NaturalModel Ctx} (h : Hom M N)
    {Γ X} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    PtpEquiv.mk M A B ≫ h.cartesianNatTrans.app X =
    PtpEquiv.mk N (A ≫ h.mapTy) ((h.extIsoExt A).hom ≫ B) := by
  simp [PtpEquiv.mk]
  have := UvPoly.Equiv.mk'_comp_cartesianNatTrans_app M.uvPolyTp (P' := N.uvPolyTp)
    A _ _ _ (M.disp_pullback _).flip B h.mapTm h.mapTy h.pb.flip
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

-- Should be in mathlib?
def isTerminal_yUnit : IsTerminal y(𝟙_ Ctx) :=
  (IsTerminal.ofUnique (𝟙_ Ctx)).isTerminalObj yoneda (𝟙_ Ctx)

/-- A Russell universe embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `UHom.id M` is essentially `Type : Type` in `M`.

Note this doesn't need to extend `Hom` as none of its fields are used;
it's just convenient to pack up the data. -/
structure UHom (M N : NaturalModel Ctx) extends Hom M N where
  U : y(𝟙_ Ctx) ⟶ N.Ty
  asTm : M.Ty ⟶ N.Tm
  U_pb : IsPullback
            /- m.Ty -/           asTm /- N.Tm -/
    (isTerminal_yUnit.from M.Ty)         N.tp
             /- ⊤ -/               U  /- N.Ty -/

def UHom.ofTyIsoExt
    {M N : NaturalModel Ctx}
    (H : Hom M N) {U : y(𝟙_ Ctx) ⟶ N.Ty} (i : M.Ty ≅ y(N.ext U)) :
    UHom M N where
  __ := H
  U := U
  asTm := i.hom ≫ N.var U
  U_pb := by
    convert IsPullback.of_iso_isPullback (N.disp_pullback _) i
    apply isTerminal_yUnit.hom_ext

def UHom.comp {M N O : NaturalModel Ctx} (α : UHom M N) (β : UHom N O) : UHom M O where
  __ := Hom.comp α.toHom β.toHom
  U := α.U ≫ β.mapTy
  asTm := α.asTm ≫ β.mapTm
  U_pb := α.U_pb.paste_horiz β.pb

def UHom.comp_assoc {M N O P : NaturalModel Ctx} (α : UHom M N) (β : UHom N O) (γ : UHom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def UHom.wkU {M N : NaturalModel Ctx} (Γ : Ctx) (α : UHom M N) : y(Γ) ⟶ N.Ty :=
  isTerminal_yUnit.from y(Γ) ≫ α.U

@[reassoc (attr := simp)]
theorem UHom.comp_wkU {M N : NaturalModel Ctx} {Δ Γ : Ctx} (α : UHom M N) (f : y(Δ) ⟶ y(Γ)) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `UHom` into a natural model with a Tarski universe. -/
def UHom.ofTarskiU (M : NaturalModel Ctx) (U : y(𝟙_ Ctx) ⟶ M.Ty) (El : y(M.ext U) ⟶ M.Ty) :
    UHom (M.pullback El) M where
  __ := M.pullbackHom El
  U
  asTm := M.var U
  U_pb := (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (by simp) (isTerminal_yUnit.hom_ext ..)
      (by simp) (by simp)

/-! ## Universe embeddings -/

variable (Ctx) in
/-- A sequence of Russell universe embeddings. -/
structure UHomSeq [CartesianMonoidalCategory Ctx] where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs (i : Nat) (h : i < length + 1) : NaturalModel Ctx
  homSucc' (i : Nat) (h : i < length) : UHom (objs i <| by omega) (objs (i + 1) <| by omega)

namespace UHomSeq

variable (s : UHomSeq Ctx)

instance : GetElem (UHomSeq Ctx) Nat (NaturalModel Ctx) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs i h

def homSucc (i : Nat) (h : i < s.length := by get_elem_tactic) : UHom s[i] s[i+1] :=
  s.homSucc' i h

/-- Composition of embeddings between `i` and `j` in the chain. -/
def hom (s : UHomSeq Ctx) (i j : Nat) (ij : i < j := by omega)
    (jlen : j < s.length + 1 := by get_elem_tactic) : UHom s[i] s[j] :=
  if h : i + 1 = j then
    h ▸ s.homSucc i
  else
    (s.homSucc i).comp <| s.hom (i+1) j
termination_by s.length - i

/- It is useful to be able to talk about the underlying sequence of Homs in a UHomSeq.
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
  (s.homOfLe i j).pb.lift t A eq

@[simp]
theorem unlift_tp {i j ij jlen Γ A}
    {t : y(Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s[i]'(ij.trans_lt jlen)).tp = A := by
  simp [unlift]

@[simp]
theorem unlift_lift {i j ij jlen Γ A}
    {t : y(Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s.homOfLe i j).mapTm = t := by
  simp [unlift]

def unliftVar (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : y(Γ) ⟶ (s[i]'(ij.trans_lt jlen)).Ty)
    {A' : y(Γ) ⟶ s[j].Ty} (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    y(s[j].ext A') ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  s.unlift i j ij jlen (ym(s[j].disp _) ≫ A) (s[j].var _) (by simp [eq])

@[simp]
theorem unliftVar_tp {i j ij jlen Γ A} {A' : y(Γ) ⟶ s[j].Ty}
    (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    s.unliftVar i j ij jlen A eq ≫ (s[i]'(ij.trans_lt jlen)).tp = ym(s[j].disp _) ≫ A := by
  simp [unliftVar]

theorem substCons_unliftVar {i j ij jlen Γ A} {A' : y(Γ) ⟶ s[j].Ty}
    {eq : A ≫ (s.homOfLe i j).mapTy = A'}
    {Δ} {σ : Δ ⟶ Γ} {t : y(Δ) ⟶ _}
    (t_tp : t ≫ (s[i]'(ij.trans_lt jlen)).tp = ym(σ) ≫ A) :
    ym(s[j].substCons σ A' (t ≫ (s.homOfLe i j ij jlen).mapTm) (by
      simp [*]
      conv_lhs => rhs; apply (s.homOfLe i j).pb.w
      subst A'; rw [← Category.assoc, ← Category.assoc, ← t_tp]))
    ≫ s.unliftVar i j ij jlen A eq = t := by
  simp [unlift, unliftVar]; apply (s.homOfLe i j).pb.hom_ext <;> simp [*]

/--
If `s` is a sequence of universe homomorphisms then for `i ≤ j` we get a polynomial endofunctor
natural transformation `s[i].Ptp ⟶ s[j].Ptp`.
-/
def cartesianNatTrans (i j : Nat)
    (ij : i ≤ j := by get_elem_tactic) (jlen : j < s.length + 1 := by get_elem_tactic) :
    s[i].Ptp ⟶ s[j].Ptp :=
  (s.homOfLe i j).cartesianNatTrans

@[reassoc]
theorem mk_comp_cartesianNatTrans {i j ij jlen} {Γ X} (A : y(Γ) ⟶ s[i].Ty)
    (B : y(s[i].ext A) ⟶ X) :
    PtpEquiv.mk s[i] A B ≫ (s.cartesianNatTrans i j).app X =
    PtpEquiv.mk s[j] (A ≫ (s.homOfLe i j).mapTy)
    (ym(substCons _ (s[j].disp _) _ (s.unliftVar i j ij jlen A rfl) (by simp)) ≫ B) := by
  convert Hom.mk_comp_cartesianNatTrans _ _ _
  apply (IsPullback.paste_horiz (s[i].disp_pullback _) (s.homOfLe i j).pb).hom_ext
  · simp [unliftVar]
  · simp

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
def cartesianNatTransTm (i0 i1 j0 j1 : Nat)
    (ii : i0 ≤ i1 := by get_elem_tactic) (ilen : i1 < s.length + 1 := by get_elem_tactic)
    (jj : j0 ≤ j1 := by get_elem_tactic) (jlen : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Tm ⟶ s[i1].Ptp.obj s[j1].Tm :=
  (s.cartesianNatTrans i0 i1).app s[j0].Tm ≫
  s[i1].Ptp.map (s.homOfLe j0 j1).mapTm

theorem mk_comp_cartesianNatTransTm {i0 i1 j0 j1 ii ilen jj jlen}
    {Γ X} (A : y(Γ) ⟶ s[i0].Ty) (B : y(s[i0].ext A) ⟶ s[j0].Tm)
    : PtpEquiv.mk s[i0] A B ≫ s.cartesianNatTransTm i0 i1 j0 j1 ii ilen jj jlen =
      PtpEquiv.mk s[i1] (A ≫ (s.homOfLe i0 i1).mapTy)
        (ym(substCons _ (s[i1].disp _) _ (s.unliftVar i0 i1 ii ilen A rfl) (by simp))
          ≫ B ≫ (s.homOfLe j0 j1).mapTm) := by
  simp [cartesianNatTransTm, mk_comp_cartesianNatTrans_assoc, PtpEquiv.mk_map]

theorem cartesianNatTransTm_fstProj {i0 i1 j0 j1 ii ilen jj jlen} :
    s.cartesianNatTransTm i0 i1 j0 j1 ii ilen jj jlen ≫ s[i1].uvPolyTp.fstProj s[j1].Tm =
    s[i0].uvPolyTp.fstProj s[j0].Tm ≫ (s.homOfLe i0 i1).mapTy := by
  simp [cartesianNatTransTm]
  slice_lhs 2 3 => apply UvPoly.map_fstProj
  apply cartesianNatTrans_fstProj

def cartesianNatTransTy (i0 i1 j0 j1 : Nat)
    (i0len : i0 ≤ i1 := by get_elem_tactic) (i1len : i1 < s.length + 1 := by get_elem_tactic)
    (j0len : j0 ≤ j1 := by get_elem_tactic) (j1len : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Ty ⟶ s[i1].Ptp.obj s[j1].Ty :=
  (s.cartesianNatTrans i0 i1).app s[j0].Ty ≫
  s[i1].Ptp.map (s.homOfLe j0 j1).mapTy

theorem mk_comp_cartesianNatTransTy {i0 i1 j0 j1 ii ilen jj jlen}
    {Γ X} (A : y(Γ) ⟶ s[i0].Ty) (B : y(s[i0].ext A) ⟶ s[j0].Ty)
    : PtpEquiv.mk s[i0] A B ≫ s.cartesianNatTransTy i0 i1 j0 j1 ii ilen jj jlen =
      PtpEquiv.mk s[i1] (A ≫ (s.homOfLe i0 i1).mapTy)
        (ym(substCons _ (s[i1].disp _) _ (s.unliftVar i0 i1 ii ilen A rfl) (by simp))
          ≫ B ≫ (s.homOfLe j0 j1).mapTy) := by
  simp [cartesianNatTransTy, mk_comp_cartesianNatTrans_assoc, PtpEquiv.mk_map]

theorem cartesianNatTransTy_fstProj {i0 i1 j0 j1 ii ilen jj jlen} :
    s.cartesianNatTransTy i0 i1 j0 j1 ii ilen jj jlen ≫ s[i1].uvPolyTp.fstProj s[j1].Ty =
    s[i0].uvPolyTp.fstProj s[j0].Ty ≫ (s.homOfLe i0 i1).mapTy := by
  simp only [cartesianNatTransTy]
  slice_lhs 2 3 => apply UvPoly.map_fstProj
  apply cartesianNatTrans_fstProj

theorem hom_comp_trans (s : UHomSeq Ctx) (i j k : Nat) (ij : i < j) (jk : j < k)
    (klen : k < s.length + 1) :
    (s.hom i j ij).comp (s.hom j k jk) = s.hom i k (ij.trans jk) := by
  conv_rhs => unfold hom
  conv in s.hom i j _ => unfold hom
  split_ifs
  all_goals try omega
  . rename_i h _
    cases h
    simp
  . rw [UHom.comp_assoc, hom_comp_trans]
termination_by s.length - i

/--
TODO: Consider generalising to just UHom?
Convert a map into the `i`th type classifier into a a term of the
`i+1`th term classifier, that is a term of the `i`th universe.
It is defined by composition with the first projection of the pullback square
               v
     s[i].Ty ----> s[i+1].Tm
     ^    |          |
  A /     |   p.b.   |
   /      |          |
  /       V          V
y(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : y(Γ) ⟶ s[i].Ty) :
    y(Γ) ⟶ s[i+1].Tm :=
  A ≫ (s.homSucc i).asTm

@[simp]
theorem code_tp {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : y(Γ) ⟶ s[i].Ty) :
    s.code ilen A ≫ s[i+1].tp = (s.homSucc i).wkU Γ := by
  simp [code, (s.homSucc i).U_pb.w, UHom.wkU]

@[reassoc]
theorem comp_code {Δ Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length)
    (σ : y(Δ) ⟶ y(Γ)) (A : y(Γ) ⟶ s[i].Ty) :
    σ ≫ s.code ilen A = s.code ilen (σ ≫ A) := by
  simp [code]

/--
TODO: Consider generalising to just UHom?
Convert a a term of the `i`th universe (it is a `i+1` level term) into
a map into the `i`th type classifier.
It is the unique map into the pullback
             a
y(Γ) -----------------¬
‖  -->          v     V
‖    s[i].Ty ----> s[i+1].Tm
‖         |          |
‖         |   p.b.   |
‖         |          |
‖         V          V
y(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : y(Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    y(Γ) ⟶ s[i].Ty :=
  (s.homSucc i).U_pb.lift a (isTerminal_yUnit.from y(Γ)) (by rw [a_tp, UHom.wkU])

@[reassoc]
theorem comp_el (s : UHomSeq Ctx) {Δ Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (σ : y(Δ) ⟶ y(Γ)) (a : y(Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    σ ≫ s.el ilen a a_tp = s.el ilen (σ ≫ a) (by simp [a_tp]) :=
  (s.homSucc i).U_pb.hom_ext (by simp [el]) (by simp)

@[simp]
lemma el_code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : y(Γ) ⟶ s[i].Ty) :
    el s ilen (code s ilen A) (code_tp _ _ _) = A :=
  (s.homSucc i).U_pb.hom_ext (by simp [el, code]) (by simp)

@[simp]
lemma code_el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : y(Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    code s ilen (el s ilen a a_tp) = a := by
  simp [code, el]

end UHomSeq

/-- The data of type and term formers at each universe `s[i].tp`.

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
structure UHomSeqPiSig (Ctx : Type u) [SmallCategory.{u} Ctx] [CartesianMonoidalCategory Ctx]
    extends UHomSeq Ctx where
  nmPi (i : Nat) (ilen : i < length + 1 := by get_elem_tactic) : NaturalModel.Pi toUHomSeq[i]
  nmSig (i : Nat) (ilen : i < length + 1 := by get_elem_tactic) : NaturalModel.Sigma toUHomSeq[i]

namespace UHomSeqPiSig

variable {Ctx : Type u} [SmallCategory.{u} Ctx] [CartesianMonoidalCategory Ctx]

instance : GetElem (UHomSeqPiSig Ctx) Nat (NaturalModel Ctx)
    (fun s i => i < s.length + 1) where
  getElem s i h := s.toUHomSeq[i]

variable (s : UHomSeqPiSig Ctx)

@[simp]
theorem getElem_toUHomSeq (i : Nat) (ilen : i < s.length + 1) : s.toUHomSeq[i] = s[i] := rfl

-- Sadly, we have to spell out `ilen` and `jlen` due to
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
variable {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)

/-! ## Pi -/

def Pi : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  s.cartesianNatTransTy i (max i j) j (max i j) ≫ (s.nmPi (max i j)).Pi

def lam : s[i].Ptp.obj s[j].Tm ⟶ s[max i j].Tm :=
  s.cartesianNatTransTm i (max i j) j (max i j) ≫ (s.nmPi (max i j)).lam

def Pi_pb :
    IsPullback (s.lam ilen jlen) (s[i].Ptp.map s[j].tp) s[max i j].tp (s.Pi ilen jlen) := by
  have p1 : NatTrans.IsCartesian (s.cartesianNatTrans i (max i j)) := by
   dsimp only [UHomSeq.cartesianNatTrans]
   apply UvPoly.isCartesian_cartesianNatTrans
  let pbB : IsPullback
      (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTm)
      (s[max i j].Ptp.map s[j].tp)
      (s[max i j].Ptp.map s[max i j].tp)
      (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTy) :=
    CategoryTheory.UvPoly.preservesPullbacks s[max i j].uvPolyTp _ _ _ _
    (s.homOfLe j (max i j)).pb
  have q := IsPullback.paste_horiz pbB (s.nmPi (max i j)).Pi_pullback
  apply CategoryTheory.IsPullback.paste_horiz (p1 s[j].tp).flip q

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B
``` -/
def mkPi {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) : y(Γ) ⟶ s[max i j].Ty :=
  PtpEquiv.mk s[i] A B ≫ s.Pi ilen jlen

theorem comp_mkPi {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    ym(σ) ≫ s.mkPi ilen jlen A B = s.mkPi ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) := by
  simp [mkPi, ← Category.assoc, PtpEquiv.mk_comp_left]

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ t : B
-------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. t : ΠA. B
``` -/
def mkLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (t : y(s[i].ext A) ⟶ s[j].Tm) : y(Γ) ⟶ s[max i j].Tm :=
  PtpEquiv.mk s[i] A t ≫ s.lam ilen jlen

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B) :
    s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B := by
  simp [mkLam, mkPi, (s.Pi_pb ilen jlen).w, PtpEquiv.mk_map_assoc, t_tp]

theorem comp_mkLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (t : y(s[i].ext A) ⟶ s[j].Tm) :
    ym(σ) ≫ s.mkLam ilen jlen A t = s.mkLam ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ t) := by
  simp [mkLam, ← Category.assoc, PtpEquiv.mk_comp_left]


/--
```
Γ ⊢ᵢ A  Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B
-----------------------------
Γ.A ⊢ⱼ unlam f : B
``` -/
def unLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    y(s[i].ext A) ⟶ s[j].Tm := by
  let total : y(Γ) ⟶ s[i].Ptp.obj s[j].Tm :=
    (s.Pi_pb ilen jlen).lift f (PtpEquiv.mk s[i] A B) f_tp
  refine PtpEquiv.snd s[i] total _ ?_
  have eq : total ≫ s[i].Ptp.map s[j].tp = PtpEquiv.mk s[i] A B :=
    (s.Pi_pb ilen jlen).lift_snd ..
  apply_fun PtpEquiv.fst s[i] at eq
  rw [PtpEquiv.fst_comp_right] at eq
  simpa using eq

@[simp]
theorem unLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B f f_tp ≫ s[j].tp = B := by
  rw [unLam, ← PtpEquiv.snd_comp_right]
  convert PtpEquiv.snd_mk s[i] A B using 2; simp

theorem comp_unLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    ym(s[i].substWk σ A) ≫ s.unLam ilen jlen A B f f_tp =
      s.unLam ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B)
        (ym(σ) ≫ f) (by simp [f_tp, comp_mkPi]) := by
  simp [unLam]
  rw [← PtpEquiv.snd_comp_left]
  simp [PtpEquiv.snd, UvPoly.Equiv.snd'_eq]
  simp only [← Category.assoc]; congr 2
  apply pullback.hom_ext <;> simp; congr 1
  apply (s.Pi_pb ilen jlen).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_left]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B  Γ ⊢ᵢ a : A
---------------------------------
Γ ⊢ⱼ f a : B[id.a]
``` -/
def mkApp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) : y(Γ) ⟶ s[j].Tm :=
  ym(s[i].sec A a a_tp) ≫ s.unLam ilen jlen A B f f_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    s.mkApp ilen jlen A B f f_tp a a_tp ≫ s[j].tp = ym(s[i].sec A a a_tp) ≫ B := by
  simp [mkApp]

theorem comp_mkApp {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    ym(σ) ≫ s.mkApp ilen jlen A B f f_tp a a_tp =
      s.mkApp ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B)
        (ym(σ) ≫ f) (by simp [f_tp, comp_mkPi])
        (ym(σ) ≫ a) (by simp [a_tp]) := by
  unfold mkApp; rw [← Functor.map_comp_assoc, comp_sec, Functor.map_comp_assoc, comp_unLam]

@[simp]
theorem mkLam_unLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.mkLam ilen jlen A (s.unLam ilen jlen A B f f_tp) = f := by
  let total : y(Γ) ⟶ s[i].Ptp.obj s[j].Tm :=
    (s.Pi_pb ilen jlen).lift f (PtpEquiv.mk s[i] A B) f_tp
  simp [mkLam, unLam]
  have : PtpEquiv.fst s[i] total = A := by
    simp [total, PtpEquiv.fst, UvPoly.Equiv.fst]
    rw [← s[i].uvPolyTp.map_fstProj s[j].tp]
    slice_lhs 1 2 => apply (s.Pi_pb ilen jlen).lift_snd
    apply PtpEquiv.fst_mk
  slice_lhs 1 1 => equals total =>
    apply PtpEquiv.ext _ (A := A) (by simp) (by simp [this]) (by simp [total])
  apply (s.Pi_pb ilen jlen).lift_fst

@[simp]
theorem unLam_mkLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B)
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
def etaExpand {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    y(Γ) ⟶ s[max i j].Tm :=
  s.mkLam ilen jlen A <|
    s.mkApp ilen jlen
      (ym(s[i].disp A) ≫ A) (ym(s[i].substWk ..) ≫ B) (ym(s[i].disp A) ≫ f)
        (by simp [f_tp, comp_mkPi])
      (s[i].var A) (s[i].var_tp A)

theorem etaExpand_eq {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
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
theorem mkApp_mkLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B)
    (lam_tp : s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    s.mkApp ilen jlen A B (s.mkLam ilen jlen A t) lam_tp a a_tp = ym(s[i].sec A a a_tp) ≫ t := by
  rw [mkApp, unLam_mkLam]
  assumption

/-! ## Sigma -/

def Sig : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  s.cartesianNatTransTy i (max i j) j (max i j) ≫ (s.nmSig (max i j)).Sig

def pair : UvPoly.compDom s[i].uvPolyTp s[j].uvPolyTp ⟶ s[max i j].Tm :=
  let l : s[i].uvPolyTp.compDom s[j].uvPolyTp ⟶ s[max i j].uvPolyTp.compDom s[max i j].uvPolyTp :=
    UvPoly.compDomMap
      (s.homOfLe i (max i j)).mapTm
      (s.homOfLe j (max i j)).mapTm
      (s.homOfLe i (max i j)).mapTy
      (s.homOfLe j (max i j)).mapTy
      (s.homOfLe i (max i j)).pb.flip
      (s.homOfLe j (max i j)).pb.flip
  l ≫ (s.nmSig (max i j)).pair

def Sig_pb : IsPullback
    (s.pair ilen jlen)
  (s[i].uvPolyTp.comp s[j].uvPolyTp).p s[max i j].tp
    (s.Sig ilen jlen) :=
  (UvPoly.compDomMap_isPullback ..).paste_horiz (s.nmSig (max i j)).Sig_pullback

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΣA. B
``` -/
def mkSig {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    y(Γ) ⟶ s[max i j].Ty :=
  PtpEquiv.mk s[i] A B ≫ s.Sig ilen jlen

theorem comp_mkSig {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    ym(σ) ≫ s.mkSig ilen jlen A B =
      s.mkSig ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) := by
  simp [mkSig, ← Category.assoc, PtpEquiv.mk_comp_left]

/--
```
Γ ⊢ᵢ t : A  Γ ⊢ⱼ u : B[t]
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ⟨t, u⟩ : ΣA. B
``` -/
def mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    y(Γ) ⟶ s[max i j].Tm := by
  -- have ht : (t ≫ (s.homOfLe i (max i j)).mapTm) ≫ s[max i j].tp =
  --     A ≫ (s.homOfLe i (max i j)).mapTy := by
  --   have := (s.homOfLe i (max i j)).pb.w; dsimp at this
  --   rw [Category.assoc, this, ← Category.assoc, t_tp]
  -- refine compDomEquiv.mk _
  --   (t ≫ (s.homOfLe i (max i j)).mapTm)
  --   (ym(substCons _ (s[max i j].disp _) _
  --       (s.unliftVar i (max i j) (by omega) _ A (by simp [*]))
  --       (by have := @s.unliftVar_tp; simp_all))
  --     ≫ B ≫ (s.homOfLe j (max i j)).mapTy)
  --   (u ≫ (s.homOfLe j (max i j)).mapTm)
  --   ?_
  --   ≫ (s.nmSigma (max i j)).pair
  -- have hu : (u ≫ (s.homOfLe j (max i j)).mapTm) ≫ s[max i j].tp =
  --     ym(s[i].sec A t t_tp) ≫ B ≫ (s.homOfLe j (max i j)).mapTy := by
  --   have := (s.homOfLe j (max i j)).pb.w; dsimp at this
  --   rw [Category.assoc, this, ← Category.assoc, u_tp, Category.assoc]
  -- dsimp; rw [hu, ← Functor.map_comp_assoc]; congr! 2
  -- rw [comp_substCons, sec]; congr!
  -- · simp
  -- · symm; apply s.substCons_unliftVar; simp [t_tp]
  refine compDomEquiv.mk _ t (ym(eqToHom congr(s[i].ext $t_tp)) ≫ B) u ?_ ≫ s.pair ilen jlen
  rw [u_tp, ← Functor.map_comp_assoc]; subst A; simp

theorem comp_mkPair {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    ym(σ) ≫ s.mkPair ilen jlen A B t t_tp u u_tp =
      s.mkPair ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B)
        (ym(σ) ≫ t) (by simp [t_tp])
        (ym(σ) ≫ u) (by simp [u_tp, comp_sec_functor_map_assoc]) := by
  simp only[← Category.assoc,eqToHom_map,mkPair]
  congr
  apply NaturalModel.compDomEquiv.mk_naturality (A:= A) (e1 := t_tp)
  · simp[u_tp]
  · simp only [u_tp]
    rw![t_tp]
    rfl




@[simp]
theorem mkPair_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkPair ilen jlen A B t t_tp u u_tp ≫ s[max i j].tp = s.mkSig ilen jlen A B := by
  unfold mkPair mkSig Sig
  sorry -- equiv theorems

def mkFst {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    y(Γ) ⟶ s[i].Tm :=
  -- s.unlift i (max i j) (by omega) (by omega) A
  --   (compDomEquiv.fst s[max i j]
  --     ((s.nmSig (max i j)).Sig_pullback.lift p
  --       (PtpEquiv.mk s[max i j]
  --         (A ≫ (s.homOfLe i (max i j)).mapTy)
  --         (ym(substCons _ (s[max i j].disp _) _
  --           (s.unliftVar i (max i j) (by omega) _ A (by simp [*]))
  --           (by have' := @s.unliftVar_tp; simp_all))
  --         ≫ B ≫ (s.homOfLe j (max i j)).mapTy))
  --       (by
  --         simp [mkSig, *, Sig]
  --         rw [← Category.assoc]; congr! 1
  --         apply s.mk_cartesianNatTransTy)))
  --   (by simp [compDomEquiv.fst_tp])
  compDomEquiv.fst s[j] ((s.Sig_pb ilen jlen).lift p (PtpEquiv.mk _ A B) p_tp)

@[simp]
theorem mkFst_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    s.mkFst ilen jlen A B p p_tp ≫ s[i].tp = A := by simp [mkFst, compDomEquiv.fst_tp]

@[simp]
theorem mkFst_mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkFst ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = t := by
  simp [mkFst, mkPair]
  apply (s.homOfLe i (max i j)).pb.hom_ext <;> simp
  · sorry
  · sorry

theorem comp_mkFst {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    ym(σ) ≫ s.mkFst ilen jlen A B p p_tp =
      s.mkFst ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) (ym(σ) ≫ p)
        (by simp [p_tp, comp_mkSig]) := by
  sorry

def mkSnd {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    y(Γ) ⟶ s[j].Tm := by
  let := (s.nmSig (max i j)).Sig_pullback.lift p
    (PtpEquiv.mk s[max i j]
      (A ≫ (s.homOfLe i (max i j)).mapTy)
      (ym(substCons _ (s[max i j].disp _) _
        (s.unliftVar i (max i j) (by omega) _ A (by simp [*]))
        (by have' := @s.unliftVar_tp; simp_all))
      ≫ B ≫ (s.homOfLe j (max i j)).mapTy))
    (by
      simp [mkSig, *, Sig]
      rw [← Category.assoc]; congr! 1
      apply s.mk_comp_cartesianNatTransTy)
  refine s.unlift j (max i j) (by omega) (by omega)
    (ym(s[i].sec _ (s.mkFst ilen jlen A B p p_tp) (by simp)) ≫ B)
    (compDomEquiv.snd s[max i j] this) ?_
  simp [compDomEquiv.snd_tp]
  sorry

@[simp]
theorem mkSnd_mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkSnd ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = u := by
  sorry

@[simp]
theorem mkSnd_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    s.mkSnd ilen jlen A B p p_tp ≫ s[j].tp =
      ym(s[i].sec A (s.mkFst ilen jlen A B p p_tp) (by simp)) ≫ B := s.unlift_tp ..

theorem comp_mkSnd {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    ym(σ) ≫ s.mkSnd ilen jlen A B p p_tp =
      s.mkSnd ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) (ym(σ) ≫ p)
        (by simp [p_tp, comp_mkSig]) := by
  sorry

@[simp]
theorem mkPair_mkFst_mkSnd {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSig ilen jlen A B) :
    s.mkPair ilen jlen A B
      (s.mkFst ilen jlen A B p p_tp) (by simp)
      (s.mkSnd ilen jlen A B p p_tp) (by simp) = p := by
  sorry

/-! ## Identity types -/

/--
```
Γ ⊢ᵢ A  Γ ⊢ᵢ a0, a1 : A
-----------------------
Γ ⊢ᵢ Id(A, a0, a1)
``` -/
def mkId {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (a0 a1 : y(Γ) ⟶ s[i].Tm)
    (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
    y(Γ) ⟶ s[i].Ty :=
  sorry

theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (a0 a1 : y(Γ) ⟶ s[i].Tm)
    (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
    ym(σ) ≫ s.mkId ilen A a0 a1 a0_tp a1_tp =
      s.mkId ilen (ym(σ) ≫ A) (ym(σ) ≫ a0) (ym(σ) ≫ a1)
        (by simp [a0_tp]) (by simp [a1_tp]) := by
  sorry

/--
```
Γ ⊢ᵢ t : A
-----------------------
Γ ⊢ᵢ refl(t) : Id(A, t, t)
``` -/
def mkRefl {Γ : Ctx} (t : y(Γ) ⟶ s[i].Tm) : y(Γ) ⟶ s[i].Tm :=
  sorry

theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (t : y(Γ) ⟶ s[i].Tm) :
    ym(σ) ≫ s.mkRefl ilen t = s.mkRefl ilen (ym(σ) ≫ t) := by
  sorry

@[simp]
theorem mkRefl_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A) :
    s.mkRefl ilen t ≫ s[i].tp = s.mkId ilen A t t t_tp t_tp := by
  sorry

/--
```
Γ ⊢ᵢ t : A
-----------------------
Γ ⊢ᵢ idRec(t) : Id(A, t, t)
``` -/
def mkIdRec {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (M : y(s[i].ext (s.mkId ilen (ym(s[i].disp A) ≫ A)
      (ym(s[i].disp A) ≫ t) (s[i].var A) (by> simp [*]) (by> simp))) ⟶ s[j].Ty)
    (r : y(Γ) ⟶ s[j].Tm) (r_tp : r ≫ s[j].tp =
      ym(substCons _ (s[i].sec A t t_tp) _ (s.mkRefl ilen t)
        (by> subst t_tp; simp [comp_mkId])) ≫ M)
    (u : y(Γ) ⟶ s[i].Tm) (u_tp : u ≫ s[i].tp = A)
    (h : y(Γ) ⟶ s[i].Tm) (h_tp : h ≫ s[i].tp = s.mkId ilen A t u t_tp u_tp) :
    y(Γ) ⟶ s[j].Tm :=
  sorry

theorem comp_mkIdRec {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (t t_tp M) (r : y(Γ) ⟶ s[j].Tm) (r_tp u u_tp h h_tp) :
    ym(σ) ≫ s.mkIdRec ilen jlen A t t_tp M r r_tp u u_tp h h_tp =
    s.mkIdRec ilen jlen (ym(σ) ≫ A) (ym(σ) ≫ t) (by> simp [*])
       (ym(s[i].substWk (s[i].substWk σ _) _ _ (by>
            simp [comp_mkId]
            congr! 1 <;> rw [← Functor.map_comp_assoc, substWk_disp] <;> simp))
          ≫ M)
       (ym(σ) ≫ r) (by>
        simp [*]
        simp only [← Functor.map_comp_assoc]; congr! 2
        simp [comp_substCons, comp_sec, substWk, comp_mkRefl])
       (ym(σ) ≫ u) (by> simp [*])
       (ym(σ) ≫ h) (by> simp [*, comp_mkId]) := by
  sorry

@[simp]
theorem mkIdRec_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty)
    (t t_tp M) (r : y(Γ) ⟶ s[j].Tm) (r_tp u u_tp h h_tp) :
    s.mkIdRec ilen jlen A t t_tp M r r_tp u u_tp h h_tp ≫ s[j].tp =
      ym(substCons _ (s[i].sec _ u u_tp) _ h (by> simp [*, comp_mkId])) ≫ M := by
  sorry

@[simp]
theorem mkIdRec_mkRefl {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty)
    (t t_tp M) (r : y(Γ) ⟶ s[j].Tm) (r_tp) :
    s.mkIdRec ilen jlen A t t_tp M r r_tp t t_tp
      (s.mkRefl ilen t) (s.mkRefl_tp ilen _ t t_tp) = r := by
  sorry

end UHomSeqPiSig
