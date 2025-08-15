import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import GroupoidModel.ForPoly

/-! Morphisms of natural models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory

namespace NaturalModelBase

variable {Ctx : Type u} [SmallCategory Ctx]

/- We have a 'nice', specific terminal object in `Ctx`,
and this instance allows use to use it directly
rather than through an isomorphism with `Limits.terminal`.
`ChosenTerminal` would suffice but is not defined in mathlib,
so we use `ChosenFiniteProducts`. -/
variable [CartesianMonoidalCategory Ctx]

-- Should be in mathlib?
def isTerminal_yUnit : IsTerminal y(𝟙_ Ctx) :=
  (IsTerminal.ofUnique (𝟙_ Ctx)).isTerminalObj yoneda (𝟙_ Ctx)

structure Hom (M N : NaturalModelBase Ctx) where
  mapTm : M.Tm ⟶ N.Tm
  mapTy : M.Ty ⟶ N.Ty
  pb : IsPullback mapTm M.tp N.tp mapTy

def Hom.id (M : NaturalModelBase Ctx) : Hom M M where
  mapTm := 𝟙 _
  mapTy := 𝟙 _
  pb := IsPullback.of_id_fst

def Hom.comp {M N O : NaturalModelBase Ctx} (α : Hom M N) (β : Hom N O) : Hom M O where
  mapTm := α.mapTm ≫ β.mapTm
  mapTy := α.mapTy ≫ β.mapTy
  pb := α.pb.paste_horiz β.pb

def Hom.comp_assoc {M N O P : NaturalModelBase Ctx} (α : Hom M N) (β : Hom N O) (γ : Hom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp]

/-- Morphism into the representable natural transformation `M`
from the pullback of `M` along a type. -/
protected def pullbackHom (M : NaturalModelBase Ctx) {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
    Hom (M.pullback A) M where
  mapTm := M.var A
  mapTy := A
  pb := M.disp_pullback A

/-- Given `M : NaturalModelBase`, a semantic type `A : y(Γ) ⟶ M.Ty`,
and a substitution `σ : Δ ⟶ Γ`, construct a Hom for the substitution `A[σ]`.
-/
def Hom.subst (M : NaturalModelBase Ctx)
    {Γ Δ : Ctx} (A : y(Γ) ⟶ M.Ty) (σ : Δ ⟶ Γ) :
    Hom (M.pullback (ym(σ) ≫ A)) (M.pullback A) :=
  let Aσ := ym(σ) ≫ A
  { mapTm :=
    (M.disp_pullback A).lift (M.var Aσ) ym(M.disp Aσ ≫ σ) (by aesop_cat)
    mapTy := ym(σ)
    pb := by
      convert IsPullback.of_right' (M.disp_pullback Aσ) (M.disp_pullback A)
      simp }

/-- A Russell universe embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `UHom.id M` is essentially `Type : Type` in `M`.

Note this doesn't need to extend `Hom` as none of its fields are used;
it's just convenient to pack up the data. -/
structure UHom (M N : NaturalModelBase Ctx) extends Hom M N where
  U : y(𝟙_ Ctx) ⟶ N.Ty
  asTm : M.Ty ⟶ N.Tm
  U_pb : IsPullback
                                asTm
    (isTerminal_yUnit.from M.Ty)   N.tp
                                 U

def UHom.ofTyIsoExt
    {M N : NaturalModelBase Ctx}
    (H : Hom M N) {U : y(𝟙_ Ctx) ⟶ N.Ty} (i : M.Ty ≅ y(N.ext U)) :
    UHom M N := { H with
  U := U
  asTm := i.hom ≫ N.var U
  U_pb := by
    convert IsPullback.of_iso_isPullback (N.disp_pullback _) i
    apply isTerminal_yUnit.hom_ext
}

def UHom.comp {M N O : NaturalModelBase Ctx} (α : UHom M N) (β : UHom N O) : UHom M O := {
  Hom.comp α.toHom β.toHom with
  U := α.U ≫ β.mapTy
  asTm := α.asTm ≫ β.mapTm
  U_pb := α.U_pb.paste_horiz β.pb
}

def UHom.comp_assoc {M N O P : NaturalModelBase Ctx} (α : UHom M N) (β : UHom N O) (γ : UHom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def UHom.wkU {M N : NaturalModelBase Ctx} (Γ : Ctx) (α : UHom M N) : y(Γ) ⟶ N.Ty :=
  isTerminal_yUnit.from y(Γ) ≫ α.U

@[reassoc (attr := simp)]
theorem UHom.comp_wkU {M N : NaturalModelBase Ctx} {Δ Γ : Ctx} (α : UHom M N) (f : y(Δ) ⟶ y(Γ)) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `UHom` into a natural model with a Tarski universe. -/
def UHom.ofTarskiU (M : NaturalModelBase Ctx) (U : y(𝟙_ Ctx) ⟶ M.Ty) (El : y(M.ext U) ⟶ M.Ty) :
    UHom (M.pullback El) M := {
  M.pullbackHom El with
  U
  asTm := M.var U
  U_pb := (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (by simp) (isTerminal_yUnit.hom_ext ..)
      (by simp) (by simp)
}

/-! ## Universe embeddings -/

variable (Ctx) in
/-- A sequence of Russell universe embeddings. -/
structure UHomSeq [CartesianMonoidalCategory Ctx] where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs (i : Nat) (h : i < length + 1) : NaturalModelBase Ctx
  homSucc' (i : Nat) (h : i < length) : UHom (objs i <| by omega) (objs (i + 1) <| by omega)

namespace UHomSeq

variable (s : UHomSeq Ctx)

instance : GetElem (UHomSeq Ctx) Nat (NaturalModelBase Ctx) (fun s i => i < s.length + 1) where
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
    have : i < j := by omega
    (s.hom i j this _).toHom

/--
If `s` is a sequence of universe homomorphisms then for `i ≤ j` we get a polynomial endofunctor
natural transformation `s[i].Ptp ⟶ s[j].Ptp`.
-/
def homCartesianNaturalTrans (i j : Nat)
    (ilen : i ≤ j := by get_elem_tactic) (jlen : j < s.length + 1 := by get_elem_tactic) :
    s[i].Ptp ⟶ s[j].Ptp :=
  let hi : Hom s[i] s[j] := s.homOfLe i j
  s[i].uvPolyTp.cartesianNatTrans s[j].uvPolyTp hi.mapTy hi.mapTm hi.pb.flip

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
def homCartesianNaturalTransTm (i0 i1 j0 j1 : Nat)
    (i0len : i0 ≤ i1 := by get_elem_tactic) (i1len : i1 < s.length + 1 := by get_elem_tactic)
    (j0len : j0 ≤ j1 := by get_elem_tactic) (j1len : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Tm ⟶ s[i1].Ptp.obj s[j1].Tm :=
  (s.homCartesianNaturalTrans i0 i1).app s[j0].Tm ≫
  s[i1].uvPolyTp.functor.map (s.homOfLe j0 j1).mapTm

def homCartesianNaturalTransTy (i0 i1 j0 j1 : Nat)
    (i0len : i0 ≤ i1 := by get_elem_tactic) (i1len : i1 < s.length + 1 := by get_elem_tactic)
    (j0len : j0 ≤ j1 := by get_elem_tactic) (j1len : j1 < s.length + 1 := by get_elem_tactic)
    : s[i0].Ptp.obj s[j0].Ty ⟶ s[i1].Ptp.obj s[j1].Ty :=
  (s.homCartesianNaturalTrans i0 i1).app s[j0].Ty ≫
  s[i1].uvPolyTp.functor.map (s.homOfLe j0 j1).mapTy

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
structure UHomSeqPiSigma (Ctx : Type u) [SmallCategory.{u} Ctx] [CartesianMonoidalCategory Ctx]
    extends UHomSeq Ctx where
  nmPi (i : Nat) (ilen : i < length + 1 := by get_elem_tactic) : NaturalModelPi toUHomSeq[i]
  nmSigma (i : Nat) (ilen : i < length + 1 := by get_elem_tactic) : NaturalModelSigma toUHomSeq[i]

namespace UHomSeqPiSigma

variable {Ctx : Type u} [SmallCategory.{u} Ctx] [CartesianMonoidalCategory Ctx]

instance : GetElem (UHomSeqPiSigma Ctx) Nat (NaturalModelBase Ctx)
    (fun s i => i < s.length + 1) where
  getElem s i h := s.toUHomSeq[i]

variable (s : UHomSeqPiSigma Ctx)

@[simp]
theorem getElem_toUHomSeq (i : Nat) (ilen : i < s.length + 1) : s.toUHomSeq[i] = s[i] := rfl

-- Sadly, we have to spell out `ilen` and `jlen` due to
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
variable {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)

/-! ## Pi -/

def Pi : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  s.homCartesianNaturalTransTy i (max i j) j (max i j) ≫ (s.nmPi (max i j)).Pi

def lam : s[i].Ptp.obj s[j].Tm ⟶ s[max i j].Tm :=
  s.homCartesianNaturalTransTm i (max i j) j (max i j) ≫ (s.nmPi (max i j)).lam



def Pi_pb :
    IsPullback (s.lam ilen jlen) (s[i].Ptp.map s[j].tp) s[max i j].tp (s.Pi ilen jlen) := by
    have i2m : Hom s[i] s[max i j] := s.homOfLe i (max i j)
    have t:= s[j].tp
    let p := (s.homCartesianNaturalTrans i (max i j))
    have p1 : NatTrans.IsCartesian ((s.homCartesianNaturalTrans i (max i j))) := by
     simp[NaturalModelBase.UHomSeq.homCartesianNaturalTrans]
     apply CategoryTheory.UvPoly.isCartesian_cartesianNatTrans
    let pbL : IsPullback
              ((s.homCartesianNaturalTrans i (max i j) _ _).app s[j].Tm)
              (s[i].Ptp.map s[j].tp)
              (s[max i j].Ptp.map s[j].tp)
              ((s.homCartesianNaturalTrans i (max i j) _ _).app s[j].Ty) := (p1 s[j].tp).flip
    let pbR := (s.nmPi (max i j)).Pi_pullback
    let pbB0: IsPullback
              (s.homOfLe j (max i j)).mapTm
              (s[j].tp)
              (s[max i j].tp)
              ((s.homOfLe j (max i j)).mapTy) := (s.homOfLe j (max i j)).pb
    let pbB : IsPullback
              (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTm)
              (s[max i j].Ptp.map s[j].tp)
              (s[max i j].Ptp.map s[max i j].tp)
              (s[max i j].Ptp.map (s.homOfLe j (max i j)).mapTy) :=
              CategoryTheory.UvPoly.preservesPullbacks s[max i j].uvPolyTp _ _ _ _ pbB0

    have q := CategoryTheory.IsPullback.paste_horiz pbB pbR
    simp[lam,Pi,UHomSeq.homCartesianNaturalTransTm,UHomSeq.homCartesianNaturalTransTy]
    apply CategoryTheory.IsPullback.paste_horiz pbL q

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B
``` -/
def mkPi {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) : y(Γ) ⟶ s[max i j].Ty :=
  s[i].Ptp_equiv.symm ⟨A, B⟩ ≫ s.Pi ilen jlen

theorem comp_mkPi {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    ym(σ) ≫ s.mkPi ilen jlen A B = s.mkPi ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) := by
  sorry

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ t : B
-------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. t : ΠA. B
``` -/
def mkLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (t : y(s[i].ext A) ⟶ s[j].Tm) : y(Γ) ⟶ s[max i j].Tm :=
  s[i].Ptp_equiv.symm ⟨A, t⟩ ≫ s.lam ilen jlen

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B) :
    s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B := by
  simp [mkLam, mkPi, (s.Pi_pb ilen jlen).w, s[i].Ptp_equiv_symm_naturality_right_assoc, t_tp]

theorem comp_mkLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (t : y(s[i].ext A) ⟶ s[j].Tm) :
    ym(σ) ≫ s.mkLam ilen jlen A t = s.mkLam ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ t) := by
  sorry

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
    (s.Pi_pb ilen jlen).lift f (s[i].Ptp_equiv.symm ⟨A, B⟩) f_tp
  convert (s[i].Ptp_equiv total).snd
  have eq : total ≫ s[i].Ptp.map s[j].tp = s[i].Ptp_equiv.symm ⟨A, B⟩ :=
    (s.Pi_pb ilen jlen).isLimit.fac _ (some .right)
  apply_fun s[i].Ptp_equiv at eq
  apply_fun Sigma.fst at eq
  rw [Equiv.apply_symm_apply, Ptp_equiv_naturality_right] at eq
  simpa using eq.symm

@[simp]
theorem unLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B f f_tp ≫ s[j].tp = B := by
  -- This proof is `s[i].Ptp_equiv_symm_naturality`, `IsPullback.lift_snd`, and ITT gunk.
  dsimp only [unLam]
  sorry

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
  sorry

@[simp]
theorem mkLam_unLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.mkLam ilen jlen A (s.unLam ilen jlen A B f f_tp) = f := by
  sorry

@[simp]
theorem unLam_mkLam {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B)
    (lam_tp : s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B (s.mkLam ilen jlen A t) lam_tp = t := by
  sorry

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
      (s[i].wk A A) (ym(s[i].substWk ..) ≫ B) (s[i].wk A f)
        (by simp_rw [wk_tp, f_tp, wk, comp_mkPi])
      (s[i].var A) (s[i].var_tp A)

theorem etaExpand_eq {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.etaExpand ilen jlen A B f f_tp = f := by
  sorry

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
  s.homCartesianNaturalTransTy i (max i j) j (max i j) ≫ (s.nmSigma (max i j)).Sig

def pair : UvPoly.compDom s[i].uvPolyTp s[j].uvPolyTp ⟶ s[max i j].Tm :=
  let h:  s[i].uvPolyTp.compDom s[j].uvPolyTp ⟶ s[max i j].uvPolyTp.compDom s[max i j].uvPolyTp
  := sorry
  h ≫ (s.nmSigma (max i j)).pair

def Sig_pb : IsPullback
    (s.pair ilen jlen)
  (s[i].uvPolyTp.comp s[j].uvPolyTp).p s[max i j].tp
    (s.Sig ilen jlen) :=
  sorry

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΣA. B
``` -/
def mkSigma {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    y(Γ) ⟶ s[max i j].Ty :=
  s[i].Ptp_equiv.symm ⟨A, B⟩ ≫ s.Sig ilen jlen

theorem comp_mkSigma {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) :
    ym(σ) ≫ s.mkSigma ilen jlen A B =
      s.mkSigma ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) := by
  sorry

/--
```
Γ ⊢ᵢ t : A  Γ ⊢ⱼ u : B[t]
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ⟨t, u⟩ : ΣA. B
``` -/
def mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    y(Γ) ⟶ s[max i j].Tm :=
  NaturalModelBase.compDomEquiv.mk s[j] t (t_tp ▸ B) u sorry ≫ s.pair ilen jlen

theorem comp_mkPair {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    ym(σ) ≫ s.mkPair ilen jlen A B t t_tp u u_tp =
      s.mkPair ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B)
        (ym(σ) ≫ t) (by simp [t_tp])
        (ym(σ) ≫ u) (by simp [u_tp, comp_sec_functor_map_assoc]) := by
  sorry

@[simp]
theorem mkPair_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkPair ilen jlen A B t t_tp u u_tp ≫ s[max i j].tp = s.mkSigma ilen jlen A B := by
  sorry -- equiv theorems

def mkFst {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    y(Γ) ⟶ s[i].Tm :=
  let AB := s[i].Ptp_equiv.symm ⟨A, B⟩
  let tu : y(Γ) ⟶ s[i].uvPolyTp.compDom s[j].uvPolyTp :=
    (s.Sig_pb ilen jlen).lift p AB p_tp
  NaturalModelBase.compDomEquiv.fst s[j] tu

@[simp]
theorem mkFst_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    s.mkFst ilen jlen A B p p_tp ≫ s[i].tp = A := by
  sorry

@[simp]
theorem mkFst_mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkFst ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = t := by
  sorry

theorem comp_mkFst {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    ym(σ) ≫ s.mkFst ilen jlen A B p p_tp =
      s.mkFst ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) (ym(σ) ≫ p)
        (by simp [p_tp, comp_mkSigma]) := by
  sorry

def mkSnd {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    y(Γ) ⟶ s[j].Tm :=
  let AB := s[i].Ptp_equiv.symm ⟨A, B⟩
  let tu : y(Γ) ⟶ s[i].uvPolyTp.compDom s[j].uvPolyTp :=
    (s.Sig_pb ilen jlen).lift p AB p_tp
  NaturalModelBase.compDomEquiv.snd s[j] tu

@[simp]
theorem mkSnd_mkPair {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (u : y(Γ) ⟶ s[j].Tm) (u_tp : u ≫ s[j].tp = ym(s[i].sec A t t_tp) ≫ B) :
    s.mkSnd ilen jlen A B (s.mkPair ilen jlen A B t t_tp u u_tp) (by simp) = u := by
  sorry

@[simp]
theorem mkSnd_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    s.mkSnd ilen jlen A B p p_tp ≫ s[j].tp =
      ym(s[i].sec A (s.mkFst ilen jlen A B p p_tp) (by simp)) ≫ B := by
  sorry

theorem comp_mkSnd {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    ym(σ) ≫ s.mkSnd ilen jlen A B p p_tp =
      s.mkSnd ilen jlen (ym(σ) ≫ A) (ym(s[i].substWk σ A) ≫ B) (ym(σ) ≫ p)
        (by simp [p_tp, comp_mkSigma]) := by
  sorry

@[simp]
theorem mkPair_mkFst_mkSnd {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (p : y(Γ) ⟶ s[max i j].Tm) (p_tp : p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) :
    s.mkPair ilen jlen A B
      (s.mkFst ilen jlen A B p p_tp) (by simp)
      (s.mkSnd ilen jlen A B p p_tp) (by simp) = p := by
  sorry

end UHomSeqPiSigma
