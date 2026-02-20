import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import HoTTLean.ForMathlib
import HoTTLean.Model.Unstructured.UnstructuredUniverse
import HoTTLean.Syntax.Typing

/-! Morphisms of unstructured models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Opposite MonoidalCategory

namespace Model

namespace UnstructuredUniverse

variable {Ctx : Type u} [Category Ctx] (M : UnstructuredUniverse Ctx)

open ChosenTerminal

macro "by>" s:tacticSeq : term => `(by as_aux_lemma => $s)

structure Hom (M N : UnstructuredUniverse Ctx) where
  mapTm : M.Tm ⟶ N.Tm
  mapTy : M.Ty ⟶ N.Ty
  pb : IsPullback mapTm M.tp N.tp mapTy

def Hom.id (M : UnstructuredUniverse Ctx) : Hom M M where
  mapTm := 𝟙 _
  mapTy := 𝟙 _
  pb := IsPullback.of_id_fst

def Hom.comp {M N O : UnstructuredUniverse Ctx} (α : Hom M N) (β : Hom N O) : Hom M O where
  mapTm := α.mapTm ≫ β.mapTm
  mapTy := α.mapTy ≫ β.mapTy
  pb := α.pb.paste_horiz β.pb

def Hom.comp_assoc {M N O P : UnstructuredUniverse Ctx} (α : Hom M N) (β : Hom N O) (γ : Hom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp]

/-- Morphism into the representable natural transformation `M`
from the pullback of `M` along a type. -/
protected def pullbackHom (M : UnstructuredUniverse Ctx) {Γ : Ctx} (A : (Γ) ⟶ M.Ty) :
    Hom (M.pullback A) M where
  mapTm := M.var A
  mapTy := A
  pb := M.disp_pullback A

/-- Given `M : Universe`, a semantic type `A : (Γ) ⟶ M.Ty`,
and a substitution `σ : Δ ⟶ Γ`, construct a Hom for the substitution `A[σ]`.
-/
def Hom.subst (M : UnstructuredUniverse Ctx)
    {Γ Δ : Ctx} (A : (Γ) ⟶ M.Ty) (σ : Δ ⟶ Γ) :
    Hom (M.pullback ((σ) ≫ A)) (M.pullback A) :=
  let Aσ := (σ) ≫ A
  { mapTm :=
    (M.disp_pullback A).lift (M.var Aσ) (M.disp Aσ ≫ σ) (by aesop_cat)
    mapTy := (σ)
    pb := by
      convert IsPullback.of_right' (M.disp_pullback Aσ) (M.disp_pullback A)}

@[simp] def Hom.extIsoExt {M N : UnstructuredUniverse Ctx} (h : Hom M N)
    {Γ} (A : Γ ⟶ M.Ty) : (N.ext (A ≫ h.mapTy)) ≅ (M.ext A) :=
  IsPullback.isoIsPullback N.Tm Γ (N.disp_pullback (A ≫ h.mapTy))
  (IsPullback.paste_horiz (M.disp_pullback A) h.pb)

variable [ChosenTerminal Ctx]

/-- A Russell universe embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `UHom.id M` is essentially `Type : Type` in `M`.

Note this doesn't need to extend `Hom` as none of its fields are used;
it's just convenient to pack up the data. -/
structure UHom (M N : UnstructuredUniverse Ctx) extends Hom M N where
  U : terminal ⟶ N.Ty
  asTm : M.Ty ⟶ N.Tm
  U_pb : IsPullback
            /- m.Ty -/           asTm /- N.Tm -/
    (isTerminal.from M.Ty)         N.tp
             /- ⊤ -/               U  /- N.Ty -/

def UHom.ofTyIsoExt
    {M N : UnstructuredUniverse Ctx}
    (H : Hom M N) {U : (𝟭_ Ctx) ⟶ N.Ty} (i : M.Ty ≅ (N.ext U)) :
    UHom M N where
  __ := H
  U := U
  asTm := i.hom ≫ N.var U
  U_pb := by
    convert IsPullback.of_iso_isPullback (N.disp_pullback _) i
    apply isTerminal.hom_ext

def UHom.comp {M N O : UnstructuredUniverse Ctx} (α : UHom M N) (β : UHom N O) : UHom M O where
  __ := Hom.comp α.toHom β.toHom
  U := α.U ≫ β.mapTy
  asTm := α.asTm ≫ β.mapTm
  U_pb := α.U_pb.paste_horiz β.pb

def UHom.comp_assoc {M N O P : UnstructuredUniverse Ctx} (α : UHom M N) (β : UHom N O) (γ : UHom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def UHom.wkU {M N : UnstructuredUniverse Ctx} (Γ : Ctx) (α : UHom M N) : (Γ) ⟶ N.Ty :=
  isTerminal.from Γ ≫ α.U

@[reassoc (attr := simp)]
theorem UHom.comp_wkU {M N : UnstructuredUniverse Ctx} {Δ Γ : Ctx} (α : UHom M N) (f : (Δ) ⟶ (Γ)) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `UHom` into a natural model with a Tarski universe. -/
def UHom.ofTarskiU (M : UnstructuredUniverse Ctx) (U : (𝟭_ Ctx) ⟶ M.Ty) (El : (M.ext U) ⟶ M.Ty) :
    UHom (M.pullback El) M where
  __ := M.pullbackHom El
  U
  asTm := M.var U
  U_pb := (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (by simp) (isTerminal.hom_ext ..)
      (by simp) (by simp)

section

variable {M N : UnstructuredUniverse Ctx} (α : Hom M N) {Γ Δ : Ctx} {σ : Δ ⟶ Γ} (A : Γ ⟶ M.Ty)
  {σA : Δ ⟶ M.Ty} (eq : σ ≫ A = σA)

def Hom.extCompMapTyIsoExt : N.ext (A ≫ α.mapTy) ≅ M.ext A :=
  (N.disp_pullback (A ≫ α.mapTy)).isoIsPullback _ _
  (IsPullback.paste_horiz (M.disp_pullback A) α.pb)

lemma Hom.extCompMapTyIsoExt_hom_comp_substWk  :
    (α.extCompMapTyIsoExt σA).hom ≫ M.substWk σ A σA eq =
    N.substWk σ (A ≫ α.mapTy) (σA ≫ α.mapTy) (by simp [← eq]) ≫ (α.extCompMapTyIsoExt A).hom := by
  apply (disp_pullback ..).hom_ext
  · apply α.pb.hom_ext
    · simp [extCompMapTyIsoExt]
    · simp [eq, extCompMapTyIsoExt]
  · simp [extCompMapTyIsoExt]

end

namespace PolymorphicPi.ofMonomorphic

variable {U0 U1 U2 : UnstructuredUniverse Ctx} (P : PolymorphicPi U2 U2 U2)
    (l0 : Hom U0 U2) (l1 : Hom U1 U2) {Γ : Ctx} {A : Γ ⟶ U0.Ty}
    (B : U0.ext A ⟶ U1.Ty)

abbrev B2 := (l0.extCompMapTyIsoExt A).hom ≫ B ≫ l1.mapTy

def Pi : Γ ⟶ U2.Ty := P.Pi (B2 l0 l1 B)

def lam (b : U0.ext A ⟶ U1.Tm) (b_tp : b ≫ U1.tp = B) : Γ ⟶ U2.Tm :=
  P.lam ((l0.extCompMapTyIsoExt A).hom ≫ B ≫ l1.mapTy)
  ((l0.extCompMapTyIsoExt A).hom ≫ b ≫ l1.mapTm) (by simp [← b_tp, l1.pb.w])

def unLam (f : Γ ⟶ U2.Tm) (hf : f ≫ U2.tp = ofMonomorphic.Pi P l0 l1 B) : U0.ext A ⟶ U1.Tm :=
  l1.pb.lift ((Hom.extCompMapTyIsoExt l0 A).inv ≫ P.unLam (B2 l0 l1 B) f (by simp [hf, Pi])) B
  (by simp [P.unLam_tp])

end PolymorphicPi.ofMonomorphic

def PolymorphicPi.ofMonomorphic {U0 U1 U2 : UnstructuredUniverse Ctx} (P : PolymorphicPi U2 U2 U2)
    (l0 : Hom U0 U2) (l1 : Hom U1 U2) : PolymorphicPi U0 U1 U2 where
  Pi := ofMonomorphic.Pi P l0 l1
  Pi_comp σ A σA eq B := by
    dsimp [ofMonomorphic.Pi]
    rw [← P.Pi_comp _ _ (σA := σA ≫ l0.mapTy) (by simp [← eq])]
    simp only [← Category.assoc, Hom.extCompMapTyIsoExt_hom_comp_substWk]
  lam := ofMonomorphic.lam P l0 l1
  lam_comp σ A σA eq B b b_tp := by
    dsimp [ofMonomorphic.lam]
    rw [← P.lam_comp _ (σA := σA ≫ l0.mapTy) (by simp [← eq])]
    simp only [← Category.assoc, Hom.extCompMapTyIsoExt_hom_comp_substWk]
  lam_tp _ _ _ := P.lam_tp ..
  unLam := ofMonomorphic.unLam  P l0 l1
  unLam_tp B f f_tp := by simp [ofMonomorphic.unLam]
  unLam_lam B b b_tp := by
    apply l1.pb.hom_ext <;> simp [ofMonomorphic.unLam, ofMonomorphic.lam, P.unLam_lam, b_tp]
  lam_unLam := by simp [ofMonomorphic.unLam, ofMonomorphic.lam, P.lam_unLam]

/-! ## Universe embeddings -/

variable (Ctx) in
/-- A sequence of Russell universe embeddings. -/
structure UHomSeq where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  univMax_le : SynthLean.univMax ≤ length
  objs (i : Nat) (h : i < length + 1) : UnstructuredUniverse Ctx
  homSucc' (i : Nat) (h : i < length) : UHom (objs i <| by omega) (objs (i + 1) <| by omega)

namespace UHomSeq

/-- Enable index notation `s[-]` to use the field `univMax_le`,
as well as the concrete value of `univMax`. -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| (
      have := Model.UnstructuredUniverse.UHomSeq.univMax_le ‹_›
      have that := this
      unfold SynthLean.univMax at that
      omega))

variable (s : UHomSeq Ctx)

instance : GetElem (UHomSeq Ctx) Nat (UnstructuredUniverse Ctx) (fun s i => i < s.length + 1) where
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
    {t : (Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s[i]'(ij.trans_lt jlen)).tp = A := by
  simp [unlift]

@[simp]
theorem unlift_lift {i j ij jlen Γ A}
    {t : (Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s.homOfLe i j).mapTm = t := by
  simp [unlift]

def unliftVar (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : (Γ) ⟶ (s[i]'(ij.trans_lt jlen)).Ty)
    {A' : (Γ) ⟶ s[j].Ty} (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    (s[j].ext A') ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  s.unlift i j ij jlen ((s[j].disp _) ≫ A) (s[j].var _) (by simp [eq])

@[simp]
theorem unliftVar_tp {i j ij jlen Γ A} {A' : (Γ) ⟶ s[j].Ty}
    (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    s.unliftVar i j ij jlen A eq ≫ (s[i]'(ij.trans_lt jlen)).tp = (s[j].disp _) ≫ A := by
  simp [unliftVar]

theorem substCons_unliftVar {i j ij jlen Γ A} {A' : (Γ) ⟶ s[j].Ty}
    {eq : A ≫ (s.homOfLe i j).mapTy = A'}
    {Δ} {σ : Δ ⟶ Γ} {t : (Δ) ⟶ _}
    (t_tp : t ≫ (s[i]'(ij.trans_lt jlen)).tp = (σ) ≫ A) :
    (s[j].substCons σ A' (t ≫ (s.homOfLe i j ij jlen).mapTm) (by
      simp [*]
      conv_lhs => rhs; apply (s.homOfLe i j).pb.w
      subst A'; rw [← Category.assoc, ← Category.assoc, ← t_tp]))
    ≫ s.unliftVar i j ij jlen A eq = t := by
  simp [unlift, unliftVar]; apply (s.homOfLe i j).pb.hom_ext <;> simp [*]

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
(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    (Γ) ⟶ s[i+1].Tm :=
  A ≫ (s.homSucc i).asTm

@[simp]
theorem code_tp {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    s.code ilen A ≫ s[i+1].tp = (s.homSucc i).wkU Γ := by
  simp [code, (s.homSucc i).U_pb.w, UHom.wkU]

@[reassoc]
theorem comp_code {Δ Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length)
    (σ : (Δ) ⟶ (Γ)) (A : (Γ) ⟶ s[i].Ty) :
    σ ≫ s.code ilen A = s.code ilen (σ ≫ A) := by
  simp [code]

/--
TODO: Consider generalising to just UHom?
Convert a a term of the `i`th universe (it is a `i+1` level term) into
a map into the `i`th type classifier.
It is the unique map into the pullback
             a
(Γ) -----------------¬
‖  -->          v     V
‖    s[i].Ty ----> s[i+1].Tm
‖         |          |
‖         |   p.b.   |
‖         |          |
‖         V          V
(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    (Γ) ⟶ s[i].Ty :=
  (s.homSucc i).U_pb.lift a (isTerminal.from (Γ)) (by rw [a_tp, UHom.wkU])

@[reassoc]
theorem comp_el (s : UHomSeq Ctx) {Δ Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (σ : (Δ) ⟶ (Γ)) (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    σ ≫ s.el ilen a a_tp = s.el ilen (σ ≫ a) (by simp [a_tp]) :=
  (s.homSucc i).U_pb.hom_ext (by simp [el]) (by simp)

@[simp]
lemma el_code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    el s ilen (code s ilen A) (code_tp _ _ _) = A :=
  (s.homSucc i).U_pb.hom_ext (by simp [el, code]) (by simp)

@[simp]
lemma code_el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    code s ilen (el s ilen a a_tp) = a := by
  simp [code, el]

/-! ## Pi -/

/-- `Pi` and `lam` formers at the `max` of any two universes.
This interprets
```
Γ ⊢ᵢ A type  Γ.A ⊢ⱼ B type
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B type
``` -/
class PiSeq (s : UHomSeq Ctx) where
  polyPi (s) (i j : Nat)
    -- Sadly, we have to spell out `ilen` and `jlen` due to
    -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
    (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) :
    PolymorphicPi s[i] s[j] s[max i j]

-- Re-export for use with dot notation.
abbrev polyPi := @PiSeq.polyPi

def PiSeq.ofMonomorphic
    (nmPi : (i : Nat) → (ilen : i < s.length + 1 := by get_elem_tactic) →
    s[i].PolymorphicPi s[i] s[i]) : PiSeq s where
  polyPi i j _ _ := .ofMonomorphic (nmPi (max i j)) (s.homOfLe _ _) (s.homOfLe _ _)

/-! ## Sigma -/

/-- `Sig` and `pair` formers at the `max` of any two universes. -/
class SigSeq (s : UHomSeq Ctx) where
  polySig (s) (i j : Nat)
    (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) :
    PolymorphicSigma s[i] s[j] s[max i j]

abbrev polySig := @SigSeq.polySig

/-! ## Identity types -/

/-- `Id` and `refl` formers at any universe,
together with identity elimination into any other universe. -/
class IdSeq (s : UHomSeq Ctx) where
  idIntro (s) (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
    PolymorphicIdIntro s[i] s[i]
  idElim (s) (i j : Nat)
    (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) :
    PolymorphicIdElim (idIntro i) s[j]

abbrev idIntro := @IdSeq.idIntro
abbrev idElim := @IdSeq.idElim
