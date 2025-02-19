import GroupoidModel.Russell_PER_MS.NaturalModelBase
import GroupoidModel.ForMathlib

/-! Morphisms of natural models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Limits Opposite

namespace NaturalModelBase

variable {Ctx : Type u} [Category.{v, u} Ctx]

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

/-- A Russell embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `UHom.id M` is essentially `Type : Type` in `M`. -/
structure UHom (M N : NaturalModelBase Ctx) extends Hom M N where
  U : ⊤_ (Psh Ctx) ⟶ N.Ty
  U_pb : ∃ v, IsPullback v (terminal.from M.Ty) N.tp U

  -- Or an explicit bijection:
  -- U_equiv : (y(⊤_ Ctx) ⟶ M.Ty) ≃ { A : y(⊤_ Ctx) ⟶ N.Tm // A ≫ N.tp = U }

def UHom.comp {M N O : NaturalModelBase Ctx} (α : UHom M N) (β : UHom N O) : UHom M O := {
  Hom.comp α.toHom β.toHom with
  U := α.U ≫ β.mapTy
  U_pb :=
    have ⟨v, pb⟩ := α.U_pb
    ⟨v ≫ β.mapTm, pb.paste_horiz β.pb⟩
}

def UHom.comp_assoc {M N O P : NaturalModelBase Ctx} (α : UHom M N) (β : UHom N O) (γ : UHom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def UHom.wkU {M N : NaturalModelBase Ctx} (Γ : Ctx) (α : UHom M N) : y(Γ) ⟶ N.Ty :=
  terminal.from y(Γ) ≫ α.U

@[reassoc (attr := simp)]
theorem UHom.comp_wkU {M N : NaturalModelBase Ctx} {Δ Γ : Ctx} (α : UHom M N) (f : y(Δ) ⟶ y(Γ)) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `UHom` into a natural model with a Tarski universe. -/
def UHom.ofTarskiU [HasTerminal Ctx] (M : NaturalModelBase Ctx)
    (U : y(⊤_ Ctx) ⟶ M.Ty) (El : y(M.ext U) ⟶ M.Ty) :
    UHom (M.pullback El) M := {
  M.pullbackHom El with
  U := (PreservesTerminal.iso (yoneda (C := Ctx))).inv ≫ U
  U_pb := ⟨M.var U,
    (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (PreservesTerminal.iso (yoneda (C := Ctx)))
      (Iso.refl _)
      (by simp) (terminal.hom_ext ..)
      (by simp) (by rw [Iso.hom_inv_id_assoc]; simp)⟩
}

/-- A sequence of Russell embeddings. -/
structure UHomSeq (Ctx : Type u) [Category.{v, u} Ctx] where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs (i : Nat) (h : i < length + 1) : NaturalModelBase Ctx
  homSucc' (i : Nat) (h : i < length) : UHom (objs i <| by omega) (objs (i + 1) <| by omega)

namespace UHomSeq

instance : GetElem (UHomSeq Ctx) Nat (NaturalModelBase Ctx) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs i h

def homSucc (s : UHomSeq Ctx) (i : Nat) (h : i < s.length := by get_elem_tactic) : UHom s[i] s[i+1] :=
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

def code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : y(Γ) ⟶ s[i].Ty) :
    y(Γ) ⟶ s[i+1].Tm :=
  sorry

@[simp]
theorem code_tp {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : y(Γ) ⟶ s[i].Ty) :
    s.code ilen A ≫ s[i+1].tp = (s.homSucc i).wkU Γ :=
  sorry

theorem comp_code {Δ Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length)
    (σ : y(Δ) ⟶ y(Γ)) (A : y(Γ) ⟶ s[i].Ty) :
    σ ≫ s.code ilen A = s.code ilen (σ ≫ A) := by
  sorry

def el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : y(Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    y(Γ) ⟶ s[i].Ty :=
  sorry

theorem comp_el (s : UHomSeq Ctx) {Δ Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (σ : y(Δ) ⟶ y(Γ)) (a : y(Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    σ ≫ s.el ilen a a_tp = s.el ilen (σ ≫ a) (by simp [a_tp]) := by
  sorry

-- code_el A = A
-- el_code A = A

end UHomSeq

/-- The data of Π and λ term formers for every `i, j ≤ length + 1`, interpreting
```
Γ ⊢ᵢ A type  Γ.A ⊢ⱼ B type
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B type
```
and
```
Γ ⊢ᵢ A type  Γ.A ⊢ⱼ t : B
-------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. t : ΠA. B
```

This amounts to `O(length²)` data.
One might object that the same formation rules could be modeled with `O(length)` data:
etc etc

However, with `O(length²)` data we can use Lean's own type formers directly,
rather than using `Π (ULift A) (ULift B)`.
The interpretations of types are thus more direct. -/
structure UHomSeqPis (Ctx : Type u) [SmallCategory.{u} Ctx] extends UHomSeq Ctx where
  Pis' (i : Nat) (ilen : i < length + 1) :
    toUHomSeq[i].Ptp.obj toUHomSeq[i].Ty ⟶ toUHomSeq[i].Ty
  lams' (i : Nat) (ilen : i < length + 1) :
    toUHomSeq[i].Ptp.obj toUHomSeq[i].Tm  ⟶ toUHomSeq[i].Tm
  Pi_pbs' (i : Nat) (ilen : i < length + 1) :
    IsPullback (lams' i ilen) (toUHomSeq[i].Ptp.map toUHomSeq[i].tp) toUHomSeq[i].tp (Pis' i ilen)

namespace UHomSeqPis

variable {Ctx : Type u} [SmallCategory.{u} Ctx]

instance : GetElem (UHomSeqPis Ctx) Nat (NaturalModelBase Ctx) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs i h

variable (s : UHomSeqPis Ctx)

@[simp]
theorem getElem_toUHomSeq (i : Nat) (ilen : i < s.length + 1) : s.toUHomSeq[i] = s[i] := by
  rfl

def Pis (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
    s[i].Ptp.obj s[i].Ty ⟶ s[i].Ty :=
  s.Pis' i ilen

def lams (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
    s[i].Ptp.obj s[i].Tm ⟶ s[i].Tm :=
  s.lams' i ilen

def Pi_pbs (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
    IsPullback (s.lams i) (s[i].Ptp.map s[i].tp) s[i].tp (s.Pis i) :=
  s.Pi_pbs' i ilen

-- Sadly, we have to spell out `ilen` and `jlen` due to
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
variable {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)

def PisPoly : s[i].Ptp.obj s[j].Ty ⟶ s[max i j].Ty :=
  sorry ≫ s.Pis (max i j)

def lamsPoly : s[i].Ptp.obj s[j].Tm ⟶ s[max i j].Tm :=
  sorry

def PisPoly_pbs :
    IsPullback (s.lamsPoly ilen jlen) (s[i].Ptp.map s[j].tp) s[max i j].tp (s.PisPoly ilen jlen) :=
  sorry

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ B
-----------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B
``` -/
def mkPi {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty) : y(Γ) ⟶ s[max i j].Ty :=
  s[i].Ptp_equiv ⟨A, B⟩ ≫ s.PisPoly ilen jlen

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
  s[i].Ptp_equiv ⟨A, t⟩ ≫ s.lamsPoly ilen jlen

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (t : y(s[i].ext A) ⟶ s[j].Tm) (t_tp : t ≫ s[j].tp = B) :
    s.mkLam ilen jlen A t ≫ s[max i j].tp = s.mkPi ilen jlen A B := by
  simp [mkLam, mkPi, (s.PisPoly_pbs ilen jlen).w, s[i].Ptp_equiv_naturality_assoc, t_tp]

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
    (s.PisPoly_pbs ilen jlen).lift f (s[i].Ptp_equiv ⟨A, B⟩) f_tp
  -- bug: `get_elem_tactic` fails on `i` with
  -- convert (s[i].Ptp_equiv.symm total).snd
  let this := s[i].Ptp_equiv.symm total
  convert this.snd
  have eq : total ≫ s[i].Ptp.map s[j].tp = s[i].Ptp_equiv ⟨A, B⟩ :=
    (s.PisPoly_pbs ilen jlen).isLimit.fac _ (some .right)
  simpa [s[i].Ptp_equiv_symm_naturality] using (s[i].Ptp_ext.mp eq).left.symm

@[simp]
theorem unLam_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B) :
    s.unLam ilen jlen A B f f_tp ≫ s[j].tp = B := by
  -- This proof is `s[i].Ptp_equiv_symm_naturality`, `IsPullback.lift_snd`, and ITT gunk.
  dsimp only [unLam]
  sorry
  -- generalize_proofs _ pf pf'
  -- have := pf.lift_snd f (s[i].Ptp_equiv ⟨A, B⟩) f_tp
  -- generalize pf.lift f (s[i].Ptp_equiv ⟨A, B⟩) f_tp = x at this pf'
  -- have := congrArg s[i].Ptp_equiv.symm this
  -- simp only [s[i].Ptp_equiv_symm_naturality, Equiv.symm_apply_apply, Sigma.mk.inj_iff] at this
  -- cases this.left
  -- simp [← eq_of_heq this.right]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B  Γ ⊢ᵢ a : A
---------------------------------
Γ ⊢ⱼ f a : B[id.a]
``` -/
def mkApp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) : y(Γ) ⟶ s[j].Tm :=
  s[i].inst A (s.unLam ilen jlen A B f f_tp) a a_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : y(Γ) ⟶ s[i].Ty) (B : y(s[i].ext A) ⟶ s[j].Ty)
    (f : y(Γ) ⟶ s[max i j].Tm) (f_tp : f ≫ s[max i j].tp = s.mkPi ilen jlen A B)
    (a : y(Γ) ⟶ s[i].Tm) (a_tp : a ≫ s[i].tp = A) :
    s.mkApp ilen jlen A B f f_tp a a_tp ≫ s[j].tp = s[i].inst A B a a_tp := by
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
      (s[i].wk A A) (ym(s[i].substWk ..) ≫ B) (s[i].wk A f) (by
        simp_rw [wk_tp, f_tp, wk, comp_mkPi]
        )
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
    -- Q: should `inst ..` be the simp-NF, or should the more basic `σ ≫ _`?
    s.mkApp ilen jlen A B (s.mkLam ilen jlen A t) lam_tp a a_tp = s[i].inst A t a a_tp := by
  rw [mkApp, unLam_mkLam]
  assumption

end UHomSeqPis
