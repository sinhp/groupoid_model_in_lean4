import GroupoidModel.Russell_PER_MS.NaturalModelBase

/-! Morphisms of natural models, and Russell-universe embeddings. -/

universe u

noncomputable section

open CategoryTheory Limits Opposite

namespace NaturalModelBase

variable {Ctx : Type u} [Category Ctx]

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
structure UHomSeq (Ctx : Type u) [Category Ctx] where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs : Fin (length + 1) → NaturalModelBase Ctx
  homs : (i : Fin length) → UHom (objs i.castSucc) (objs i.succ)

namespace UHomSeq

instance : GetElem (UHomSeq Ctx) Nat (NaturalModelBase Ctx) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs ⟨i, h⟩

/-- Composition of embeddings between `i` and `j` in the chain. -/
def hom (s : UHomSeq Ctx) (i j : Fin s.length) (ij : i < j) : UHom s[i] s[j] :=
  if h : i.val + 1 = j.val then
    cast (by congr 2; exact Fin.eq_mk_iff_val_eq.mpr h) <| s.homs i
  else
    (s.homs i).comp <| s.hom ⟨i + 1, by omega⟩ j (by apply Fin.mk_lt_of_lt_val; omega)
termination_by s.length - i

theorem comp_hom_trans (s : UHomSeq Ctx) (i j k : Fin s.length) (ij : i < j) (jk : j < k) :
    (s.hom i j ij).comp (s.hom j k jk) = s.hom i k (ij.trans jk) := by
  conv_rhs => unfold hom
  conv in s.hom i j _ => unfold hom
  split_ifs
  all_goals try omega
  . rename_i h _
    cases j; cases h
    simp
  . rw [UHom.comp_assoc, comp_hom_trans]
termination_by s.length - i

end UHomSeq
