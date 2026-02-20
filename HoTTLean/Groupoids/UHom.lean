import HoTTLean.Model.Unstructured.UHom
import HoTTLean.Groupoids.Pi
import HoTTLean.Groupoids.Id

noncomputable section

universe v u

namespace GroupoidModel

open Model.UnstructuredUniverse

def uHom : UHom U.{v, max u (v+2)} U.{v+1, max u (v+2)} :=
    @UHom.ofTyIsoExt _ _ _ _ _
    { mapTy := U.liftTy.{v,max u (v+2)}
      mapTm := U.liftTm
      pb := IsPullback.liftTm_isPullback }
    U.asSmallClosedType
    U.isoExtAsSmallClosedType.{v,u}

def uHomSeqHomSucc' (i : Nat) (h : i < 3) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => uHom.{0,4}
  | 1 => uHom.{1,4}
  | 2 => uHom.{2,4}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def uHomSeq : UHomSeq Ctx.{4} where
  length := 3
  univMax_le := by unfold SynthLean.univMax; omega
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

def uHomSeqMonomorphicPi (i : ℕ) (ilen : (i < 4)) :
    uHomSeq[i].PolymorphicPi uHomSeq[i] uHomSeq[i] :=
  match i with
  | 0 => UMonomorphicPi.{_,4}
  | 1 => UMonomorphicPi.{_,4}
  | 2 => UMonomorphicPi.{_,4}
  | 3 => UMonomorphicPi.{_,4}
  | (n+4) => by omega

instance : uHomSeq.PiSeq :=
  UHomSeq.PiSeq.ofMonomorphic _ uHomSeqMonomorphicPi

instance : uHomSeq.SigSeq where
  polySig
  | 0, 0, ilen, jlen => USig.{_,_,4}
  | 0, 1, ilen, jlen => USig.{_,_,4}
  | 0, 2, ilen, jlen => USig.{_,_,4}
  | 0, 3, ilen, jlen => USig.{_,_,4}
  | 1, 0, ilen, jlen => USig.{_,_,4}
  | 1, 1, ilen, jlen => USig.{_,_,4}
  | 1, 2, ilen, jlen => USig.{_,_,4}
  | 1, 3, ilen, jlen => USig.{_,_,4}
  | 2, 0, ilen, jlen => USig.{_,_,4}
  | 2, 1, ilen, jlen => USig.{_,_,4}
  | 2, 2, ilen, jlen => USig.{_,_,4}
  | 2, 3, ilen, jlen => USig.{_,_,4}
  | 3, 0, ilen, jlen => USig.{_,_,4}
  | 3, 1, ilen, jlen => USig.{_,_,4}
  | 3, 2, ilen, jlen => USig.{_,_,4}
  | 3, 3, ilen, jlen => USig.{_,_,4}
  | i, (j+4), ilen, jlen => by simp [uHomSeq] at jlen; omega
  | (i+4), j, ilen, jlen => by simp [uHomSeq] at ilen; omega

instance : uHomSeq.IdSeq where
  idIntro
  | 0, ilen => UPath.polymorphicIdIntro
  | 1, ilen => UPath.polymorphicIdIntro
  | 2, ilen => UPath.polymorphicIdIntro
  | 3, ilen => UPath.polymorphicIdIntro
  | (i+4), ilen => by simp [uHomSeq] at ilen; omega
  idElim
  | 0, 0, ilen, jlen => UId.{_,4}
  | 0, 1, ilen, jlen => UId.{_,4}
  | 0, 2, ilen, jlen => UId.{_,4}
  | 0, 3, ilen, jlen => UId.{_,4}
  | 1, 0, ilen, jlen => UId.{_,4}
  | 1, 1, ilen, jlen => UId.{_,4}
  | 1, 2, ilen, jlen => UId.{_,4}
  | 1, 3, ilen, jlen => UId.{_,4}
  | 2, 0, ilen, jlen => UId.{_,4}
  | 2, 1, ilen, jlen => UId.{_,4}
  | 2, 2, ilen, jlen => UId.{_,4}
  | 2, 3, ilen, jlen => UId.{_,4}
  | 3, 0, ilen, jlen => UId.{_,4}
  | 3, 1, ilen, jlen => UId.{_,4}
  | 3, 2, ilen, jlen => UId.{_,4}
  | 3, 3, ilen, jlen => UId.{_,4}
  | i, (j+4), ilen, jlen => by simp [uHomSeq] at jlen; omega
  | (i+4), j, ilen, jlen => by simp [uHomSeq] at ilen; omega
