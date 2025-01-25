import GroupoidModel.Russell_PER_MS.Lemmas
import GroupoidModel.Russell_PER_MS.UHom

import GroupoidModel.ForMathlib

universe v u

open CategoryTheory Limits

noncomputable section

namespace NaturalModelBase
namespace UHomSeq

variable {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞]

/-! ## Context stacks -/

/-- `s.CtxStack Γ` witnesses a sequence of context extension operations in `s`
that built the semantic context `Γ`. -/
inductive CtxStack (s : UHomSeq 𝒞) : 𝒞 → Type (max u v) where
  | nil : CtxStack s (⊤_ 𝒞)
  | cons {Γ} {l : Nat} (llen : l < s.length + 1) (A : y(Γ) ⟶ s[l].Ty) :
    CtxStack s Γ → CtxStack s (s[l].ext A)

variable {s : UHomSeq 𝒞}

protected def CtxStack.var {Γ : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.CtxStack Γ → ℕ → Part (y(Γ) ⟶ s[l].Tm)
  | .nil, _ => .none
  | .cons (l := l') _ A _, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].var A
  | .cons (l := l') _ A S, n+1 => do
    let v ← S.var llen n
    return ym(s[l'].disp A) ≫ v

/-- A "contextual" context (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the list `[Aₙ₋₁, …, A₀]`.

This kind of context can be destructured. -/
def CCtx (s : UHomSeq 𝒞) : Type (max u v) := Σ Γ : 𝒞, s.CtxStack Γ

def nilCCtx (s : UHomSeq 𝒞) : s.CCtx :=
  ⟨⊤_ 𝒞, .nil⟩

def CCtx.cons {l : Nat} (Γ : s.CCtx) (ilen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) : s.CCtx :=
  ⟨s[l].ext A, .cons ilen A Γ.2⟩

protected def CCtx.var {l : Nat} (Γ : s.CCtx) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Tm) :=
  Γ.2.var llen i

variable (slen : univMax ≤ s.length)

include slen in
theorem lt_slen_of_eqTp {Γ A B l} : Γ ⊢[l] A ≡ B → l < s.length + 1 := by
  intro Aeq
  have := Aeq.le_univMax
  omega

end UHomSeq

/-! ## Interpretation -/

namespace UHomSeqPis

variable {𝒞 : Type u} [SmallCategory 𝒞] [HasTerminal 𝒞]
  {s : UHomSeqPis 𝒞}

mutual

/- Recall: cannot have `ofCtx` appearing in the output types
(that would be induction-recursion or something like it),
thus the context must be an *input*. -/
def ofType (Γ : s.CCtx) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Ty)
  | .pi i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.cons ilen A) j B
    return lij ▸ s.mkPi ilen jlen A B
  | .univ i, _ =>
    Part.assert (l = i + 1) fun li => do
    return li ▸ (s.homSucc i).wkU Γ.1
  | .el t, _ => do
    Part.assert (l < s.length) fun llen => do
    let A ← ofTerm Γ (l+1) t
    Part.assert (A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1) fun A_tp => do
    return s.el llen A A_tp
  | _, _ => .none

def ofTerm (Γ : s.CCtx) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Tm)
  | .bvar i, llen => Γ.var llen i
  | .lam i j A e, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let e ← ofTerm (Γ.cons ilen A) j e
    return lij ▸ s.mkLam ilen jlen A e
  | .app i j B f a, _ => do
    Part.assert (l = j) fun lj => do
    Part.assert (i < s.length + 1) fun ilen => do
    have jlen : j < s.length + 1 := by omega
    let f ← ofTerm Γ (max i j) f
    let a ← ofTerm Γ i a
    let B ← ofType (Γ.cons ilen (a ≫ s[i].tp)) j B
    Part.assert (f ≫ s[max i j].tp = s.mkPi ilen jlen (a ≫ s[i].tp) B) fun h =>
    return lj ▸ s.mkApp ilen jlen _ B f h a rfl
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

def ofCtx (s : UHomSeqPis 𝒞) : Ctx → Part s.CCtx
  | [] => return s.nilCCtx
  | (A,l) :: Γ => do
    Part.assert (l < s.length + 1) fun llen => do
    let sΓ ← s.ofCtx Γ
    let sA ← ofType sΓ l A
    return sΓ.cons llen sA

theorem cons_mem_ofCtx {Γ A l llen sΓ sA} : sΓ ∈ s.ofCtx Γ → sA ∈ ofType sΓ l A llen →
    sΓ.cons llen sA ∈ s.ofCtx ((A,l) :: Γ) := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

theorem mem_var_of_lookup {Γ A i l llen sΓ sA} : Lookup Γ i A l →
    sΓ ∈ s.ofCtx Γ → sA ∈ ofType sΓ l A llen →
    ∃ sv, sv ∈ (sΓ.var llen i) ∧ sv ≫ s[l].tp = sA := by
  intro lk sΓmem sAmem
  induction lk
  . sorry
  . sorry

/-! ## Semantic substitution -/



theorem mem_ofType_inst {A B t l l' llen l'len} {sΓ sA sB st}
    (sA_mem : sA ∈ ofType sΓ l A llen)
    (st_mem : st ∈ ofTerm sΓ l t llen) (st_tp : st ≫ s[l].tp = sA)
    (sB_mem : sB ∈ ofType (sΓ.cons llen sA) l' B l'len) :
    s[l].inst sA sB st st_tp ∈ ofType sΓ l' (B.inst t) l'len := by
  sorry

theorem mem_ofTerm_inst {A B t a l l' llen l'len} {sΓ sA sB st sa}
    (sA_mem : sA ∈ ofType sΓ l A llen)
    (st_mem : st ∈ ofTerm sΓ l t llen) (st_tp : st ≫ s[l].tp = sA)
    (sB_mem : sB ∈ ofType (sΓ.cons llen sA) l' B l'len)
    (sa_mem : sa ∈ ofTerm (sΓ.cons llen sA) l' a l'len) (sa_tp : sa ≫ s[l'].tp = sB) :
    s[l].inst sA sa st st_tp ∈ ofTerm sΓ l' (a.inst t) l'len :=
  sorry

theorem mem_ofType_lift {A B l l' llen l'len} {sΓ sA sB}
    (sA_mem : sA ∈ ofType sΓ l A llen)
    (sB_mem : sB ∈ ofType sΓ l' B l'len) :
    (s[l']'l'len).wk sB sA ∈ ofType (sΓ.cons l'len sB) l (A.lift) llen :=
  sorry

theorem mem_ofType_liftN {A B l l' llen l'len n k} {sΓ sA sB}
    (sA_mem : sA ∈ ofType sΓ l A llen)
    (sB_mem : sB ∈ ofType sΓ l' B l'len) :
    -- TODO: semantic liftN
    (s[l']'l'len).wk sB sA ∈ ofType (sΓ.cons l'len sB) l (A.liftN n k) llen :=
  sorry

theorem mem_ofTerm_lift {B t l l' llen l'len} {sΓ sB st}
    (st_mem : st ∈ ofTerm sΓ l t llen)
    (sB_mem : sB ∈ ofType sΓ l' B l'len) :
    (s[l']'l'len).wk sB st ∈ ofTerm (sΓ.cons l'len sB) l (t.lift) llen :=
  sorry

/-! ## Soundness of interpretation -/

variable (slen : univMax ≤ s.length)

macro "simp_part" : tactic =>
  `(tactic| simp only [Part.mem_assert_iff, Part.mem_bind_iff, Part.mem_some_iff,
    exists_true_left, exists_const])
macro "simp_part" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [Part.mem_assert_iff, Part.mem_bind_iff, Part.mem_some_iff,
    exists_true_left, exists_const] $loc)

theorem mem_ofTerm_app {B f a} {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)
    {sΓ : s.CCtx} {sA : y(sΓ.1) ⟶ s[i].Ty} {sB : y((sΓ.cons ilen sA).1) ⟶ (s[j]'jlen).Ty}
    {sf : y(sΓ.1) ⟶ s[max i j].Tm} {sa : y(sΓ.1) ⟶ (s[i]'ilen).Tm}
    (sB_mem : sB ∈ ofType (sΓ.cons ilen sA) j B jlen)
    (sf_mem : sf ∈ ofTerm sΓ (max i j) f (by skip) /- wtf -/)
    (sf_tp : sf ≫ s[max i j].tp = s.mkPi ilen jlen sA sB)
    (sa_mem : sa ∈ ofTerm sΓ i a ilen)
    (sa_tp : sa ≫ s[i].tp = sA) :
    s.mkApp ilen jlen sA sB sf sf_tp sa sa_tp ∈ ofTerm sΓ j (.app i j B f a) jlen := by
  cases sa_tp
  dsimp [ofTerm]
  simp_part
  use ilen, sf, sf_mem, sa, sa_mem, sB, sB_mem, sf_tp

theorem mem_ofTerm_lam {A t} {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)
    {sΓ : s.CCtx} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {st : y((sΓ.cons ilen sA).1) ⟶ (s[j]'jlen).Tm}
    (sA_mem : sA ∈ ofType sΓ i A ilen)
    (st_mem : st ∈ ofTerm (sΓ.cons ilen sA) j t jlen) :
    s.mkLam ilen jlen sA st ∈ ofTerm sΓ (max i j) (.lam i j A t) (by skip) := by
  dsimp [ofTerm]
  simp_part
  use sA, sA_mem, st, st_mem

theorem mem_ofTerm_etaExpand {A B f} {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)
    {sΓ : s.CCtx} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.cons ilen sA).1) ⟶ (s[j]'jlen).Ty}
    {sf : y(sΓ.1) ⟶ s[max i j].Tm}
    (sA_mem : sA ∈ ofType sΓ i A ilen)
    (sB_mem : sB ∈ ofType (sΓ.cons ilen sA) j B jlen)
    (sf_mem : sf ∈ ofTerm sΓ (max i j) f (by skip) /- wtf -/)
    (sf_tp : sf ≫ s[max i j].tp = s.mkPi ilen jlen sA sB) :
    s.etaExpand ilen jlen sA sB sf sf_tp ∈
      ofTerm sΓ (max i j) (.lam i j A <| .app i j (B.liftN 1 1) f.lift (.bvar 0)) (by skip) := by
  dsimp [etaExpand]
  apply mem_ofTerm_lam ilen jlen sA_mem
  apply mem_ofTerm_app ilen jlen
  . -- TODO: mem_ofType_liftN
    sorry
  . exact mem_ofTerm_lift sf_mem sA_mem
  . dsimp [ofTerm, UHomSeq.CCtx.var, UHomSeq.CtxStack.var]
    simp

-- TODO: this proof is boring, repetitive exists-elim/exists-intro: automate!
theorem ofType_ofTerm_sound :
    (∀ {Γ l A B}, (Aeq : Γ ⊢[l] A ≡ B) → ∀ {sΓ}, sΓ ∈ ofCtx s Γ →
      have llen := s.lt_slen_of_eqTp slen Aeq
      ∃ sA ∈ ofType sΓ l A llen, sA ∈ ofType sΓ l B llen) ∧
    (∀ {Γ l t u A}, (teq : Γ ⊢[l] t ≡ u : A) → ∀ {sΓ}, sΓ ∈ ofCtx s Γ →
      have llen := s.lt_slen_of_eqTp slen teq.wf_tp
      ∃ sA ∈ ofType sΓ l A llen, ∃ st ∈ ofTerm sΓ l t llen,
        st ∈ ofTerm sΓ l u llen ∧ st ≫ s[l].tp = sA) := by

  have cons_helper {Γ A A' l sΓ} :
      (Aeq : Γ ⊢[l] A ≡ A') → sΓ ∈ ofCtx s Γ →
        have llen := s.lt_slen_of_eqTp slen Aeq
        ∀ {sA}, sA ∈ ofType sΓ l A llen → sΓ.cons llen sA ∈ ofCtx s ((A, l) :: Γ) :=
    fun Aeq sΓmem {sA} sAmem =>
      have llen := s.lt_slen_of_eqTp slen Aeq
      have sΓA := sΓ.cons llen sA
      cons_mem_ofCtx sΓmem sAmem

  refine
    ⟨@EqTp.rec (fun Γ l A B _ => _) (fun Γ l t u A _ => _)
      ?cong_pi ?cong_univ ?cong_el ?inst_tp ?symm_tp ?trans_tp ?cong_bvar ?cong_lam ?cong_app
      ?cong_code ?app_lam ?eta ?conv ?inst_tm ?symm_tm ?trans_tm,
    @EqTm.rec (fun Γ l A B _ => _) (fun Γ l t u A _ => _)
      ?cong_pi ?cong_univ ?cong_el ?inst_tp ?symm_tp ?trans_tp ?cong_bvar ?cong_lam ?cong_app
      ?cong_code ?app_lam ?eta ?conv ?inst_tm ?symm_tm ?trans_tm⟩

  case eta =>
    intros; intros
    rename_i l l' twf ihf _ sΓmem _
    have ⟨sAB, sABmem, sf, sfmem, sfmem', sftp⟩ := ihf sΓmem
    have maxlen := s.lt_slen_of_eqTp slen twf.wf_tp
    have llen : l < s.length + 1 := by omega
    have l'len : l' < s.length + 1 := by omega
    have sABmem_ := sABmem
    dsimp [ofType] at sABmem
    simp_part at sABmem
    have ⟨sA, sAmem, sB, sBmem, sABeq⟩ := sABmem
    refine ⟨sAB, sABmem_, ?_⟩
    refine ⟨s.etaExpand llen l'len sA sB sf (sABeq ▸ sftp), ?_, ?_, ?_⟩
    . rw [etaExpand_eq]; assumption
    . apply mem_ofTerm_etaExpand llen l'len sAmem sBmem sfmem (sABeq ▸ sftp)
    . rw [etaExpand_eq]; assumption

  all_goals intros; dsimp [ofType]; try intros
  case cong_pi Aeq Beq ihA ihB sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (cons_helper Aeq sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen Aeq
    have l'len := s.lt_slen_of_eqTp slen Beq
    use s.mkPi llen l'len sA sB
    simp_part
    constructor
    . use sA, sAmem, sB, sBmem
    . use sA, sAmem', sB, sBmem'
  case cong_univ => simp
  case cong_el Aeq ih _ sΓmem =>
    have ⟨sU, sUmem, sA, sAmem, sAmem', sAtp⟩ := ih sΓmem
    have llen := Nat.succ_lt_succ_iff.mp <| s.lt_slen_of_eqTp slen Aeq.wf_tp
    dsimp [ofType] at sUmem
    simp_part at sUmem
    use s.el llen sA (sUmem ▸ sAtp)
    simp_part
    simp only [llen, exists_true_left]
    exact ⟨⟨sA, sAmem, sAtp.trans sUmem, rfl⟩, sA, sAmem', sAtp.trans sUmem, rfl⟩
  case inst_tp teq ihB iht sΓ sΓmem =>
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := iht sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (cons_helper teq.wf_tp sΓmem sAmem)
    exact ⟨_, mem_ofType_inst sAmem stmem sttp sBmem, mem_ofType_inst sAmem stmem' sttp sBmem⟩
  case symm_tp ih _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    exact ⟨sA, sAmem', sAmem⟩ -- `use` fails here?
  case trans_tp ih ih' _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    have ⟨sA', sA'mem, sA'mem'⟩ := ih' sΓmem
    use sA, sAmem
    convert sA'mem'
    exact Part.mem_unique sAmem' sA'mem
  case cong_bvar lk ihA _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sv, svmem, svtp⟩ := mem_var_of_lookup lk sΓmem sAmem
    use sA, sAmem, sv, svmem, svmem, svtp
  case cong_lam Aeq teq ihA iht sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sB, sBmem, st, stmem, stmem', sttp⟩ := iht (cons_helper Aeq sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen Aeq
    have l'len := s.lt_slen_of_eqTp slen teq.wf_tp
    simp_part
    use s.mkPi llen l'len sA sB
    refine ⟨⟨sA, sAmem, sB, sBmem, rfl⟩,
      _, mem_ofTerm_lam llen l'len sAmem stmem,
      mem_ofTerm_lam llen l'len sAmem' stmem',
      ?_⟩
    simp [sttp]
  case cong_app Beq _ aeq ihB ihf iha _ sΓmem =>
    dsimp [ofTerm]
    have ⟨sA, sAmem, sa, samem, samem', satp⟩ := iha sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (cons_helper aeq.wf_tp sΓmem sAmem)
    have ⟨sAB, sABmem, sf, sfmem, sfmem', sftp⟩ := ihf sΓmem
    dsimp [ofType] at sABmem
    simp_part at sABmem
    have ⟨sA', sA'mem, sB', sB'mem, sABeq⟩ := sABmem
    cases Part.mem_unique sA'mem sAmem
    cases Part.mem_unique sB'mem sBmem
    cases sABeq
    cases satp
    have llen := s.lt_slen_of_eqTp slen aeq.wf_tp
    have l'len := s.lt_slen_of_eqTp slen Beq
    simp_part
    refine ⟨_, mem_ofType_inst sAmem samem rfl sBmem,
      s.mkApp llen l'len _ sB sf sftp sa rfl,
      ⟨llen, sf, sfmem, sa, samem, sB, sBmem, sftp, rfl⟩,
      ⟨llen, sf, sfmem', sa, samem', sB, sBmem', sftp, rfl⟩,
      ?_⟩
    simp
  case cong_code lMax Aeq ih _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    dsimp [ofTerm]
    simp_part
    have llen := lMax.trans_le slen
    refine ⟨_, rfl, s.code llen sA,
      ⟨Nat.succ_pos _, sA, sAmem, rfl⟩,
      ⟨Nat.succ_pos _, sA, sAmem', rfl⟩,
      ?_⟩
    erw [s.toUHomSeq.code_tp]
  case app_lam twf uwf iht ihu _ sΓmem =>
    have ⟨sA, sAmem, su, sumem, _, sutp⟩ := ihu sΓmem
    have ⟨sB, sBmem, st, stmem, _, sttp⟩ := iht (cons_helper uwf.wf_tp sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen uwf.wf_tp
    have l'len := s.lt_slen_of_eqTp slen twf.wf_tp
    refine ⟨_, mem_ofType_inst sAmem sumem sutp sBmem,
      _, mem_ofTerm_app llen l'len sBmem (mem_ofTerm_lam llen l'len sAmem stmem) ?_ sumem sutp,
      ?_, ?_⟩
    . simp [sttp]
    . rw [mkApp_mkLam (t_tp := sttp)]
      exact mem_ofTerm_inst sAmem sumem sutp sBmem stmem sttp
    . simp
  case conv ihA iht sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sA_, sAmem_, st, stmem, stmem', sttp⟩ := iht sΓmem
    use sA, sAmem', st, stmem, stmem'
    convert sttp
    exact Part.mem_unique sAmem sAmem_
  case inst_tm l _ _ teq iha iht sΓ sΓmem =>
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := iht sΓmem
    have ⟨sB, sBmem, sa, samem, samem', satp⟩ := iha (cons_helper teq.wf_tp sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen teq.wf_tp
    refine ⟨_, mem_ofType_inst sAmem stmem sttp sBmem, _,
      mem_ofTerm_inst sAmem stmem sttp sBmem samem satp,
      mem_ofTerm_inst sAmem stmem' sttp sBmem samem' satp,
      s[l].inst_tp sA sB sa satp st sttp⟩
  case symm_tm ih _ sΓmem =>
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := ih sΓmem
    use sA, sAmem, st, stmem', stmem, sttp
  case trans_tm ih ih' _ sΓmem =>
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := ih sΓmem
    have ⟨sA', sA'mem, st', st'mem, st'mem', st'tp⟩ := ih' sΓmem
    refine ⟨sA, sAmem, st, stmem, ?_, sttp⟩
    convert st'mem'
    exact Part.mem_unique stmem' st'mem

end UHomSeqPis
end NaturalModelBase
