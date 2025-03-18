import GroupoidModel.Russell_PER_MS.Lemmas
import GroupoidModel.Russell_PER_MS.UHom

import GroupoidModel.ForMathlib

macro "simp_part" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [
    Part.mem_assert_iff, Part.mem_bind_iff, Part.mem_map_iff,
    Part.pure_eq_some, Part.bind_eq_bind, Part.map_bind,
    Part.map_some, Part.mem_bind_iff, Part.mem_some_iff,
    exists_true_left, exists_const] $(loc)?)

universe v u

open CategoryTheory Limits


noncomputable section

namespace NaturalModelBase
namespace UHomSeq

variable {𝒞 : Type u} [SmallCategory 𝒞] [ChosenFiniteProducts 𝒞]

/-! ## Extension sequences -/

/-- `s.ExtSeq Γ Γ'` is a diff from the semantic context `Γ` to `Γ'`,
where `Γ` is a prefix of `Γ'`.
It witnesses a sequence of context extension operations in `s`
that built `Γ'` on top of `Γ`.
We write `Γ ≤ Γ'`. -/
inductive ExtSeq (s : UHomSeq 𝒞) (Γ : 𝒞) : 𝒞 → Type u where
  | nil : s.ExtSeq Γ Γ
  | snoc {Γ'} {l : Nat} (d : s.ExtSeq Γ Γ') (llen : l < s.length + 1) (A : y(Γ') ⟶ s[l].Ty) :
    s.ExtSeq Γ (s[l].ext A)

namespace ExtSeq

-- Q : What would a `Lookup` `Prop` family for `ExtSeq` look like?
-- The purpose of adding it would be to totalize `var`, `tp`, and other functions.

variable {s : UHomSeq 𝒞}

@[simp]
def length {Γ Γ' : 𝒞} : s.ExtSeq Γ Γ' → ℕ
  | nil => 0
  | snoc d _ _ => d.length + 1

@[simp]
def append {Γ₁ Γ₂ Γ₃ : 𝒞} : s.ExtSeq Γ₁ Γ₂ → s.ExtSeq Γ₂ Γ₃ → s.ExtSeq Γ₁ Γ₃
  | d, .nil           => d
  | d, .snoc e llen A => .snoc (d.append e) llen A

theorem append_assoc {Γ₁ Γ₂ Γ₃ Γ₄ : 𝒞}
    (d₁ : s.ExtSeq Γ₁ Γ₂) (d₂ : s.ExtSeq Γ₂ Γ₃) (d₃ : s.ExtSeq Γ₃ Γ₄) :
    d₁.append (d₂.append d₃) = (d₁.append d₂).append d₃ := by
  induction d₃ <;> simp [*]

/-- The composite display map associated to a sequence. -/
@[simp]
def disp {Γ Γ' : 𝒞} : s.ExtSeq Γ Γ' → (Γ' ⟶ Γ)
  | .nil => 𝟙 _
  | snoc (l := l) d _ A =>
    s[l].disp A ≫ d.disp

/-- Weaken a substitution and its domain by an extension sequence.
```
Δ ⊢ σ : Γ  d : Γ ≤ Γ'
-----------------------------
Δ ≤ Δ.d[σ]  Δ.d[σ] ⊢ σ.d : Γ'
```
where
```
Δ ⊢ σ : Γ  d : Γ ≤ Γ.Aₙ.….A₁
-----------------------------
Δ.d[σ] ≡ Δ.Aₙ[σ].….A₁[⋯]
```
-/
@[simp]
def substWk {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) : s.ExtSeq Γ Γ' → Σ (Δ' : 𝒞), s.ExtSeq Δ Δ' × (Δ' ⟶ Γ')
  | .nil => ⟨Δ, .nil, σ⟩
  | snoc (l := l) d llen A =>
    let ⟨Δ, d, σ⟩ := d.substWk σ
    ⟨s[l].ext (ym(σ) ≫ A), d.snoc llen (ym(σ) ≫ A), s[l].substWk σ A⟩

@[simp]
theorem substWk_length {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ') :
    (d.substWk σ).2.1.length = d.length := by
  induction d <;> simp [substWk, *]

theorem substWk_disp {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ') :
    (d.substWk σ).2.2 ≫ d.disp = (d.substWk σ).2.1.disp ≫ σ := by
  induction d generalizing σ <;> simp [substWk, *]

/-- `Γ.Aₖ.….A₀ ⊢ vₙ : Aₙ[↑ⁿ⁺¹]` -/
@[simp]
protected def var {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Tm)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].var A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.var llen n
    return s[l'].wk A v

/-- `Γ.Aₖ.….A₀ ⊢ Aₙ[↑ⁿ⁺¹]` -/
@[simp]
protected def tp {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Ty)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].wk A A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.tp llen n
    return s[l'].wk A v

theorem var_tp {Γ Γ' : 𝒞} {l : Nat} (d : s.ExtSeq Γ Γ') (llen : l < s.length + 1) (n : ℕ) :
    (d.var llen n).map (· ≫ s[l].tp) = d.tp llen n := by
  induction d generalizing n
  . simp [ExtSeq.var, ExtSeq.tp]
  next l' _ _ _ ih =>
    cases n
    . dsimp [ExtSeq.var, ExtSeq.tp]
      by_cases eq : l' = l
      . cases eq
        simp [Part.assert_pos rfl]
      . simp [Part.assert_neg eq]
    . simp [ExtSeq.var, ExtSeq.tp, ← ih, wk]

theorem var_eq_of_lt_length {l i} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' : 𝒞}
    (d : s.ExtSeq sΓ sΓ') (e : s.ExtSeq sΓ' sΓ'') :
    i < e.length → (d.append e).var llen i = e.var llen i := by
  induction e generalizing i with
  | nil => simp
  | snoc _ _ _ ih =>
    intro h
    cases i
    . simp
    . simp only [length, Nat.add_lt_add_iff_right] at h
      simp [ih h]

theorem var_append_add_length {l i} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' : 𝒞}
    (d : s.ExtSeq sΓ sΓ') (e : s.ExtSeq sΓ' sΓ'') :
    (d.append e).var llen (i + e.length) = (d.var llen i).map (ym(e.disp) ≫ ·) := by
  induction e <;> (simp [ExtSeq.var, Part.bind_some_eq_map, Part.map_map, wk, *]; rfl)

theorem var_substWk_add_length {l i} {llen : l < s.length + 1} {sΔ sΔ' sΓ sΓ' : 𝒞}
    (d : s.ExtSeq sΔ sΔ') (σ : sΔ' ⟶ sΓ) (e : s.ExtSeq sΓ sΓ') :
    let ⟨_, d', _⟩ := e.substWk σ
    (d.append d').var llen (i + e.length) = (d.var llen i).map (ym(d'.disp) ≫ ·) := by
  rw [← e.substWk_length σ]
  apply var_append_add_length

theorem var_substWk_of_lt_length {l i} {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ')
    (llen : l < s.length + 1) {st} (st_mem : st ∈ d.var llen i) :
    i < d.length → ym((substWk σ d).2.2) ≫ st ∈ (substWk σ d).2.1.var llen i := by
  induction d generalizing i with
  | nil => simp
  | snoc _ _ _ ih =>
    intro h
    cases i
    . clear ih
      dsimp [ExtSeq.var] at st_mem ⊢
      simp_part at st_mem ⊢
      obtain ⟨rfl, rfl⟩ := st_mem
      simp
    . simp only [length, Nat.add_lt_add_iff_right] at h
      dsimp [ExtSeq.var] at st_mem ⊢
      simp_part at st_mem ⊢
      obtain ⟨a, amem, rfl⟩ := st_mem
      refine ⟨_, ih amem h, ?_⟩
      simp only [wk, ← Functor.map_comp_assoc]
      simp

theorem mem_var_liftVar {l} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' sΘ : 𝒞}
    {st : y(sΓ'') ⟶ (s[l]'llen).Tm} (i)
    (c : s.ExtSeq sΓ sΓ') (d : s.ExtSeq sΓ' sΘ) (e : s.ExtSeq sΓ' sΓ'')
    (st_mem : st ∈ (c.append e).var llen i) :
    let ⟨_, d', σ⟩ := e.substWk d.disp
    ym(σ) ≫ st ∈ (c.append d |>.append d').var llen (liftVar d.length i e.length) := by
  by_cases ielen : i < e.length
  . simp only [liftVar, ielen, ↓reduceIte]
    rw [var_eq_of_lt_length _ _ ielen] at st_mem
    rw [var_eq_of_lt_length _ _ (substWk_length d.disp e ▸ ielen)]
    exact var_substWk_of_lt_length _ _ _ st_mem ielen
  . obtain ⟨k, rfl⟩ : ∃ k, i = k + e.length := Nat.exists_eq_add_of_le' (not_lt.mp ielen)
    rw [var_append_add_length] at st_mem
    simp only [liftVar, ielen, ↓reduceIte, ← add_assoc]
    rw [var_substWk_add_length, add_comm, var_append_add_length]
    simp_part at st_mem ⊢
    obtain ⟨st, stmem, rfl⟩ := st_mem
    refine ⟨ym(d.disp) ≫ st, ⟨st, stmem, rfl⟩, ?_⟩
    simp_rw [← Functor.map_comp_assoc, substWk_disp]

end ExtSeq

/-! ## Contextual objects -/

variable [HasTerminal 𝒞] {s : UHomSeq 𝒞}

-- Q: Should we get rid of `CObj` altogether, and generalize interpretation to `ExtSeq`s?
/-- A "contextual" object (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the extension sequence `[Aₙ₋₁ :: … :: A₀]`.

This kind of object can be destructured. -/
def CObj (s : UHomSeq 𝒞) : Type u := Σ Γ : 𝒞, s.ExtSeq (⊤_ 𝒞) Γ

def nilCObj (s : UHomSeq 𝒞) : s.CObj :=
  ⟨⊤_ 𝒞, .nil⟩

namespace CObj

@[simps]
def snoc {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) : s.CObj :=
  ⟨s[l].ext A, Γ.2.snoc llen A⟩

@[simps]
def append {sΓ' : 𝒞} (Γ : s.CObj) (d : s.ExtSeq Γ.1 sΓ') : s.CObj :=
  ⟨sΓ', Γ.2.append d⟩

@[simp]
theorem append_nil (Γ : s.CObj) : Γ.append .nil = Γ := by
  rfl

@[simp]
theorem append_snoc {sΓ' : 𝒞} {l} (Γ : s.CObj) (d : s.ExtSeq Γ.1 sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Γ.append (d.snoc llen A) = (Γ.append d).snoc llen A := by
  rfl

def substWk {sΓ sΓ' : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ') :
    Σ (Δ' : s.CObj), Δ'.1 ⟶ sΓ' :=
  let ⟨Δ', d', σ'⟩ := d.substWk σ
  ⟨⟨Δ', Δ.2.append d'⟩, σ'⟩

@[simp]
theorem substWk_nil {sΓ : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) :
    Δ.substWk σ .nil = ⟨Δ, σ⟩ := by
  rfl

theorem substWk_snoc {sΓ sΓ' : 𝒞} {l} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Δ.substWk σ (d.snoc llen A) =
      let ⟨Δ', σ'⟩ := Δ.substWk σ d
     ⟨Δ'.snoc llen (ym(σ') ≫ A), s[l].substWk σ' A⟩ := by
  rfl

protected def var {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Tm) :=
  Γ.2.var llen i

protected def tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Ty) :=
  Γ.2.tp llen i

theorem var_tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    (Γ.var llen i).map (· ≫ s[l].tp) = Γ.tp llen i :=
  Γ.2.var_tp llen i

theorem mem_var_liftVar {l} {llen : l < s.length + 1} {sΓ : s.CObj} {sΘ sΓ' : 𝒞}
    {st : y(sΓ') ⟶ (s[l]'llen).Tm} (i)
    (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
    (st_mem : st ∈ (sΓ.append e).var llen i) :
    let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
    ym(σ) ≫ st ∈ sΔ.var llen (liftVar d.length i e.length) :=
  ExtSeq.mem_var_liftVar _ sΓ.2 d e st_mem

end CObj

variable (slen : univMax ≤ s.length)

include slen in
omit [HasTerminal 𝒞] in
theorem lt_slen_of_eqTp {Γ A B l} : Γ ⊢[l] A ≡ B → l < s.length + 1 := by
  intro Aeq
  have := Aeq.le_univMax
  omega

end UHomSeq

/-! ## Interpretation -/

namespace UHomSeqPis

variable {𝒞 : Type u} [SmallCategory 𝒞] [ChosenFiniteProducts 𝒞] {s : UHomSeqPis 𝒞}

mutual

/- Recall: cannot have `ofCtx` appearing in the output types
(that would be induction-recursion or something like it),
thus the context must be an *input*. -/
def ofType (Γ : s.CObj) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Ty)
  | .pi i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
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

def ofTerm (Γ : s.CObj) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Tm)
  | .bvar i, llen => Γ.var llen i
  | .lam i j A e, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let e ← ofTerm (Γ.snoc ilen A) j e
    return lij ▸ s.mkLam ilen jlen A e
  | .app i j B f a, _ => do
    Part.assert (l = j) fun lj => do
    Part.assert (i < s.length + 1) fun ilen => do
    have jlen : j < s.length + 1 := by omega
    let f ← ofTerm Γ (max i j) f
    let a ← ofTerm Γ i a
    let B ← ofType (Γ.snoc ilen (a ≫ s[i].tp)) j B
    Part.assert (f ≫ s[max i j].tp = s.mkPi ilen jlen (a ≫ s[i].tp) B) fun h =>
    return lj ▸ s.mkApp ilen jlen _ B f h a rfl
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

def ofCtx (s : UHomSeqPis 𝒞) : Ctx → Part s.CObj
  | [] => return s.nilCObj
  | (A,l) :: Γ => do
    Part.assert (l < s.length + 1) fun llen => do
    let sΓ ← s.ofCtx Γ
    let sA ← ofType sΓ l A
    return sΓ.snoc llen sA

variable (slen : univMax ≤ s.length)

theorem snoc_mem_ofCtx {Γ A l llen sΓ sA} : sΓ ∈ s.ofCtx Γ → sA ∈ ofType sΓ l A llen →
    sΓ.snoc llen sA ∈ s.ofCtx ((A,l) :: Γ) := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

/-! ## Admissibility of thinning -/

mutual

theorem mem_ofType_liftN {A l llen} {sΓ : s.CObj} {sΘ sΓ' : 𝒞} {sA : y(sΓ') ⟶ (s[l]'llen).Ty}
    (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
    (sA_mem : sA ∈ ofType (sΓ.append e) l A llen) :
    let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
    ym(σ) ≫ sA ∈ ofType sΔ l (A.liftN d.length e.length) llen := by
  cases A <;> (
    dsimp [Expr.liftN, ofType] at sA_mem ⊢
    try simp_part at sA_mem ⊢)
  case univ =>
    rcases sA_mem with ⟨rfl, rfl⟩
    simp
  case pi _ _ A B =>
    rcases sA_mem with ⟨rfl, sA, sAmem, sB, sBmem, rfl⟩
    refine ⟨rfl,
      _, mem_ofType_liftN d e sAmem,
      _, mem_ofType_liftN d (e.snoc _ sA) sBmem,
      ?_⟩
    simp [comp_mkPi, UHomSeq.CObj.substWk]
  case el a =>
    obtain ⟨llen, sa, samem, satp, rfl⟩ := sA_mem
    refine ⟨llen,
      _, mem_ofTerm_liftN d e samem,
      ?_⟩
    simp [satp, UHomSeq.comp_el, UHomSeq.CObj.substWk]
  all_goals simp at sA_mem

theorem mem_ofTerm_liftN {t l llen} {sΓ : s.CObj} {sΘ sΓ' : 𝒞} {st : y(sΓ') ⟶ (s[l]'llen).Tm}
    (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
    (st_mem : st ∈ ofTerm (sΓ.append e) l t llen) :
    let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
    ym(σ) ≫ st ∈ ofTerm sΔ l (t.liftN d.length e.length) llen := by
  cases t <;> (
    dsimp [Expr.liftN, ofTerm] at st_mem ⊢
    try simp_part at st_mem ⊢)
  case bvar =>
    exact sΓ.mem_var_liftVar _ _ _ st_mem
  case app i j _ _ _ =>
    obtain ⟨rfl, ipos, sfn, sfnmem, sarg, sargmem, sB, sBmem, sfntp, rfl⟩ := st_mem
    refine ⟨rfl, ipos,
      _, mem_ofTerm_liftN d e sfnmem,
      _, mem_ofTerm_liftN d e sargmem,
      _, mem_ofType_liftN d (e.snoc _ <| sarg ≫ s[i].tp) sBmem,
      ?_⟩
    simp [sfntp, comp_mkPi, comp_mkApp]
    exact ⟨rfl, rfl⟩ -- TODO: why `simp` doesn't close! sides syntactically the same! !!!
  case lam =>
    obtain ⟨rfl, sA, sAmem, st, stmem, rfl⟩ := st_mem
    refine ⟨rfl,
      _, mem_ofType_liftN d e sAmem,
      _, mem_ofTerm_liftN d (e.snoc _ sA) stmem,
      ?_⟩
    simp [comp_mkLam, UHomSeq.CObj.substWk]
  case code =>
    obtain ⟨lpos, sA, sAmem, rfl⟩ := st_mem
    refine ⟨lpos, _, mem_ofType_liftN d e sAmem, ?_⟩
    rw [← UHomSeq.comp_code]
    -- `cast` removal
    generalize_proofs at *
    generalize h : l - 1 = k at *
    cases (by omega : k + 1 = l)
    simp [UHomSeq.CObj.substWk]
  all_goals simp at st_mem

end

theorem mem_ofType_lift {A l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sA} (sB : y(sΓ.1) ⟶ s[l'].Ty)
    (sA_mem : sA ∈ ofType sΓ l A llen) :
    (s[l']'l'len).wk sB sA ∈ ofType (sΓ.snoc l'len sB) l A.lift llen := by
  convert mem_ofType_liftN (UHomSeq.ExtSeq.nil.snoc l'len sB) .nil sA_mem using 1
  simp [wk, UHomSeq.ExtSeq.substWk, UHomSeq.ExtSeq.disp, UHomSeq.CObj.substWk]

theorem mem_ofTerm_lift {t l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {st} (sB : y(sΓ.1) ⟶ s[l'].Ty)
    (st_mem : st ∈ ofTerm sΓ l t llen) :
    (s[l']'l'len).wk sB st ∈ ofTerm (sΓ.snoc l'len sB) l t.lift llen := by
  convert mem_ofTerm_liftN (UHomSeq.ExtSeq.nil.snoc l'len sB) .nil st_mem using 1
  simp [wk, UHomSeq.ExtSeq.substWk, UHomSeq.ExtSeq.disp, UHomSeq.CObj.substWk]

/-! ## Admissibility of instantiation -/

theorem mem_ofTerm_instVar {a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sΓ' : 𝒞}
    {st : y(sΓ') ⟶ (s[l]'llen).Tm} {sa : y(sΓ.1) ⟶ (s[l']'l'len).Tm}
    (i)
    (sA : y(sΓ.1) ⟶ s[l'].Ty) (d : s.ExtSeq (s[l'].ext sA) sΓ')
    (st_mem : st ∈ (sΓ.snoc l'len sA |>.append d).var llen i)
    (sa_mem : sa ∈ ofTerm sΓ l' a l'len) (sa_tp : sa ≫ s[l'].tp = sA) :
    let σ := s[l'].substCons (𝟙 _) sA sa (by simpa using sa_tp)
    let ⟨sΔ, σ'⟩ := sΓ.substWk σ d
    ym(σ') ≫ st ∈ ofTerm sΔ l (instVar i a d.length) llen := by
  rcases i.lt_trichotomy d.length with ilen | rfl | ilen
  . simp only [instVar, ilen, ↓reduceIte, ofTerm,
      UHomSeq.CObj.var, UHomSeq.CObj.substWk, UHomSeq.CObj.append] at st_mem ⊢
    rw [UHomSeq.ExtSeq.var_eq_of_lt_length _ _ ilen] at st_mem
    rw [UHomSeq.ExtSeq.var_eq_of_lt_length]
    . exact UHomSeq.ExtSeq.var_substWk_of_lt_length _ d llen st_mem ilen
    . simp [ilen]
  . simp only [instVar, lt_self_iff_false, ↓reduceIte,
      UHomSeq.CObj.var, UHomSeq.CObj.append] at st_mem ⊢
    rw [show d.length = 0 + d.length by omega, UHomSeq.ExtSeq.var_append_add_length] at st_mem
    dsimp [UHomSeq.ExtSeq.var] at st_mem
    simp_part at st_mem
    obtain ⟨sa, ⟨rfl, rfl⟩, rfl⟩ := st_mem
    conv => enter [2]; dsimp [UHomSeq.CObj.substWk]
    rw [← Functor.map_comp_assoc, UHomSeq.ExtSeq.substWk_disp, Functor.map_comp_assoc]
    simp only [substCons_var]
    have := mem_ofTerm_liftN
       (d.substWk (s[l'].substCons (𝟙 sΓ.fst) sA sa (by simp [sa_tp]))).snd.1
      .nil sa_mem
    simp only [UHomSeq.CObj.substWk_nil, UHomSeq.CObj.append_fst, UHomSeq.ExtSeq.substWk_length,
      UHomSeq.ExtSeq.length] at this
    exact this
  . simp only [show ¬(i < d.length) by omega, show i ≠ d.length by omega,
      instVar, lt_self_iff_false, ↓reduceIte,
      UHomSeq.CObj.var, UHomSeq.CObj.append, ofTerm, UHomSeq.CObj.substWk] at st_mem ⊢
    obtain ⟨k, rfl⟩ : ∃ k, i = k + (d.length + 1) := Nat.exists_eq_add_of_le' (by omega)
    simp only [show k + (d.length + 1) = (k + 1) + d.length by omega,
      UHomSeq.ExtSeq.var_append_add_length, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var] at st_mem
    simp_part at st_mem
    obtain ⟨sv, svmem, rfl⟩ := st_mem
    rw [← Functor.map_comp_assoc, UHomSeq.ExtSeq.substWk_disp, Functor.map_comp_assoc]
    simp only [id_eq, eq_mpr_eq_cast, Nat.add_succ_sub_one, getElem_toUHomSeq, wk, ←
      Functor.map_comp_assoc, substCons_disp, CategoryTheory.Functor.map_id, Category.id_comp]
    have := sΓ.2.mem_var_liftVar
      k (UHomSeq.ExtSeq.substWk (s[l'].substCons (𝟙 sΓ.fst) sA sa (by simp [sa_tp])) d).snd.1 .nil
      svmem
    simp at this
    convert this using 2
    omega

-- TODO: the inductive cases here are literally the same as in `mem_ofType_liftN`.
-- Formalize this observation as an induction principle?
mutual

theorem mem_ofType_inst {B a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sΓ' : 𝒞} {sB : y(sΓ') ⟶ (s[l']'l'len).Ty} {sa : y(sΓ.1) ⟶ (s[l]'llen).Tm}
    (sA : y(sΓ.1) ⟶ s[l].Ty)
    (d : s.ExtSeq (sΓ.snoc llen sA).1 sΓ')
    (sB_mem : sB ∈ ofType ((sΓ.snoc llen sA).append d) l' B l'len)
    (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
    let σ := s[l].substCons (𝟙 _) sA sa (by simpa using sa_tp)
    let ⟨sΔ, σ'⟩ := sΓ.substWk σ d
    ym(σ') ≫ sB ∈ ofType sΔ l' (B.inst a d.length) l'len := by
  cases B <;> (
    dsimp [Expr.inst, ofType] at sB_mem ⊢
    try simp_part at sB_mem ⊢)
  case univ =>
    rcases sB_mem with ⟨rfl, rfl⟩
    simp
  case pi =>
    rcases sB_mem with ⟨rfl, sB, sBmem, sC, sCmem, rfl⟩
    refine ⟨rfl,
      _, mem_ofType_inst sA d sBmem sa_mem sa_tp,
      _, mem_ofType_inst sA (d.snoc _ sB) sCmem sa_mem sa_tp,
      ?_⟩
    simp [comp_mkPi, UHomSeq.CObj.substWk]
  case el =>
    obtain ⟨llen, sa, samem, satp, rfl⟩ := sB_mem
    refine ⟨llen,
      _, mem_ofTerm_inst sA d samem sa_mem sa_tp,
      ?_⟩
    simp [satp, UHomSeq.comp_el, UHomSeq.CObj.substWk]
  all_goals simp at sB_mem

theorem mem_ofTerm_inst {t a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sΓ' : 𝒞} {st : y(sΓ') ⟶ (s[l']'l'len).Tm} {sa : y(sΓ.1) ⟶ (s[l]'llen).Tm}
    (sA : y(sΓ.1) ⟶ s[l].Ty)
    (d : s.ExtSeq (sΓ.snoc llen sA).1 sΓ')
    (st_mem : st ∈ ofTerm ((sΓ.snoc llen sA).append d) l' t l'len)
    (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
    let σ := s[l].substCons (𝟙 _) sA sa (by simpa using sa_tp)
    let ⟨sΔ, σ'⟩ := sΓ.substWk σ d
    ym(σ') ≫ st ∈ ofTerm sΔ l' (t.inst a d.length) l'len := by
  cases t <;> (
    dsimp [Expr.inst, ofTerm] at st_mem ⊢
    try simp_part at st_mem ⊢)
  case bvar =>
    exact mem_ofTerm_instVar _ sA d st_mem sa_mem sa_tp
  case app i j _ _ _ =>
    obtain ⟨rfl, ipos, sfn, sfnmem, sarg, sargmem, sB, sBmem, sfntp, rfl⟩ := st_mem
    refine ⟨rfl, ipos,
      _, mem_ofTerm_inst sA d sfnmem sa_mem sa_tp,
      _, mem_ofTerm_inst sA d sargmem sa_mem sa_tp,
      _, mem_ofType_inst sA (d.snoc _ <| sarg ≫ s[i].tp) sBmem sa_mem sa_tp,
      ?_⟩
    simp [sfntp, comp_mkPi, comp_mkApp]
    exact ⟨rfl, rfl⟩ -- TODO: why `simp` doesn't close! sides syntactically the same! !!!
  case lam =>
    obtain ⟨rfl, sB, sBmem, st, stmem, rfl⟩ := st_mem
    refine ⟨rfl,
      _, mem_ofType_inst sA d sBmem sa_mem sa_tp,
      _, mem_ofTerm_inst sA (d.snoc _ sB) stmem sa_mem sa_tp,
      ?_⟩
    simp [comp_mkLam, UHomSeq.CObj.substWk]
  case code =>
    obtain ⟨lpos, sB, sBmem, rfl⟩ := st_mem
    refine ⟨lpos, _, mem_ofType_inst sA d sBmem sa_mem sa_tp, ?_⟩
    rw [← UHomSeq.comp_code]
    -- `cast` removal
    generalize_proofs at *
    generalize h : l' - 1 = k at *
    cases (by omega : k + 1 = l')
    simp [UHomSeq.CObj.substWk]
  all_goals simp at st_mem

end

theorem mem_ofType_inst0 {B a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sA sB sa}
    (sB_mem : sB ∈ ofType (sΓ.snoc llen sA) l' B l'len)
    (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
    s[l].inst sA sB sa sa_tp ∈ ofType sΓ l' (B.inst a) l'len :=
  mem_ofType_inst sA .nil sB_mem sa_mem sa_tp

theorem mem_ofTerm_inst0 {t a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
    {sΓ : s.CObj} {sA st sa}
    (st_mem : st ∈ ofTerm (sΓ.snoc llen sA) l' t l'len)
    (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
    s[l].inst sA st sa sa_tp ∈ ofTerm sΓ l' (t.inst a) l'len :=
  mem_ofTerm_inst sA .nil st_mem sa_mem sa_tp

/-! ## Soundness of interpretation -/

theorem mem_ofTerm_app {B f a} {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)
    {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ s[i].Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
    {sf : y(sΓ.1) ⟶ s[max i j].Tm} {sa : y(sΓ.1) ⟶ (s[i]'ilen).Tm}
    (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
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
    {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {st : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Tm}
    (sA_mem : sA ∈ ofType sΓ i A ilen)
    (st_mem : st ∈ ofTerm (sΓ.snoc ilen sA) j t jlen) :
    s.mkLam ilen jlen sA st ∈ ofTerm sΓ (max i j) (.lam i j A t) (by skip) := by
  dsimp [ofTerm]
  simp_part
  use sA, sA_mem, st, st_mem

theorem mem_ofTerm_etaExpand {A B f} {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)
    {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
    {sf : y(sΓ.1) ⟶ s[max i j].Tm}
    (sA_mem : sA ∈ ofType sΓ i A ilen)
    (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
    (sf_mem : sf ∈ ofTerm sΓ (max i j) f (by skip) /- wtf -/)
    (sf_tp : sf ≫ s[max i j].tp = s.mkPi ilen jlen sA sB) :
    s.etaExpand ilen jlen sA sB sf sf_tp ∈
      ofTerm sΓ (max i j) (.lam i j A <| .app i j (B.liftN 1 1) f.lift (.bvar 0)) (by skip) := by
  dsimp [etaExpand]
  apply mem_ofTerm_lam ilen jlen sA_mem
  apply mem_ofTerm_app ilen jlen
  . have := mem_ofType_liftN (UHomSeq.ExtSeq.nil.snoc _ sA) (UHomSeq.ExtSeq.nil.snoc _ sA) sB_mem
    dsimp at this
    convert this using 2 <;> congr <;> simp [UHomSeq.CObj.substWk, wk]
  . exact mem_ofTerm_lift _ sf_mem
  . dsimp [ofTerm, UHomSeq.CObj.var, UHomSeq.ExtSeq.var]
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

  have snoc_helper {Γ A A' l sΓ} :
      (Aeq : Γ ⊢[l] A ≡ A') → sΓ ∈ ofCtx s Γ →
        have llen := s.lt_slen_of_eqTp slen Aeq
        ∀ {sA}, sA ∈ ofType sΓ l A llen → sΓ.snoc llen sA ∈ ofCtx s ((A, l) :: Γ) :=
    fun Aeq sΓmem {sA} sAmem =>
      have llen := s.lt_slen_of_eqTp slen Aeq
      have sΓA := sΓ.snoc llen sA
      snoc_mem_ofCtx sΓmem sAmem

  refine
    ⟨@EqTp.rec (fun Γ l A B _ => _) (fun Γ l t u A _ => _)
      ?cong_pi ?cong_univ ?cong_el ?inst_tp ?lift_tp ?symm_tp ?trans_tp ?cong_bvar0 ?cong_lam ?cong_app
      ?cong_code ?app_lam ?eta ?conv ?inst_tm ?lift_tm ?symm_tm ?trans_tm,
    @EqTm.rec (fun Γ l A B _ => _) (fun Γ l t u A _ => _)
      ?cong_pi ?cong_univ ?cong_el ?inst_tp ?lift_tp ?symm_tp ?trans_tp ?cong_bvar0 ?cong_lam ?cong_app
      ?cong_code ?app_lam ?eta ?conv ?inst_tm ?lift_tm ?symm_tm ?trans_tm⟩

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
    have ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper Aeq sΓmem sAmem)
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
    have ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper teq.wf_tp sΓmem sAmem)
    exact ⟨_, mem_ofType_inst0 sBmem stmem sttp, mem_ofType_inst0 sBmem stmem' sttp⟩
  case lift_tp ih _ sΓmem =>
    dsimp [ofCtx] at sΓmem
    simp_part at sΓmem
    obtain ⟨_, _, sΓmem, sB, sBmem, rfl⟩ := sΓmem
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    exact ⟨_, mem_ofType_lift sB sAmem, mem_ofType_lift sB sAmem'⟩
  case symm_tp ih _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    exact ⟨sA, sAmem', sAmem⟩ -- `use` fails here?
  case trans_tp ih ih' _ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ih sΓmem
    have ⟨sA', sA'mem, sA'mem'⟩ := ih' sΓmem
    use sA, sAmem
    convert sA'mem'
    exact Part.mem_unique sAmem' sA'mem
  case cong_bvar0 lk ihA _ sΓmem =>
    dsimp [ofCtx, ofTerm] at sΓmem ⊢
    simp_part at sΓmem
    obtain ⟨_, sΓ, sΓmem, sA, sAmem, rfl⟩ := sΓmem
    dsimp [UHomSeq.CObj.var]
    simp_part
    exact ⟨_, mem_ofType_lift sA sAmem, _, rfl, rfl, by simp⟩
  case cong_lam Aeq teq ihA iht sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sB, sBmem, st, stmem, stmem', sttp⟩ := iht (snoc_helper Aeq sΓmem sAmem)
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
    obtain ⟨sA, sAmem, sa, samem, samem', rfl⟩ := iha sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper aeq.wf_tp sΓmem sAmem)
    have ⟨sAB, sABmem, sf, sfmem, sfmem', sftp⟩ := ihf sΓmem
    dsimp [ofType] at sABmem
    simp_part at sABmem
    obtain ⟨sA', sA'mem, sB', sB'mem, rfl⟩ := sABmem
    cases Part.mem_unique sA'mem sAmem
    cases Part.mem_unique sB'mem sBmem
    have llen := s.lt_slen_of_eqTp slen aeq.wf_tp
    have l'len := s.lt_slen_of_eqTp slen Beq
    simp_part
    refine ⟨_, mem_ofType_inst0 sBmem samem rfl,
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
    have ⟨sB, sBmem, st, stmem, _, sttp⟩ := iht (snoc_helper uwf.wf_tp sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen uwf.wf_tp
    have l'len := s.lt_slen_of_eqTp slen twf.wf_tp
    refine ⟨_, mem_ofType_inst0 sBmem sumem sutp,
      _, mem_ofTerm_app llen l'len sBmem (mem_ofTerm_lam llen l'len sAmem stmem) ?_ sumem sutp,
      ?_, ?_⟩
    . simp [sttp]
    . rw [mkApp_mkLam (t_tp := sttp)]
      exact mem_ofTerm_inst0 stmem sumem sutp
    . simp
  case conv ihA iht sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sA_, sAmem_, st, stmem, stmem', sttp⟩ := iht sΓmem
    use sA, sAmem', st, stmem, stmem'
    convert sttp
    exact Part.mem_unique sAmem sAmem_
  case inst_tm l _ _ teq iha iht sΓ sΓmem =>
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := iht sΓmem
    have ⟨sB, sBmem, sa, samem, samem', satp⟩ := iha (snoc_helper teq.wf_tp sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen teq.wf_tp
    refine ⟨_, mem_ofType_inst0 sBmem stmem sttp, _,
      mem_ofTerm_inst0 samem stmem sttp,
      mem_ofTerm_inst0 samem' stmem' sttp,
      s[l].inst_tp sA sB sa satp st sttp⟩
  case lift_tm ih _ sΓmem =>
    dsimp [ofCtx] at sΓmem
    simp_part at sΓmem
    obtain ⟨_, _, sΓmem, sB, sBmem, rfl⟩ := sΓmem
    have ⟨sA, sAmem, st, stmem, stmem', sttp⟩ := ih sΓmem
    refine ⟨_, mem_ofType_lift sB sAmem,
      _, mem_ofTerm_lift sB stmem, mem_ofTerm_lift sB stmem',
      ?_⟩
    simp [← sttp, wk]
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
