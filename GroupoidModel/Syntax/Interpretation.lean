import GroupoidModel.Syntax.Inversion
import GroupoidModel.Syntax.UHom

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

variable {𝒞 : Type u} [SmallCategory 𝒞] [CartesianMonoidalCategory 𝒞]

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

@[functor_map (attr := reassoc)]
theorem substWk_disp {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ') :
    (d.substWk σ).2.2 ≫ d.disp = (d.substWk σ).2.1.disp ≫ σ := by
  induction d generalizing σ <;> simp [substWk, NaturalModelBase.substWk_disp_assoc, *]

/-- `Γ.Aₖ.….A₀ ⊢ vₙ : Aₙ[↑ⁿ⁺¹]` -/
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
    . simp [ExtSeq.var]
    . simp only [length, Nat.add_lt_add_iff_right] at h
      simp [ExtSeq.var, ih h]

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
      simp [NaturalModelBase.substWk_disp]

-- theorem mem_var_liftVar {l} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' sΘ : 𝒞}
--     {st : y(sΓ'') ⟶ (s[l]'llen).Tm} (i)
--     (c : s.ExtSeq sΓ sΓ') (d : s.ExtSeq sΓ' sΘ) (e : s.ExtSeq sΓ' sΓ'')
--     (st_mem : st ∈ (c.append e).var llen i) :
--     let ⟨_, d', σ⟩ := e.substWk d.disp
--     ym(σ) ≫ st ∈ (c.append d |>.append d').var llen (liftVar d.length i e.length) := by
--   by_cases ielen : i < e.length
--   . simp only [liftVar, ielen, ↓reduceIte]
--     rw [var_eq_of_lt_length _ _ ielen] at st_mem
--     rw [var_eq_of_lt_length _ _ (substWk_length d.disp e ▸ ielen)]
--     exact var_substWk_of_lt_length _ _ _ st_mem ielen
--   . obtain ⟨k, rfl⟩ : ∃ k, i = k + e.length := Nat.exists_eq_add_of_le' (not_lt.mp ielen)
--     rw [var_append_add_length] at st_mem
--     simp only [liftVar, ielen, ↓reduceIte, ← add_assoc]
--     rw [var_substWk_add_length, add_comm, var_append_add_length]
--     simp_part at st_mem ⊢
--     obtain ⟨st, stmem, rfl⟩ := st_mem
--     refine ⟨ym(d.disp) ≫ st, ⟨st, stmem, rfl⟩, ?_⟩
--     simp_rw [← Functor.map_comp_assoc, substWk_disp]

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
theorem append_nil (Γ : s.CObj) : Γ.append .nil = Γ := rfl

@[simp]
theorem append_snoc {sΓ' : 𝒞} {l} (Γ : s.CObj) (d : s.ExtSeq Γ.1 sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Γ.append (d.snoc llen A) = (Γ.append d).snoc llen A := rfl

def substWk {sΓ sΓ' : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ') :
    Σ (Δ' : s.CObj), Δ'.1 ⟶ sΓ' :=
  let ⟨Δ', d', σ'⟩ := d.substWk σ
  ⟨⟨Δ', Δ.2.append d'⟩, σ'⟩

@[simp]
theorem substWk_nil {sΓ : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) :
    Δ.substWk σ .nil = ⟨Δ, σ⟩ := rfl

theorem substWk_snoc {sΓ sΓ' : 𝒞} {l} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Δ.substWk σ (d.snoc llen A) =
      let ⟨Δ', σ'⟩ := Δ.substWk σ d
     ⟨Δ'.snoc llen (ym(σ') ≫ A), s[l].substWk σ' A⟩ := rfl

protected def var {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Tm) :=
  Γ.2.var llen i

protected def tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Ty) :=
  Γ.2.tp llen i

theorem var_tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    (Γ.var llen i).map (· ≫ s[l].tp) = Γ.tp llen i :=
  Γ.2.var_tp llen i

-- theorem mem_var_liftVar {l} {llen : l < s.length + 1} {sΓ : s.CObj} {sΘ sΓ' : 𝒞}
--     {st : y(sΓ') ⟶ (s[l]'llen).Tm} (i)
--     (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
--     (st_mem : st ∈ (sΓ.append e).var llen i) :
--     let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
--     ym(σ) ≫ st ∈ sΔ.var llen (liftVar d.length i e.length) :=
--   ExtSeq.mem_var_liftVar _ sΓ.2 d e st_mem

end CObj

variable (slen : univMax ≤ s.length)

section
include slen

omit [HasTerminal 𝒞] in
theorem lt_slen_of_eqTp {Γ A B l} : Γ ⊢[l] A ≡ B → l < s.length + 1 := by
  intro Aeq
  have := Aeq.le_univMax
  omega

omit [HasTerminal 𝒞] in
theorem lt_slen_of_wfTp {Γ A l} (H : Γ ⊢[l] A) : l < s.length + 1 :=
  lt_slen_of_eqTp slen (.refl_tp H)

omit [HasTerminal 𝒞] in
theorem lt_slen_of_wfTm {Γ t A l} (H : Γ ⊢[l] t : A) : l < s.length + 1 :=
  lt_slen_of_wfTp slen H.wf_tp

omit [HasTerminal 𝒞] in
theorem lt_slen_of_eqTm {Γ t u A l} (H : Γ ⊢[l] t ≡ u : A) : l < s.length + 1 :=
  lt_slen_of_wfTp slen H.wf_tp

end

end UHomSeq

/-! ## Interpretation -/

namespace UHomSeqPiSigma

variable {𝒞 : Type u} [SmallCategory 𝒞] [CartesianMonoidalCategory 𝒞] {s : UHomSeqPiSigma 𝒞}

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
  | .sigma i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
    return lij ▸ s.mkSigma ilen jlen A B
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
  | .pair i j B t u, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let t ← ofTerm Γ i t
    let B ← ofType (Γ.snoc ilen (t ≫ s[i].tp)) j B
    let u ← ofTerm Γ j u
    Part.assert (u ≫ s[j].tp = ym(s[i].sec _ t rfl) ≫ B) fun u_tp =>
    return lij ▸ s.mkPair ilen jlen (t ≫ s[i].tp) B t rfl u u_tp
  | .fst i j A B p, _ => do
    Part.assert (l = i) fun li => do
    have ilen : i < s.length + 1 := by omega
    Part.assert (j < s.length + 1) fun jlen => do
    -- RB was so right
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
    let p ← ofTerm Γ (max i j) p
    Part.assert (p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) fun p_tp =>
    return li ▸ s.mkFst ilen jlen A B p p_tp
  | .snd i j A B p, _ => do
    Part.assert (l = j) fun lj => do
    have jlen : j < s.length + 1 := by omega
    Part.assert (i < s.length + 1) fun ilen => do
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
    let p ← ofTerm Γ (max i j) p
    Part.assert (p ≫ s[max i j].tp = s.mkSigma ilen jlen A B) fun p_tp =>
    return lj ▸ s.mkSnd ilen jlen A B p p_tp
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

def ofCtx (s : UHomSeqPiSigma 𝒞) : Ctx → Part s.CObj
  | [] => return s.nilCObj
  | (A,l) :: Γ => do
    Part.assert (l < s.length + 1) fun llen => do
    let sΓ ← s.ofCtx Γ
    let sA ← ofType sΓ l A
    return sΓ.snoc llen sA

@[simp]
theorem mem_ofType_pi {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.pi i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ s.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkPi ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_sigma {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.sigma i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ s.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkSigma ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_el {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.el t) llen ↔
    ∃ llen : l < s.length,
    ∃ A : y(Γ.1) ⟶ s[l+1].Tm, A ∈ ofTerm Γ (l+1) t ∧
    ∃ A_tp : A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1,
    x = s.el llen A A_tp := by
  dsimp only [ofType]; simp_part

@[simp]
theorem ofTerm_bvar {Γ l i} {llen : l < s.length + 1} :
    s.ofTerm Γ l (.bvar i) llen = Γ.var llen i := rfl

@[simp]
theorem mem_var_zero {Γ : s.CObj} {l' l'len A l} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen 0 ↔
    ∃ l'l : l' = l, x = l'l ▸ s[l'].var A := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part; exact exists_congr fun _ => by subst l'; simp_part; rfl

@[simp]
theorem mem_var_succ {Γ : s.CObj} {l' l'len A l i} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen (i+1) ↔
    ∃ a ∈ Γ.var llen i, x = s[l'].wk A a := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part; rfl

@[simp]
theorem mem_ofTerm_lam {Γ l i j A e} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.lam i j A e) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    ∃ (A' : y(Γ.1) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (e' : y((Γ.snoc ilen A').1) ⟶ s[j].Tm), e' ∈ s.ofTerm (Γ.snoc ilen A') j e ∧
    x = lij ▸ s.mkLam ilen jlen A' e' := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_app {Γ l i j B f a} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.app i j B f a) llen ↔
    ∃ lj : l = j,
    ∃ ilen : i < s.length + 1,
    have jlen : j < s.length + 1 := by omega
    ∃ f' : y(Γ.1) ⟶ s[max i j].Tm, f' ∈ ofTerm Γ (max i j) f ∧
    ∃ a' : y(Γ.1) ⟶ s[i].Tm, a' ∈ ofTerm Γ i a ∧
    ∃ B' : y((Γ.snoc ilen (a' ≫ s[i].tp)).1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc ilen (a' ≫ s[i].tp)) j B ∧
    ∃ h, x = lj ▸ s.mkApp ilen jlen _ B' f' h a' rfl := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_pair {Γ l i j B t u} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.pair i j B t u) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    ∃ t' : y(Γ.1) ⟶ s[i].Tm, t' ∈ ofTerm Γ i t ∧
    ∃ B' : y((Γ.snoc ilen (t' ≫ s[i].tp)).1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc ilen (t' ≫ s[i].tp)) j B ∧
    ∃ u' : y(Γ.1) ⟶ s[j].Tm, u' ∈ ofTerm Γ j u ∧
    ∃ u_tp : u' ≫ s[j].tp = ym(s[i].sec _ t' rfl) ≫ B',
    x = lij ▸ s.mkPair ilen jlen (t' ≫ s[i].tp) B' t' rfl u' u_tp := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_fst {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.fst i j A B p) llen ↔
    ∃ li : l = i,
    have ilen : i < s.length + 1 := by omega
    ∃ jlen : j < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc ilen A') j B ∧
    ∃ p' : y(Γ.1) ⟶ s[max i j].Tm, p' ∈ ofTerm Γ (max i j) p ∧
    ∃ p_tp : p' ≫ s[max i j].tp = s.mkSigma ilen jlen A' B',
    x = li ▸ s.mkFst ilen jlen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_snd {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.snd i j A B p) llen ↔
    ∃ lj : l = j,
    have jlen : j < s.length + 1 := by omega
    ∃ ilen : i < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc ilen A') j B ∧
    ∃ p' : y(Γ.1) ⟶ s[max i j].Tm, p' ∈ ofTerm Γ (max i j) p ∧
    ∃ p_tp : p' ≫ s[max i j].tp = s.mkSigma ilen jlen A' B',
    x = lj ▸ s.mkSnd ilen jlen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_code {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.code t) llen ↔
    ∃ i, ∃ li : l = i + 1,
    ∃ (t' : y(Γ.fst) ⟶ s[i].Ty), t' ∈ s.ofType Γ i t ∧
    x = li ▸ s.code (by omega) t' := by
  dsimp only [ofTerm]; cases l <;> simp

@[simp]
theorem mem_ofType_univ {Γ l i} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.univ i) llen ↔
    ∃ li : l = i + 1,
    x = li ▸ (s.homSucc i).wkU Γ.1 := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp] theorem ofCtx_nil : s.ofCtx [] = s.nilCObj := rfl

@[simp]
theorem mem_ofCtx_snoc {Γ A l sΓ'} : sΓ' ∈ s.ofCtx ((A,l) :: Γ) ↔
    ∃ sΓ ∈ s.ofCtx Γ, ∃ llen, ∃ sA ∈ ofType sΓ l A llen, sΓ' = sΓ.snoc llen sA := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

theorem snoc_mem_ofCtx {Γ A l llen sΓ sA} : sΓ ∈ s.ofCtx Γ → sA ∈ ofType sΓ l A llen →
    sΓ.snoc llen sA ∈ s.ofCtx ((A,l) :: Γ) := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

/-! ## Admissibility of thinning -/

-- set_option maxHeartbeats 400000 in -- the `mutual` block takes a while to check.
-- mutual

-- theorem mem_ofType_liftN {A l llen} {sΓ : s.CObj} {sΘ sΓ' : 𝒞} {sA : y(sΓ') ⟶ (s[l]'llen).Ty}
--     (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
--     (sA_mem : sA ∈ ofType (sΓ.append e) l A llen) :
--     let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
--     ym(σ) ≫ sA ∈ ofType sΔ l (A.liftN d.length e.length) llen := by
--   cases A <;> (
--     dsimp [Expr.liftN, ofType] at sA_mem ⊢
--     try simp_part at sA_mem ⊢)
--   case univ =>
--     rcases sA_mem with ⟨rfl, rfl⟩
--     simp
--   case pi =>
--     rcases sA_mem with ⟨rfl, sA, sAmem, sB, sBmem, rfl⟩
--     refine ⟨rfl,
--       _, mem_ofType_liftN d e sAmem,
--       _, mem_ofType_liftN d (e.snoc _ sA) sBmem,
--       ?_⟩
--     simp [comp_mkPi, UHomSeq.CObj.substWk]
--   case el =>
--     obtain ⟨llen, sa, samem, satp, rfl⟩ := sA_mem
--     refine ⟨llen,
--       _, mem_ofTerm_liftN d e samem,
--       ?_⟩
--     simp [satp, UHomSeq.comp_el, UHomSeq.CObj.substWk]
--   case sigma =>
--     rcases sA_mem with ⟨rfl, sA, sAmem, sB, sBmem, rfl⟩
--     refine ⟨rfl,
--       _, mem_ofType_liftN d e sAmem,
--       _, mem_ofType_liftN d (e.snoc _ sA) sBmem,
--       ?_⟩
--     simp [comp_mkSigma, UHomSeq.CObj.substWk]
--   all_goals simp at sA_mem

-- theorem mem_ofTerm_liftN {t l llen} {sΓ : s.CObj} {sΘ sΓ' : 𝒞} {st : y(sΓ') ⟶ (s[l]'llen).Tm}
--     (d : s.ExtSeq sΓ.1 sΘ) (e : s.ExtSeq sΓ.1 sΓ')
--     (st_mem : st ∈ ofTerm (sΓ.append e) l t llen) :
--     let ⟨sΔ, σ⟩ := sΓ.append d |>.substWk d.disp e
--     ym(σ) ≫ st ∈ ofTerm sΔ l (t.liftN d.length e.length) llen := by
--   cases t <;> (
--     dsimp [Expr.liftN, ofTerm] at st_mem ⊢
--     try simp_part at st_mem ⊢)
--   case bvar =>
--     exact sΓ.mem_var_liftVar _ _ _ st_mem
--   case app i _ _ _ _ =>
--     obtain ⟨rfl, ipos, sfn, sfnmem, sarg, sargmem, sB, sBmem, sfntp, rfl⟩ := st_mem
--     refine ⟨rfl, ipos,
--       _, mem_ofTerm_liftN d e sfnmem,
--       _, mem_ofTerm_liftN d e sargmem,
--       _, mem_ofType_liftN d (e.snoc _ <| sarg ≫ s[i].tp) sBmem,
--       ?_⟩
--     simp [sfntp, comp_mkPi, comp_mkApp]
--     constructor <;> rfl -- TODO: why `simp` doesn't close! sides syntactically the same! !!!
--   case code =>
--     obtain ⟨lpos, sA, sAmem, rfl⟩ := st_mem
--     refine ⟨lpos, _, mem_ofType_liftN d e sAmem, ?_⟩
--     simp [show l-1+1 = l by omega, UHomSeq.comp_code_assoc, UHomSeq.CObj.substWk]
--   case lam =>
--     obtain ⟨rfl, sA, sAmem, st, stmem, rfl⟩ := st_mem
--     refine ⟨rfl,
--       _, mem_ofType_liftN d e sAmem,
--       _, mem_ofTerm_liftN d (e.snoc _ sA) stmem,
--       ?_⟩
--     simp [comp_mkLam, UHomSeq.CObj.substWk]
--   case pair =>
--     obtain ⟨rfl, st, stmem, sB, sBmem, su, sumem, sutp, rfl⟩ := st_mem
--     refine ⟨rfl,
--       _, mem_ofTerm_liftN d e stmem,
--       _, mem_ofType_liftN d (e.snoc _ _) sBmem,
--       _, mem_ofTerm_liftN d e sumem,
--       ?_, ?_⟩
--     . simp [sutp, NaturalModelBase.comp_sec_functor_map_assoc]; rfl
--     . simp [comp_mkPair]; rfl
--   case fst =>
--     obtain ⟨rfl, llen, sA, sAmem, sB, sBmem, sp, spmem, sptp, rfl⟩ := st_mem
--     refine ⟨rfl, llen,
--       _, mem_ofType_liftN d e sAmem,
--       _, mem_ofType_liftN d (e.snoc _ _) sBmem,
--       _, mem_ofTerm_liftN d e spmem,
--       ?_, ?_⟩
--     . simp [sptp, comp_mkSigma]
--     . simp [comp_mkFst, UHomSeq.CObj.substWk]
--   case snd =>
--     obtain ⟨rfl, llen, sA, sAmem, sB, sBmem, sp, spmem, sptp, rfl⟩ := st_mem
--     refine ⟨rfl, llen,
--       _, mem_ofType_liftN d e sAmem,
--       _, mem_ofType_liftN d (e.snoc _ _) sBmem,
--       _, mem_ofTerm_liftN d e spmem,
--       ?_, ?_⟩
--     . simp [sptp, comp_mkSigma]
--     . simp [comp_mkSnd, UHomSeq.CObj.substWk]
--   all_goals simp at st_mem

-- end

-- theorem mem_ofType_lift {A l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sA} (sB : y(sΓ.1) ⟶ s[l'].Ty)
--     (sA_mem : sA ∈ ofType sΓ l A llen) :
--     (s[l']'l'len).wk sB sA ∈ ofType (sΓ.snoc l'len sB) l A.lift llen := by
--   convert mem_ofType_liftN (UHomSeq.ExtSeq.nil.snoc l'len sB) .nil sA_mem using 1
--   simp [wk, UHomSeq.ExtSeq.substWk, UHomSeq.ExtSeq.disp, UHomSeq.CObj.substWk]

-- theorem mem_ofTerm_lift {t l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {st} (sB : y(sΓ.1) ⟶ s[l'].Ty)
--     (st_mem : st ∈ ofTerm sΓ l t llen) :
--     (s[l']'l'len).wk sB st ∈ ofTerm (sΓ.snoc l'len sB) l t.lift llen := by
--   convert mem_ofTerm_liftN (UHomSeq.ExtSeq.nil.snoc l'len sB) .nil st_mem using 1
--   simp [wk, UHomSeq.ExtSeq.substWk, UHomSeq.ExtSeq.disp, UHomSeq.CObj.substWk]

/-! ## Admissibility of instantiation -/

-- set_option maxHeartbeats 400000 in
-- theorem mem_ofTerm_instVar {a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sΓ' : 𝒞}
--     {st : y(sΓ') ⟶ (s[l]'llen).Tm} {sa : y(sΓ.1) ⟶ (s[l']'l'len).Tm}
--     (i)
--     (sA : y(sΓ.1) ⟶ s[l'].Ty) (d : s.ExtSeq (s[l'].ext sA) sΓ')
--     (st_mem : st ∈ (sΓ.snoc l'len sA |>.append d).var llen i)
--     (sa_mem : sa ∈ ofTerm sΓ l' a l'len) (sa_tp : sa ≫ s[l'].tp = sA) :
--     let σ := s[l'].sec sA sa sa_tp
--     let ⟨sΔ, σ'⟩ := sΓ.substWk σ d
--     ym(σ') ≫ st ∈ ofTerm sΔ l (instVar i a d.length) llen := by
--   rcases i.lt_trichotomy d.length with ilen | rfl | ilen
--   . simp only [instVar, ilen, ↓reduceIte, ofTerm,
--       UHomSeq.CObj.var, UHomSeq.CObj.substWk, UHomSeq.CObj.append] at st_mem ⊢
--     rw [UHomSeq.ExtSeq.var_eq_of_lt_length _ _ ilen] at st_mem
--     rw [UHomSeq.ExtSeq.var_eq_of_lt_length]
--     . exact UHomSeq.ExtSeq.var_substWk_of_lt_length _ d llen st_mem ilen
--     . simp [ilen]
--   . simp only [instVar, lt_self_iff_false, ↓reduceIte,
--       UHomSeq.CObj.var, UHomSeq.CObj.append] at st_mem ⊢
--     rw [show d.length = 0 + d.length by omega, UHomSeq.ExtSeq.var_append_add_length] at st_mem
--     dsimp [UHomSeq.ExtSeq.var] at st_mem
--     simp_part at st_mem
--     obtain ⟨sa, ⟨rfl, rfl⟩, rfl⟩ := st_mem
--     have := mem_ofTerm_liftN (d.substWk (s[l'].sec sA sa sa_tp)).snd.1 .nil sa_mem
--     conv => enter [2]; dsimp [UHomSeq.CObj.substWk]
--     rw [← Functor.map_comp_assoc, UHomSeq.ExtSeq.substWk_disp, Functor.map_comp_assoc, sec_var]
--     convert this using 2
--     simp
--   . simp only [show ¬(i < d.length) by omega, show i ≠ d.length by omega,
--       instVar, lt_self_iff_false, ↓reduceIte,
--       UHomSeq.CObj.var, UHomSeq.CObj.append, ofTerm, UHomSeq.CObj.substWk] at st_mem ⊢
--     obtain ⟨k, rfl⟩ : ∃ k, i = k + (d.length + 1) := Nat.exists_eq_add_of_le' (by omega)
--     simp only [show k + (d.length + 1) = (k + 1) + d.length by omega,
--       UHomSeq.ExtSeq.var_append_add_length, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var] at st_mem
--     simp_part at st_mem
--     obtain ⟨sv, svmem, rfl⟩ := st_mem
--     have := sΓ.2.mem_var_liftVar
--       k (UHomSeq.ExtSeq.substWk (s[l'].sec sA sa sa_tp) d).snd.1 .nil svmem
--     simp at this
--     convert this using 1
--     . congr 1
--       omega
--     . rw [d.substWk_disp_functor_map_assoc]
--       simp

-- -- TODO: the inductive cases here are literally the same as in `mem_ofType_liftN`.
-- -- Formalize this observation as an induction principle?
-- set_option maxHeartbeats 400000 in
-- mutual

-- theorem mem_ofType_inst {B a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sΓ' : 𝒞} {sB : y(sΓ') ⟶ (s[l']'l'len).Ty} {sa : y(sΓ.1) ⟶ (s[l]'llen).Tm}
--     (sA : y(sΓ.1) ⟶ s[l].Ty)
--     (d : s.ExtSeq (sΓ.snoc llen sA).1 sΓ')
--     (sB_mem : sB ∈ ofType ((sΓ.snoc llen sA).append d) l' B l'len)
--     (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
--     let sΔσ' := sΓ.substWk (s[l].sec sA sa sa_tp) d
--     ym(sΔσ'.2) ≫ sB ∈ ofType sΔσ'.1 l' (B.inst a d.length) l'len := by
--   cases B <;> (
--     dsimp [Expr.inst, ofType] at sB_mem ⊢
--     try simp_part at sB_mem ⊢)
--   case univ =>
--     rcases sB_mem with ⟨rfl, rfl⟩
--     simp
--   case pi =>
--     rcases sB_mem with ⟨rfl, sB, sBmem, sC, sCmem, rfl⟩
--     refine ⟨rfl,
--       _, mem_ofType_inst sA d sBmem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc _ sB) sCmem sa_mem sa_tp,
--       ?_⟩
--     simp [comp_mkPi, UHomSeq.CObj.substWk]
--   case sigma =>
--     rcases sB_mem with ⟨rfl, sB, sBmem, sC, sCmem, rfl⟩
--     refine ⟨rfl,
--       _, mem_ofType_inst sA d sBmem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc _ sB) sCmem sa_mem sa_tp,
--       ?_⟩
--     simp [comp_mkSigma, UHomSeq.CObj.substWk]
--   case el =>
--     obtain ⟨llen, sa, samem, satp, rfl⟩ := sB_mem
--     refine ⟨llen,
--       _, mem_ofTerm_inst sA d samem sa_mem sa_tp,
--       ?_⟩
--     simp [satp, UHomSeq.comp_el, UHomSeq.CObj.substWk]
--   all_goals simp at sB_mem

-- theorem mem_ofTerm_inst {t a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sΓ' : 𝒞} {st : y(sΓ') ⟶ (s[l']'l'len).Tm} {sa : y(sΓ.1) ⟶ (s[l]'llen).Tm}
--     (sA : y(sΓ.1) ⟶ s[l].Ty)
--     (d : s.ExtSeq (sΓ.snoc llen sA).1 sΓ')
--     (st_mem : st ∈ ofTerm ((sΓ.snoc llen sA).append d) l' t l'len)
--     (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
--     let sΔσ' := sΓ.substWk (s[l].sec sA sa sa_tp) d
--     ym(sΔσ'.2) ≫ st ∈ ofTerm sΔσ'.1 l' (t.inst a d.length) l'len := by
--   intro sΔσ'
--   cases t <;> (
--     dsimp [Expr.inst, ofTerm] at st_mem ⊢
--     try simp_part at st_mem ⊢)
--   case bvar =>
--     exact mem_ofTerm_instVar _ sA d st_mem sa_mem sa_tp
--   case app i j _ _ _ =>
--     obtain ⟨rfl, ipos, sfn, sfnmem, sarg, sargmem, sB, sBmem, sfntp, rfl⟩ := st_mem
--     refine ⟨rfl, ipos,
--       _, mem_ofTerm_inst sA d sfnmem sa_mem sa_tp,
--       _, mem_ofTerm_inst sA d sargmem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc _ <| sarg ≫ s[i].tp) sBmem sa_mem sa_tp,
--       ?_⟩
--     simp [sfntp, comp_mkPi, comp_mkApp]
--     exact ⟨rfl, rfl⟩ -- TODO: why `simp` doesn't close! sides syntactically the same! !!!
--   case lam =>
--     obtain ⟨rfl, sB, sBmem, st, stmem, rfl⟩ := st_mem
--     refine ⟨rfl,
--       _, mem_ofType_inst sA d sBmem sa_mem sa_tp,
--       _, mem_ofTerm_inst sA (d.snoc _ sB) stmem sa_mem sa_tp,
--       ?_⟩
--     simp [sΔσ', comp_mkLam, UHomSeq.CObj.substWk]
--   case code =>
--     obtain ⟨lpos, sB, sBmem, rfl⟩ := st_mem
--     refine ⟨lpos, _, mem_ofType_inst sA d sBmem sa_mem sa_tp, ?_⟩
--     simp [show l'-1+1 = l' by omega, UHomSeq.comp_code_assoc, sΔσ']
--   case pair =>
--     obtain ⟨rfl, st, stmem, sB, sBmem, su, sumem, sutp, rfl⟩ := st_mem
--     refine ⟨rfl,
--       _, mem_ofTerm_inst sA d stmem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc _ _) sBmem sa_mem sa_tp,
--       _, mem_ofTerm_inst sA d sumem sa_mem sa_tp,
--       ?_, ?_⟩
--     . simp [sutp, NaturalModelBase.comp_sec_functor_map_assoc]; rfl
--     . simp [comp_mkPair]; rfl
--   case fst =>
--     obtain ⟨rfl, llen, sA', sA'mem, sB, sBmem, sp, spmem, sptp, rfl⟩ := st_mem
--     refine ⟨rfl, llen,
--       _, mem_ofType_inst sA d sA'mem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc ..) sBmem sa_mem sa_tp,
--       _, mem_ofTerm_inst sA d spmem sa_mem sa_tp,
--       ?_, ?_⟩
--     . simp [sptp, comp_mkSigma]
--       congr 1
--     . simp [comp_mkFst, UHomSeq.CObj.substWk]
--       congr 1
--   case snd =>
--     obtain ⟨rfl, llen, sA', sA'mem, sB, sBmem, sp, spmem, sptp, rfl⟩ := st_mem
--     refine ⟨rfl, llen,
--       _, mem_ofType_inst sA d sA'mem sa_mem sa_tp,
--       _, mem_ofType_inst sA (d.snoc ..) sBmem sa_mem sa_tp,
--       _, mem_ofTerm_inst sA d spmem sa_mem sa_tp,
--       ?_, ?_⟩
--     . simp [sptp, comp_mkSigma]
--       congr 1
--     . simp [comp_mkSnd, UHomSeq.CObj.substWk]
--       congr 1
--   all_goals simp at st_mem

-- end

-- theorem mem_ofType_inst0 {B a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sA sB sa}
--     (sB_mem : sB ∈ ofType (sΓ.snoc llen sA) l' B l'len)
--     (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
--     ym(s[l].sec sA sa sa_tp) ≫ sB ∈ ofType sΓ l' (B.inst a) l'len :=
--   mem_ofType_inst sA .nil sB_mem sa_mem sa_tp

-- theorem mem_ofTerm_inst0 {t a l l'} {llen : l < s.length + 1} {l'len : l' < s.length + 1}
--     {sΓ : s.CObj} {sA st sa}
--     (st_mem : st ∈ ofTerm (sΓ.snoc llen sA) l' t l'len)
--     (sa_mem : sa ∈ ofTerm sΓ l a llen) (sa_tp : sa ≫ s[l].tp = sA) :
--     ym(s[l].sec sA sa sa_tp) ≫ st ∈ ofTerm sΓ l' (t.inst a) l'len :=
--   mem_ofTerm_inst sA .nil st_mem sa_mem sa_tp

/-! ## Soundness of interpretation -/

/-! ### Π helpers -/

-- theorem mem_ofTerm_lam {A t} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {st : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Tm}
--     (sA_mem : sA ∈ ofType sΓ i A ilen)
--     (st_mem : st ∈ ofTerm (sΓ.snoc ilen sA) j t jlen) :
--     s.mkLam ilen jlen sA st ∈ ofTerm sΓ (max i j) (.lam i j A t) := by
--   dsimp [ofTerm]
--   simp_part
--   use sA, sA_mem, st, st_mem

-- theorem mem_ofTerm_app {B f a} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ s[i].Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
--     {sf : y(sΓ.1) ⟶ s[max i j].Tm} {sa : y(sΓ.1) ⟶ (s[i]'ilen).Tm}
--     (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
--     (sf_mem : sf ∈ ofTerm sΓ (max i j) f)
--     (sf_tp : sf ≫ s[max i j].tp = s.mkPi ilen jlen sA sB)
--     (sa_mem : sa ∈ ofTerm sΓ i a ilen)
--     (sa_tp : sa ≫ s[i].tp = sA) :
--     s.mkApp ilen jlen sA sB sf sf_tp sa sa_tp ∈ ofTerm sΓ j (.app i j B f a) jlen := by
--   cases sa_tp
--   dsimp [ofTerm]
--   simp_part
--   use ilen, sf, sf_mem, sa, sa_mem, sB, sB_mem, sf_tp

-- theorem mem_ofTerm_etaExpand {A B f} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
--     {sf : y(sΓ.1) ⟶ s[max i j].Tm}
--     (sA_mem : sA ∈ ofType sΓ i A ilen)
--     (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
--     (sf_mem : sf ∈ ofTerm sΓ (max i j) f)
--     (sf_tp : sf ≫ s[max i j].tp = s.mkPi ilen jlen sA sB) :
--     s.etaExpand ilen jlen sA sB sf sf_tp ∈
--       ofTerm sΓ (max i j) (.lam i j A <| .app i j (B.liftN 1 1) f.lift (.bvar 0)) := by
--   dsimp [etaExpand]
--   apply mem_ofTerm_lam sA_mem
--   apply mem_ofTerm_app
--   . have := mem_ofType_liftN (UHomSeq.ExtSeq.nil.snoc _ sA) (UHomSeq.ExtSeq.nil.snoc _ sA) sB_mem
--     dsimp at this
--     convert this using 2 <;> congr <;> simp [UHomSeq.CObj.substWk, wk]
--   . exact mem_ofTerm_lift _ sf_mem
--   . dsimp [ofTerm, UHomSeq.CObj.var, UHomSeq.ExtSeq.var]
--     simp

/-! ### Σ helpers -/

-- theorem mem_ofTerm_pair {A B t u} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
--     {st su}
--     (sA_mem : sA ∈ ofType sΓ i A ilen)
--     (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
--     (st_mem : st ∈ ofTerm sΓ i t ilen)
--     (st_tp : st ≫ s[i].tp = sA)
--     (su_mem : su ∈ ofTerm sΓ j u jlen)
--     (su_tp : su ≫ s[j].tp = ym(s[i].sec sA st st_tp) ≫ sB) :
--     s.mkPair ilen jlen sA sB st st_tp su su_tp ∈ ofTerm sΓ (max i j) (.pair i j B t u) := by
--   dsimp [ofTerm]
--   simp_part
--   cases st_tp
--   use st, st_mem, sB, sB_mem, su, su_mem, su_tp

-- theorem mem_ofTerm_fst {A B p} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
--     {sp : y(sΓ.1) ⟶ s[max i j].Tm}
--     (sA_mem : sA ∈ ofType sΓ i A ilen)
--     (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
--     (sp_mem : sp ∈ ofTerm sΓ (max i j) p)
--     (sp_tp : sp ≫ s[max i j].tp = s.mkSigma ilen jlen sA sB) :
--     s.mkFst ilen jlen sA sB sp sp_tp ∈ ofTerm sΓ i (.fst i j A B p) := by
--   dsimp [ofTerm]
--   simp_part
--   use jlen, sA, sA_mem, sB, sB_mem, sp, sp_mem, sp_tp

-- theorem mem_ofTerm_snd {A B p} {i j : Nat} {ilen : i < s.length + 1} {jlen : j < s.length + 1}
--     {sΓ : s.CObj} {sA : y(sΓ.1) ⟶ (s[i]'ilen).Ty} {sB : y((sΓ.snoc ilen sA).1) ⟶ (s[j]'jlen).Ty}
--     {sp : y(sΓ.1) ⟶ s[max i j].Tm}
--     (sA_mem : sA ∈ ofType sΓ i A ilen)
--     (sB_mem : sB ∈ ofType (sΓ.snoc ilen sA) j B jlen)
--     (sp_mem : sp ∈ ofTerm sΓ (max i j) p)
--     (sp_tp : sp ≫ s[max i j].tp = s.mkSigma ilen jlen sA sB) :
--     s.mkSnd ilen jlen sA sB sp sp_tp ∈ ofTerm sΓ j (.snd i j A B p) := by
--   dsimp [ofTerm]
--   simp_part
--   use ilen, sA, sA_mem, sB, sB_mem, sp, sp_mem, sp_tp

variable (slen : univMax ≤ s.length)

inductive CSb : (Δ Γ : s.CObj) → (Δ.1 ⟶ Γ.1) → Type _ where
  | id Γ : CSb Γ Γ (𝟙 _)
  | wk {Γ : s.CObj} {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) :
    CSb (Γ.snoc llen A) Γ (s[l].disp A)
  | comp {Θ Δ Γ : s.CObj} {σ τ} : CSb Θ Δ σ → CSb Δ Γ τ → CSb Θ Γ (σ ≫ τ)
  | snoc {Δ Γ : s.CObj} {σ} (_ : CSb Δ Γ σ) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ ofTerm Δ l e) :
    CSb Δ (Γ.snoc llen A) (s[l].substCons σ A se eq)

def CSb.toSb {Δ Γ σ} : s.CSb Δ Γ σ → Nat → Expr
  | .id _ => .bvar
  | .wk _ _ => Expr.wk
  | .comp σ τ => Expr.comp σ.toSb τ.toSb
  | .snoc σ _ _ e _ _ => Expr.snoc σ.toSb e

def CSb.sub1 {Γ : s.CObj} {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Γ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = A)
    (H : se ∈ ofTerm Γ l e) :
    CSb Γ (Γ.snoc llen A) (s[l].sec A se eq) :=
  snoc (id Γ) llen A e _ H

@[simp] theorem CSb.sub1_toSb {Γ : s.CObj} {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Γ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = A)
    (H : se ∈ ofTerm Γ l e) :
    (sub1 llen A e eq H).toSb = Expr.toSb e := by
  simp [sub1, toSb, Expr.toSb]

def CSb.up {Δ Γ σ} (sσ : s.CSb Δ Γ σ) {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) :
    CSb (Δ.snoc llen (ym(σ) ≫ A)) (Γ.snoc llen A) (by exact s[l].substWk σ A) := by
  refine ((CSb.wk ..).comp sσ).snoc _ _ (.bvar 0) _ ?_
  simp [UHomSeq.CObj.var, UHomSeq.ExtSeq.var]

@[simp] theorem CSb.up_toSb {Δ Γ σ} (sσ : s.CSb Δ Γ σ)
     {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) :
    (up sσ llen A).toSb = Expr.up sσ.toSb := by
  simp [up, toSb, Expr.up_eq_snoc]

def CSb.up' {Δ Γ σ} (sσ : s.CSb Δ Γ σ) {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty)
    {A'} (eq : ym(σ) ≫ A = A') :
    CSb (Δ.snoc llen A') (Γ.snoc llen A) (eq ▸ s[l].substWk σ A) := by
  subst eq; exact CSb.up sσ llen A

@[simp] theorem CSb.up'_toSb {Δ Γ σ} (sσ : s.CSb Δ Γ σ)
     {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) {A'} (eq : ym(σ) ≫ A = A') :
    (up' sσ llen A eq).toSb = Expr.up sσ.toSb := by
  subst eq; apply CSb.up_toSb

theorem mem_ofType_ofTerm_subst {e l} (llen : l < s.length + 1)
    {Δ Γ : s.CObj} {sσ} (σ : CSb Δ Γ sσ) {σ'} (eq : σ.toSb = σ') :
    (∀ {sA}, sA ∈ ofType Γ l e llen →
      ym(sσ) ≫ sA ∈ ofType Δ l (Expr.subst σ' e) llen) ∧
    (∀ {se}, se ∈ ofTerm Γ l e llen →
      ym(sσ) ≫ se ∈ ofTerm Δ l (Expr.subst σ' e) llen) := by
  subst σ'
  induction e generalizing Δ Γ l <;>
    (constructor <;> [intro sA H; intro se H] <;> try cases Part.notMem_none _ H)
  case pi.left ihA ihB =>
    obtain ⟨rfl, H⟩ := mem_ofType_pi.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst_pi, comp_mkPi, mem_ofType_pi, exists_true_left]
    exact ⟨_, (ihA llen.1 σ).1 hA, _,
      CSb.up_toSb (s := s) .. ▸ (ihB llen.2 (σ.up llen.1 A)).1 hB, rfl⟩
  case sigma.left ihA ihB =>
    obtain ⟨rfl, H⟩ := mem_ofType_sigma.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst_sigma, comp_mkSigma, mem_ofType_sigma, exists_true_left]
    exact ⟨_, (ihA llen.1 σ).1 hA, _,
      CSb.up_toSb (s := s) .. ▸ (ihB llen.2 (σ.up llen.1 A)).1 hB, rfl⟩
  case el.left ih =>
    obtain ⟨llen', A, hA, tp, rfl⟩ := mem_ofType_el.1 H
    simp only [Expr.subst_el, mem_ofType_el, UHomSeq.comp_el, exists_true_left, llen']
    exact ⟨_, (ih (by omega) σ).2 hA, by simp [tp], rfl⟩
  case univ.left =>
    obtain ⟨rfl, H⟩ := mem_ofType_univ.1 H; simp at H llen; subst H
    simp only [Expr.subst_univ, mem_ofType_univ, exists_true_left, UHom.comp_wkU]

  stop skip

theorem mem_ofType_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ ofType Γ l e hl) :
    s[l'].wk X se ∈ ofType (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).1 H

theorem mem_ofTerm_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ ofTerm Γ l e hl) :
    s[l'].wk X se ∈ ofTerm (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).2 H

theorem mem_ofType_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ ofType (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ ofType Γ l (Expr.subst a.toSb e) hl :=
  (mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).1 H

theorem mem_ofTerm_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ ofTerm (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ ofTerm Γ l (Expr.subst a.toSb e) hl :=
  (mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).2 H

theorem tp_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ ofCtx s Γ) :
    ∃ llen, ∃ sA ∈ sΓ.tp llen i, sA ∈ ofType sΓ l A llen := by
  induction H generalizing sΓ <;>
  · obtain ⟨_, hΓ', _, _, hB, rfl⟩ := mem_ofCtx_snoc.1 hΓ
    simp [UHomSeq.CObj.tp, UHomSeq.ExtSeq.tp, *] at *
    grind [mem_ofType_wk]

theorem var_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ ofCtx s Γ) :
    ∃ llen, ∃ st ∈ sΓ.var llen i, st ≫ s[l].tp ∈ ofType sΓ l A llen := by
  have ⟨llen, _, h1, h2⟩ := tp_sound H hΓ
  simp [← UHomSeq.CObj.var_tp] at h1
  obtain ⟨_, h1, rfl⟩ := h1
  exact ⟨llen, _, h1, h2⟩

-- TODO: this proof is boring, repetitive exists-elim/exists-intro: automate!
include slen in
set_option maxHeartbeats 300000 in
theorem ofType_ofTerm_sound :
    (∀ {Γ}, WfCtx Γ → (ofCtx s Γ).Dom) ∧
    (∀ {Γ l A}, (Awf : Γ ⊢[l] A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      (ofType sΓ l A llen).Dom) ∧
    (∀ {Γ l A B}, (Aeq : Γ ⊢[l] A ≡ B) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, sA ∈ ofType sΓ l B llen) ∧
    (∀ {Γ l A t}, (twf : Γ ⊢[l] t : A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, ∃ st ∈ ofTerm sΓ l t llen, st ≫ s[l].tp = sA) ∧
    (∀ {Γ l A t u}, (teq : Γ ⊢[l] t ≡ u : A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, ∃ st ∈ ofTerm sΓ l t llen,
        st ∈ ofTerm sΓ l u llen ∧ st ≫ s[l].tp = sA) := by

  -- have snoc_helper {Γ A A' l sΓ} :
  --     (Aeq : Γ ⊢[l] A ≡ A') → sΓ ∈ ofCtx s Γ →
  --       have llen := s.lt_slen_of_eqTp slen Aeq
  --       ∀ {sA}, sA ∈ ofType sΓ l A llen → sΓ.snoc llen sA ∈ ofCtx s ((A, l) :: Γ) :=
  --   fun Aeq sΓmem {sA} sAmem =>
  --     have llen := s.lt_slen_of_eqTp slen Aeq
  --     have sΓA := sΓ.snoc llen sA
  --     snoc_mem_ofCtx sΓmem sAmem
  simp [Part.dom_iff_mem]
  mutual_induction WfCtx
  -- all_goals
  --   simp -failIfUnchanged only [mem_ofCtx_snoc, forall_exists_index, and_imp]
  --   intros; subst_eqs

  case nil => simp
  case snoc =>
    simp only [mem_ofCtx_snoc, forall_exists_index, and_imp]
    intros; rename_i hΓ llen _ hA
    exact ⟨_, _, hΓ, llen, _, hA, rfl⟩

  case pi' | sigma' =>
    simp only [mem_ofCtx_snoc, mem_ofType_pi, mem_ofType_sigma,
      exists_true_left, forall_exists_index, and_imp]
    intros; subst_eqs; rename_i hΓ _ _ hA llen _ hB
    exact ⟨_, hΓ, by omega, _, _, hA, _, hB, rfl⟩
  case univ =>
    simp only [mem_ofType_univ, exists_true_left, forall_exists_index]
    intros; rename_i hΓ
    exact ⟨_, hΓ, by omega, _, rfl⟩
  case el =>
    simp only [mem_ofType_univ, mem_ofType_el, forall_exists_index, and_imp]
    intros; subst_eqs; rename_i hΓ _ _ _ hA h
    exact ⟨_, hΓ, by omega, _, by omega, _, hA, h, rfl⟩

  case cong_pi' | cong_sigma' =>
    simp only [mem_ofCtx_snoc, mem_ofType_pi, mem_ofType_sigma,
      forall_exists_index, and_imp, exists_true_left, Nat.max_lt]
    intros; subst_eqs; rename_i hΓ _ _ hA _ _ hΓ' _ _ hA' _ _ _ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA hA'
    exact ⟨_, hΓ, ⟨‹_›, ‹_›⟩, _, ⟨_, hA, _, ‹_›, rfl⟩, ⟨_, ‹_›, _, ‹_›, rfl⟩⟩
  case cong_el =>
    simp only [mem_ofType_univ, mem_ofType_el, forall_exists_index, and_imp]
    intros; subst_eqs
    exact ⟨_, ‹_›, by omega, _, ⟨by omega, _, ‹_›, ‹_›, rfl⟩, ⟨by omega, _, ‹_›, ‹_›, rfl⟩⟩
  case el_code =>
    simp only [mem_ofTerm_code, mem_ofType_el, forall_exists_index, and_imp,
      Nat.add_right_cancel_iff, exists_prop_eq']
    intros
    refine ⟨_, ‹_›, ‹_›, _, ⟨by omega, _, ⟨_, ‹_›, rfl⟩, ?_, rfl⟩, ?_⟩
    · apply s.code_tp
    · rwa [s.el_code]
  case refl_tp | symm_tp => grind
  case trans_tp =>
    simp only [forall_exists_index, and_imp]
    intros; rename_i hΓ _ _ _ hA₁ _ hΓ' _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA₁ hA₂
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›⟩

  case bvar =>
    simp only [ofTerm_bvar, forall_exists_index]
    intros
    obtain ⟨llen, _, h1, h2⟩ := var_sound ‹_› ‹_›
    exact ⟨_, ‹_›, llen, _, h2, _, h1, rfl⟩
  case lam' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_lam, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ _ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA hA'
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, ?_⟩
    apply mkLam_tp (t_tp := rfl)
  case app' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ _ _ _ _ hΓ₂ _ _ _ _ _ _ hA₂
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkApp_tp]
    apply mem_ofType_toSb <;> assumption
  case pair' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_pair, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₁; clear hA₁
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, ?_⟩, _, ⟨_, ‹_›, _, ‹_›, _, ‹_›, ?_, rfl⟩, rfl⟩
    · apply mkPair_tp
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
  case fst' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ hB _ _ _ hB' _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hB hB'; clear hB'
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, ?_⟩
    apply mkFst_tp
  case snd' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ hB _ _ _ hB' _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hB hB'; clear hB'
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkSnd_tp]
    apply mem_ofType_toSb <;> simp only [mem_ofTerm_fst, exists_true_left, *]
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩
  case code =>
    simp only [mem_ofTerm_code, mem_ofType_univ,
      Nat.add_right_cancel_iff, exists_prop_eq', exists_eq_left, Nat.add_lt_add_iff_right,
      forall_exists_index, and_imp, exists_true_left]
    intros
    refine ⟨_, ‹_›, by omega, _, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply UHomSeq.code_tp
  case conv =>
    simp only [forall_exists_index, and_imp]
    intros; subst_eqs
    rename_i hΓ _ _ _ _ hΓ' _ _ hA _ hA'
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, rfl⟩

  case cong_lam' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_lam, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ hΓ₁ _ _ hA₁ hA'₁ _ hΓ₂ _ _ hA₂ _ _ _ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA' hA'₁; clear hA'₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _,
      ⟨_, ‹_›, _, ‹_›, rfl⟩, ⟨_, ‹_›, _, ‹_›, rfl⟩, ?_⟩
    apply mkLam_tp (t_tp := rfl)
  case cong_app' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ hB _ _ _ _ hΓ₂ _ _ _ _ _ hB₁ _ _ hA₃
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkApp_tp]
    apply mem_ofType_toSb <;> assumption
  case cong_pair' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_pair, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ _ _ _ hΓ₂ _ _ _ _ _ _ _ hA₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₁; clear hA₁
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, ?_⟩, _,
      ⟨_, ‹_›, _, ‹_›, _, ‹_›, ?h2, rfl⟩, ⟨_, ‹_›, _, ‹_›, _, ‹_›, ?h2, rfl⟩, rfl⟩
    · apply mkPair_tp
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
  case cong_fst' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ hA₃ _ hB _ _ _ _ hB₁ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, ?_⟩
    apply mkFst_tp
  case cong_snd' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ hA₃ _ hB _ _ _ _ hB₁ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkSnd_tp]
    apply mem_ofType_toSb <;> simp only [mem_ofTerm_fst, exists_true_left, *]
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩
  case cong_code =>
    simp only [mem_ofTerm_code, mem_ofType_univ,
      Nat.add_right_cancel_iff, exists_prop_eq', exists_eq_left, Nat.add_lt_add_iff_right,
      forall_exists_index, and_imp, exists_true_left]
    intros
    refine ⟨_, ‹_›, by omega, _, ⟨_, ‹_›, rfl⟩, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply UHomSeq.code_tp
  case app_lam' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofTerm_lam,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ _ _ hB _ _ hA₃ hB₁
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _,
      ⟨‹_›, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ‹_›, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩
    · rw [mkApp_tp]
      apply mem_ofType_toSb <;> assumption
    · apply mkLam_tp (t_tp := rfl)
    · rw [mkApp_mkLam (t_tp := rfl)]
      apply mem_ofTerm_toSb <;> assumption
  case fst_pair' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofTerm_pair,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ⟨_, ‹_›, _, ‹_›, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩, ?_, ?_⟩
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
    · apply mkPair_tp
    · rwa [mkFst_mkPair]
    · rw [mkFst_mkPair]
  case snd_pair' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofTerm_pair,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _,
      ⟨_, ‹_›, _, ‹_›, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩, ?_, rfl⟩
    · rwa [mkSnd_mkPair]
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
    · apply mkPair_tp
    · rwa [mkSnd_mkPair]
  case lam_app' =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofTerm_lam, mem_ofType_pi, ofTerm_bvar,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i l _ _ _ _ _ hΓ _ A hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ hB _ _ _ hB₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ⟨_, ‹_›, _, ‹_›, ‹_›⟩, _, ‹_›, ⟨_, ‹_›, _,
      ⟨‹_›, _, mem_ofTerm_wk _ ‹_› .., _, (mem_var_zero (x := s[l].var _)).2 ⟨rfl, rfl⟩,
        _, (mem_ofType_ofTerm_subst _ (.up' (.wk _ _) _ _ ?_) (CSb.up'_toSb ..)).1 ‹_›, ?_, ?_⟩,
      .symm (mkLam_mkApp (f_tp := ‹_›) ..)⟩, rfl⟩
    · simp [wk]
    · simp [*, wk, comp_mkPi]
      generalize_proofs; congr!; simp
    · generalize_proofs; congr! 1; rename_i h _ _ _ h2
      have : h ▸ s[l].substWk (s[l].disp A) A ≍ s[l].substWk (s[l].disp A) A := by simp
      simp [(conj_eqToHom_iff_heq _ _ (h2 ▸ rfl) rfl).2 this, eqToHom_map]
  case pair_fst_snd' =>
    sorry
  case code_el =>
    sorry
  case conv_eq =>
    sorry
  case refl_tm =>
    sorry
  case symm_tm' =>
    sorry
  case trans_tm' =>
    sorry

  stop
  /- Eta laws -/

  case pair_fst_snd Awf _ _ ihA ihB ihp _ sΓmem =>
    have ⟨sA, sAmem, _⟩ := ihA sΓmem
    have ⟨sB, sBmem, _⟩ := ihB (snoc_helper Awf sΓmem sAmem)
    obtain ⟨_, sptpmem, sp, spmem, _, rfl⟩ := ihp sΓmem
    dsimp [ofType] at sptpmem
    simp_part at sptpmem ⊢
    obtain ⟨_, h, _, h', sptpeq⟩ := sptpmem
    cases Part.mem_unique h sAmem
    cases Part.mem_unique h' sBmem
    have fstmem := mem_ofTerm_fst sAmem sBmem spmem sptpeq
    have sndmem := mem_ofTerm_snd sAmem sBmem spmem sptpeq
    refine ⟨_, ⟨sA, sAmem, sB, sBmem, rfl⟩,
      _, ?_, mem_ofTerm_pair sAmem sBmem fstmem (by simp) sndmem (by simp), ?_⟩ <;>
      simp [spmem, sptpeq]
  case lam_app l l' fwf ihf _ sΓmem =>
    have ⟨sAB, sABmem, sf, sfmem, sfmem', sftp⟩ := ihf sΓmem
    have maxlen := s.lt_slen_of_eqTp slen fwf.wf_tp
    have llen : l < s.length + 1 := by omega
    have l'len : l' < s.length + 1 := by omega
    have sABmem_ := sABmem
    dsimp [ofType] at sABmem
    simp_part at sABmem
    have ⟨sA, sAmem, sB, sBmem, sABeq⟩ := sABmem
    refine ⟨sAB, sABmem_, ?_⟩
    refine ⟨s.etaExpand llen l'len sA sB sf (sABeq ▸ sftp), ?_, ?_, ?_⟩
    . rw [etaExpand_eq]; assumption
    . apply mem_ofTerm_etaExpand sAmem sBmem sfmem (sABeq ▸ sftp)
    . rw [etaExpand_eq]; assumption
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
  case cong_sigma Aeq Beq ihA ihB sΓ sΓmem =>
    have ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper Aeq sΓmem sAmem)
    have llen := s.lt_slen_of_eqTp slen Aeq
    have l'len := s.lt_slen_of_eqTp slen Beq
    use s.mkSigma llen l'len sA sB
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
      _, mem_ofTerm_lam sAmem stmem,
      mem_ofTerm_lam sAmem' stmem',
      ?_⟩
    simp [sttp]
  case cong_app Beq _ aeq ihB ihf iha _ sΓmem =>
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
    refine ⟨_, mem_ofType_inst0 sBmem samem rfl,
      _, mem_ofTerm_app sBmem sfmem sftp samem rfl,
      mem_ofTerm_app sBmem' sfmem' sftp samem' rfl,
      ?_ ⟩
    simp
  case cong_pair teq _ ihB iht ihu _ sΓmem =>
    obtain ⟨_, sttpmem, st, stmem, stmem', rfl⟩ := iht sΓmem
    have ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper teq.wf_tp sΓmem sttpmem)
    have ⟨sBt, sBtmem, su, sumem, sumem', sutp⟩ := ihu sΓmem
    cases Part.mem_unique (mem_ofType_inst0 sBmem stmem rfl) sBtmem
    simp_part
    refine ⟨_, ⟨_, sttpmem, sB, sBmem, rfl⟩,
      _,
      mem_ofTerm_pair sttpmem sBmem stmem rfl sumem sutp,
      mem_ofTerm_pair sttpmem sBmem' stmem' rfl sumem' sutp,
      ?_⟩
    simp
  case cong_fst Aeq Beq _ ihA ihB ihp _ sΓmem =>
    obtain ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    obtain ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper Aeq sΓmem sAmem)
    obtain ⟨_, sptpmem, sp, spmem, spmem', rfl⟩ := ihp sΓmem
    dsimp [ofTerm, ofType] at sptpmem
    simp_part at sptpmem ⊢
    have ⟨_, h, _, h', sptp⟩ := sptpmem
    cases Part.mem_unique h sAmem
    cases Part.mem_unique h' sBmem
    refine ⟨sA, sAmem,
      _,
      mem_ofTerm_fst sAmem sBmem spmem sptp,
      mem_ofTerm_fst sAmem' sBmem' spmem' sptp,
      ?_⟩
    simp
  case cong_snd A _ B _ p _ l l' Aeq Beq _ ihA ihB ihp sΓ sΓmem =>
    obtain ⟨sA, sAmem, sAmem'⟩ := ihA sΓmem
    obtain ⟨sB, sBmem, sBmem'⟩ := ihB (snoc_helper Aeq sΓmem sAmem)
    obtain ⟨_, sptpmem, sp, spmem, spmem', rfl⟩ := ihp sΓmem
    dsimp [ofTerm, ofType] at sptpmem
    simp_part at sptpmem ⊢
    have ⟨_, h, _, h', sptp⟩ := sptpmem
    cases Part.mem_unique h sAmem
    cases Part.mem_unique h' sBmem
    have llen := s.lt_slen_of_eqTp slen Aeq
    have l'len := s.lt_slen_of_eqTp slen Beq
    have fstmem := mem_ofTerm_fst sAmem sBmem spmem sptp
    refine ⟨_, mem_ofType_inst0 sBmem fstmem (mkFst_tp ..),
      _,
      mem_ofTerm_snd sAmem sBmem spmem sptp,
      mem_ofTerm_snd sAmem' sBmem' spmem' sptp,
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
      _, mem_ofTerm_app sBmem (mem_ofTerm_lam sAmem stmem) ?_ sumem sutp,
      ?_, ?_⟩
    . simp [sttp]
    . rw [mkApp_mkLam (t_tp := sttp)]
      exact mem_ofTerm_inst0 stmem sumem sutp
    . simp
  case fst_pair Awf _ _ _ ihA ihB iht ihu _ sΓmem =>
    have ⟨sA, sAmem, _⟩ := ihA sΓmem
    have ⟨sB, sBmem, _⟩ := ihB (snoc_helper Awf sΓmem sAmem)
    obtain ⟨_, sttpmem, st, stmem, _, rfl⟩ := iht sΓmem
    obtain ⟨_, sutpmem, su, sumem, _, rfl⟩ := ihu sΓmem
    cases Part.mem_unique sAmem sttpmem
    have := Part.mem_unique sutpmem (mem_ofType_inst0 sBmem stmem rfl)
    have := mem_ofTerm_pair sttpmem sBmem stmem rfl sumem this
    have := mem_ofTerm_fst sttpmem sBmem this (by simp)
    refine ⟨_, sAmem, _, this, ?_⟩
    simp [stmem]
  case snd_pair Awf _ _ _ ihA ihB iht ihu _ sΓmem =>
    have ⟨sA, sAmem, _⟩ := ihA sΓmem
    have ⟨sB, sBmem, _⟩ := ihB (snoc_helper Awf sΓmem sAmem)
    obtain ⟨_, sttpmem, st, stmem, _, rfl⟩ := iht sΓmem
    obtain ⟨_, sutpmem, su, sumem, _, rfl⟩ := ihu sΓmem
    cases Part.mem_unique sAmem sttpmem
    have := Part.mem_unique sutpmem (mem_ofType_inst0 sBmem stmem rfl)
    have := mem_ofTerm_pair sttpmem sBmem stmem rfl sumem this
    have := mem_ofTerm_snd sttpmem sBmem this (by simp)
    refine ⟨_, sutpmem, _, this, ?_⟩
    simp [sumem]
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
      ?_⟩
    simp [satp]
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

/-- Given `Γ, l, A` s.t. `Γ ⊢[l] A` and `sΓ = ⟦Γ⟧`, return `⟦A⟧_{sΓ}`. -/
def interpType
    {Γ : Ctx} {l : Nat} {A : Expr} (ΓA : Γ ⊢[l] A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    y(sΓ.1) ⟶ s[l].Ty :=
  (ofType sΓ l A).get <| by
    have ⟨_, h1, _, h2⟩ := (ofType_ofTerm_sound slen).2.1 ΓA
    cases Part.mem_unique sΓ_mem h1
    exact h2

end UHomSeqPiSigma
end NaturalModelBase
