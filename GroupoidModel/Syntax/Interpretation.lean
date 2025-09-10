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

namespace NaturalModel

variable {𝒞 : Type u} [SmallCategory 𝒞] [CartesianMonoidalCategory 𝒞]
open scoped MonoidalCategory

/-! ## Universe level bound helpers -/

section univBounds
variable {s : UHomSeq 𝒞} (slen : univMax ≤ s.length)
variable {χ : Type*} {E : Axioms χ} {Γ : Ctx χ} {A B t u : Expr χ} {l : Nat}
include slen

theorem _root_.EqTp.lt_slen (H : E ∣ Γ ⊢[l] A ≡ B) : l < s.length + 1 := by
  have := H.le_univMax
  omega

theorem _root_.WfTp.lt_slen (H : E ∣ Γ ⊢[l] A) : l < s.length + 1 :=
  (EqTp.refl_tp H).lt_slen slen

theorem _root_.EqTm.lt_slen (H : E ∣ Γ ⊢[l] t ≡ u : A) : l < s.length + 1 :=
  H.wf_tp.lt_slen slen

theorem _root_.WfTm.lt_slen (H : E ∣ Γ ⊢[l] t : A) : l < s.length + 1 :=
  H.wf_tp.lt_slen slen

end univBounds

namespace UHomSeq

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
variable {s : UHomSeq 𝒞}

-- Q : What would a `Lookup` `Prop` family for `ExtSeq` look like?
-- The purpose of adding it would be to totalize `var`, `tp`, and other functions.

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
  induction d generalizing σ <;> simp [substWk, NaturalModel.substWk_disp_assoc, *]

/-- `Γ.Aₖ.….A₀ ⊢ vₙ : Aₙ[↑ⁿ⁺¹]` -/
protected def var {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Tm)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].var A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.var llen n
    return ym(s[l'].disp A) ≫ v

/-- `Γ.Aₖ.….A₀ ⊢ Aₙ[↑ⁿ⁺¹]` -/
protected def tp {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Ty)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ ym(s[l'].disp A) ≫ A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.tp llen n
    return ym(s[l'].disp A) ≫ v

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
    . simp [ExtSeq.var, ExtSeq.tp, ← ih]

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
  induction e <;> (simp [ExtSeq.var, Part.bind_some_eq_map, Part.map_map, *]; rfl)

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
      simp only [← Functor.map_comp_assoc]
      simp [NaturalModel.substWk_disp]

end ExtSeq

/-! ## Contextual objects -/

-- Q: Should we get rid of `CObj` altogether, and generalize interpretation to `ExtSeq`s?
/-- A "contextual" object (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the extension sequence `[Aₙ₋₁ :: … :: A₀]`.

This kind of object can be destructured. -/
def CObj (s : UHomSeq 𝒞) : Type u := Σ Γ : 𝒞, s.ExtSeq (𝟙_ 𝒞) Γ

def nilCObj (s : UHomSeq 𝒞) : s.CObj :=
  ⟨𝟙_ 𝒞, .nil⟩

namespace CObj
variable {s : UHomSeq 𝒞}

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

@[simp]
theorem mem_var_zero {Γ : s.CObj} {l' l'len A l} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen 0 ↔
    ∃ l'l : l' = l, x = l'l ▸ s[l'].var A := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part; exact exists_congr fun _ => by subst l'; simp_part

@[simp]
theorem mem_var_succ {Γ : s.CObj} {l' l'len A l i} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen (i+1) ↔
    ∃ a ∈ Γ.var llen i, x = ym(s[l'].disp A) ≫ a := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part

theorem var_tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    (Γ.var llen i).map (· ≫ s[l].tp) = Γ.tp llen i :=
  Γ.2.var_tp llen i

end CObj
end UHomSeq

/-! ## Interpretation -/

/-- An interpretation of a signature consists of a semantic term for each named axiom.
This is the semantic equivalent of `Axioms χ`. -/
structure Interpretation (χ : Type*) (s : UHomSeq 𝒞) where
  ax (c : χ) (l : Nat) (_ : l < s.length + 1 := by get_elem_tactic) :
    Option (y(𝟙_ 𝒞) ⟶ s[l].Tm)
  -- We cannot state well-formedness yet: that needs `ofType`.

namespace Interpretation

variable {s : UHomSeq 𝒞} {χ : Type*} (I : Interpretation χ s)
variable [s.PiSeq] [s.SigSeq] [s.IdSeq]

mutual
/- Recall: cannot have `ofCtx` appearing in the output types
(that would be induction-recursion or something like it),
thus the context must be an *input*. -/
def ofType (Γ : s.CObj) (l : Nat) :
    Expr χ → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Ty)
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
    return lij ▸ s.mkSig ilen jlen A B
  | .Id _ A a0 a1, llen => do
    let A ← ofType Γ l A
    let a0 ← ofTerm Γ l a0
    let a1 ← ofTerm Γ l a1
    Part.assert (a0 ≫ s[l].tp = A) fun eq0 => do
    Part.assert (a1 ≫ s[l].tp = A) fun eq1 => do
    return s.mkId llen A a0 a1 eq0 eq1
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
    Expr χ → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Tm)
  | .ax c _, llen => do
    let some sc := I.ax c l | Part.assert False nofun
    return isTerminal_yUnit.from y(Γ.1) ≫ sc
  | .bvar i, llen => Γ.var llen i
  | .lam i j A e, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let e ← ofTerm (Γ.snoc ilen A) j e
    return lij ▸ s.mkLam ilen jlen A e
  | .app i _ B f a, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let f ← ofTerm Γ (max i l) f
    let a ← ofTerm Γ i a
    let B ← ofType (Γ.snoc ilen (a ≫ s[i].tp)) l B
    Part.assert (f ≫ s[max i l].tp = s.mkPi ilen llen (a ≫ s[i].tp) B) fun h =>
    return s.mkApp ilen llen _ B f h a rfl
  | .pair i j B t u, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let t ← ofTerm Γ i t
    let B ← ofType (Γ.snoc ilen (t ≫ s[i].tp)) j B
    let u ← ofTerm Γ j u
    Part.assert (u ≫ s[j].tp = ym(s[i].sec _ t rfl) ≫ B) fun u_tp =>
    return lij ▸ s.mkPair ilen jlen (t ≫ s[i].tp) B t rfl u u_tp
  | .fst _ j A B p, llen => do
    Part.assert (j < s.length + 1) fun jlen => do
    -- RB was so right
    let A ← ofType Γ l A
    let B ← ofType (Γ.snoc llen A) j B
    let p ← ofTerm Γ (max l j) p
    Part.assert (p ≫ s[max l j].tp = s.mkSig llen jlen A B) fun p_tp =>
    return s.mkFst llen jlen A B p p_tp
  | .snd i _ A B p, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) l B
    let p ← ofTerm Γ (max i l) p
    Part.assert (p ≫ s[max i l].tp = s.mkSig ilen llen A B) fun p_tp =>
    return s.mkSnd ilen llen A B p p_tp
  | .refl _ t, llen => do
    let t ← ofTerm Γ l t
    return s.mkRefl llen t
  | .idRec i _ t M r u h, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let t ← ofTerm Γ i t
    let A := t ≫ s[i].tp
    let M ← ofType ((Γ.snoc ilen A).snoc ilen _) l M
    let r ← ofTerm Γ l r
    Part.assert _ fun r_tp => do
    let u ← ofTerm Γ i u
    Part.assert (u ≫ s[i].tp = A) fun u_tp => do
    let h ← ofTerm Γ i h
    Part.assert (h ≫ s[i].tp = s.mkId ilen A t u rfl u_tp) fun h_tp => do
    return s.mkIdRec ilen llen A t rfl _ rfl M r r_tp u u_tp h h_tp
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

def ofCtx : Ctx χ → Part s.CObj
  | [] => return s.nilCObj
  | (A,l) :: Γ => do
    Part.assert (l < s.length + 1) fun llen => do
    let sΓ ← ofCtx Γ
    let sA ← I.ofType sΓ l A
    return sΓ.snoc llen sA

@[simp]
theorem mem_ofType_pi {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ I.ofType Γ l (.pi i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ I.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ I.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkPi ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_sigma {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ I.ofType Γ l (.sigma i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ I.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ I.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkSig ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_Id {Γ l i A a b} {llen : l < s.length + 1} {x} :
    x ∈ I.ofType Γ l (.Id i A a b) llen ↔
    ∃ (A' : y(Γ.fst) ⟶ s[l].Ty), A' ∈ I.ofType Γ l A ∧
    ∃ (a' : y(Γ.fst) ⟶ s[l].Tm), a' ∈ I.ofTerm Γ l a ∧
    ∃ (b' : y(Γ.fst) ⟶ s[l].Tm), b' ∈ I.ofTerm Γ l b ∧
    ∃ eq : a' ≫ s[l].tp = A',
    ∃ eq' : b' ≫ s[l].tp = A',
    x = s.mkId llen A' a' b' eq eq' := by
  dsimp only [ofType]; simp_part

@[simp]
theorem mem_ofType_el {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ I.ofType Γ l (.el t) llen ↔
    ∃ llen : l < s.length,
    ∃ A : y(Γ.1) ⟶ s[l+1].Tm, A ∈ I.ofTerm Γ (l+1) t ∧
    ∃ A_tp : A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1,
    x = s.el llen A A_tp := by
  dsimp only [ofType]; simp_part

@[simp]
theorem ofTerm_bvar {Γ l i} {llen : l < s.length + 1} :
    I.ofTerm Γ l (.bvar i) llen = Γ.var llen i := rfl

@[simp]
theorem mem_ofTerm_ax {Γ c A l} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.ax c A) llen ↔
    ∃ sc, I.ax c l = some sc ∧
    x = isTerminal_yUnit.from y(Γ.1) ≫ sc := by
  dsimp only [ofTerm]
  cases I.ax c l <;> simp

@[simp]
theorem mem_ofTerm_lam {Γ l i j A e} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.lam i j A e) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.1) ⟶ s[i].Ty), A' ∈ I.ofType Γ i A ∧
    ∃ (e' : y((Γ.snoc ilen A').1) ⟶ s[j].Tm), e' ∈ I.ofTerm (Γ.snoc ilen A') j e ∧
    x = lij ▸ s.mkLam ilen jlen A' e' := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_app {Γ l i j B f a} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.app i j B f a) llen ↔
    ∃ ilen : i < s.length + 1,
    ∃ f' : y(Γ.1) ⟶ s[max i l].Tm, f' ∈ I.ofTerm Γ (max i l) f ∧
    ∃ a' : y(Γ.1) ⟶ s[i].Tm, a' ∈ I.ofTerm Γ i a ∧
    ∃ A', ∃ eq : a' ≫ s[i].tp = A',
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[l].Ty,
      B' ∈ I.ofType (Γ.snoc ilen A') l B ∧
    ∃ h, x = s.mkApp ilen llen _ B' f' h a' eq := by
  dsimp only [ofTerm]; simp_part; simp only [exists_prop_eq']

@[simp]
theorem mem_ofTerm_pair {Γ l i j B t u} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.pair i j B t u) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ t' : y(Γ.1) ⟶ s[i].Tm, t' ∈ I.ofTerm Γ i t ∧
    ∃ A', ∃ eq : t' ≫ s[i].tp = A',
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[j].Ty,
      B' ∈ I.ofType (Γ.snoc ilen A') j B ∧
    ∃ u' : y(Γ.1) ⟶ s[j].Tm, u' ∈ I.ofTerm Γ j u ∧
    ∃ u_tp : u' ≫ s[j].tp = ym(s[i].sec _ t' eq) ≫ B',
    x = lij ▸ s.mkPair ilen jlen A' B' t' eq u' u_tp := by
  dsimp only [ofTerm]; simp only [exists_prop_eq']; simp_part
  exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_fst {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.fst i j A B p) llen ↔
    have ilen : l < s.length + 1 := by> omega
    ∃ jlen : j < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[l].Ty), A' ∈ I.ofType Γ l A ∧
    ∃ B' : y((Γ.snoc llen A').1) ⟶ s[j].Ty,
      B' ∈ I.ofType (Γ.snoc llen A') j B ∧
    ∃ p' : y(Γ.1) ⟶ s[max l j].Tm, p' ∈ I.ofTerm Γ (max l j) p ∧
    ∃ p_tp : p' ≫ s[max l j].tp = s.mkSig llen jlen A' B',
    x = s.mkFst llen jlen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_snd {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.snd i j A B p) llen ↔
    have llen : l < s.length + 1 := by> omega
    ∃ ilen : i < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ I.ofType Γ i A ∧
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[l].Ty,
      B' ∈ I.ofType (Γ.snoc ilen A') l B ∧
    ∃ p' : y(Γ.1) ⟶ s[max i l].Tm, p' ∈ I.ofTerm Γ (max i l) p ∧
    ∃ p_tp : p' ≫ s[max i l].tp = s.mkSig ilen llen A' B',
    x = s.mkSnd ilen llen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_refl {Γ l i t} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.refl i t) llen ↔
    ∃ t' ∈ I.ofTerm Γ l t llen, x = s.mkRefl llen t' := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_idRec {Γ l i j t M r u h} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.idRec i j t M r u h) llen ↔
    ∃ ilen : i < s.length + 1,
    ∃ t' : y(Γ.1) ⟶ s[i].Tm, t' ∈ I.ofTerm Γ i t ∧
    ∃ A', ∃ t_tp : t' ≫ s[i].tp = A',
    ∃ B' B_eq,
    ∃ M' : y(((Γ.snoc ilen A').snoc ilen B').1) ⟶ s[l].Ty,
      M' ∈ I.ofType ((Γ.snoc ilen A').snoc ilen B') l M ∧
    ∃ r' : y(Γ.1) ⟶ s[l].Tm, r' ∈ I.ofTerm Γ l r ∧
    ∃ r_tp,
    ∃ u' : y(Γ.1) ⟶ s[i].Tm, u' ∈ I.ofTerm Γ i u ∧
    ∃ u_tp : u' ≫ s[i].tp = A',
    ∃ h' : y(Γ.1) ⟶ s[i].Tm, h' ∈ I.ofTerm Γ i h ∧
    ∃ h_tp : h' ≫ s[i].tp = s.mkId ilen A' t' u' t_tp u_tp,
    x = s.mkIdRec ilen llen A' t' t_tp B' B_eq M' r' r_tp u' u_tp h' h_tp := by
  dsimp only [ofTerm]; simp_part; simp only [exists_prop_eq']

@[simp]
theorem mem_ofTerm_code {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ I.ofTerm Γ l (.code t) llen ↔
    ∃ i, ∃ li : l = i + 1,
    ∃ (t' : y(Γ.fst) ⟶ s[i].Ty), t' ∈ I.ofType Γ i t ∧
    x = li ▸ s.code (by> omega) t' := by
  dsimp only [ofTerm]; cases l <;> simp

@[simp]
theorem mem_ofType_univ {Γ l i} {llen : l < s.length + 1} {x} :
    x ∈ I.ofType Γ l (.univ i) llen ↔
    ∃ li : l = i + 1,
    x = li ▸ (s.homSucc i).wkU Γ.1 := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp] theorem ofCtx_nil : I.ofCtx [] = s.nilCObj := rfl

@[simp]
theorem mem_ofCtx_snoc {Γ A l sΓ'} : sΓ' ∈ I.ofCtx ((A,l) :: Γ) ↔
    ∃ sΓ ∈ I.ofCtx Γ, ∃ llen, ∃ sA ∈ I.ofType sΓ l A llen, sΓ' = sΓ.snoc llen sA := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

/-! ## Semantic substitutions -/

/-- An inductive characterization of those semantic substitutions
that appear in syntactic operations.
We use this as an auxiliary device
in the proof of semantic substitution admissibility.

The family with `full = false` characterizes renamings,
whereas `full = true` contains general substitutions
but where composition is limited to renamings on the left. -/
inductive CSb : (Δ Γ : s.CObj) → (Δ.1 ⟶ Γ.1) → (full : Bool := true) → Type _ where
  | id Γ (full : Bool := true) : CSb Γ Γ (𝟙 _) full
  | wk {Γ : s.CObj} {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty)
    (full : Bool := true) : CSb (Γ.snoc llen A) Γ (s[l].disp A) full
  | comp {Θ Δ Γ : s.CObj} {σ τ full} : CSb Θ Δ σ false → CSb Δ Γ τ full → CSb Θ Γ (σ ≫ τ) full
  | snoc' {Δ Γ : s.CObj} {σ full} (_ : CSb Δ Γ σ full) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e) (hf : ¬full → ∃ i, e = .bvar i)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ I.ofTerm Δ l e) :
    CSb Δ (Γ.snoc llen A) (s[l].substCons σ A se eq) full

namespace CSb
variable {I : Interpretation χ s}

def toSb {Δ Γ σ full} : I.CSb Δ Γ σ full → Nat → Expr χ
  | .id _ _ => .bvar
  | .wk _ _ _ => Expr.wk
  | .comp σ τ => Expr.comp σ.toSb τ.toSb
  | .snoc' σ _ _ e _ _ _ => Expr.snoc σ.toSb e

theorem toSb_is_bvar {Δ Γ σ} : ∀ (sσ : I.CSb Δ Γ σ false) i, ∃ j, sσ.toSb i = .bvar j
  | .id _ _, _ => ⟨_, rfl⟩
  | .wk _ _ _, _ => by simp [toSb]
  | .comp σ τ, i => by
    have ⟨j, eq⟩ := toSb_is_bvar τ i
    have ⟨k, eq'⟩ := toSb_is_bvar σ j
    simp [toSb, Expr.comp, eq, Expr.subst, eq']
  | .snoc' σ _ _ e hf _ _, i => by
    cases i <;> simp [toSb, Expr.snoc]
    · apply hf; simp
    · apply toSb_is_bvar

variable {Δ Γ : s.CObj} {σ : Δ.1 ⟶ Γ.1} {full : Bool}
  {l : Nat} (llen : l < s.length + 1)

def snoc (sσ : I.CSb Δ Γ σ) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ I.ofTerm Δ l e) :
    I.CSb Δ (Γ.snoc llen A) (s[l].substCons σ A se eq) :=
  snoc' sσ llen A e (by simp) eq H

@[simp] theorem snoc_toSb (sσ : I.CSb Δ Γ σ) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ I.ofTerm Δ l e) :
    (snoc sσ llen A e eq H).toSb = Expr.snoc sσ.toSb e := rfl

def sub1 {se : y(Γ.1) ⟶ s[l].Tm}
    (A : y(Γ.1) ⟶ s[l].Ty) (e) (eq : se ≫ s[l].tp = A) (H : se ∈ I.ofTerm Γ l e) :
    I.CSb Γ (Γ.snoc llen A) (s[l].sec A se eq) :=
  (CSb.id Γ).snoc llen A e (by simp [eq]) H

@[simp] theorem sub1_toSb {se : y(Γ.1) ⟶ s[l].Tm}
    (A : y(Γ.1) ⟶ s[l].Ty) (e) (eq : se ≫ s[l].tp = A) (H : se ∈ I.ofTerm Γ l e) :
    (sub1 llen A e eq H).toSb = Expr.toSb e := by
  simp [sub1, toSb, Expr.toSb]

def up {Δ Γ σ full} (sσ : I.CSb Δ Γ σ full)
    {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty)
    (A' := ym(σ) ≫ A) (eq : ym(σ) ≫ A = A' := by rfl) :
    I.CSb (Δ.snoc llen A') (Γ.snoc llen A) (s[l].substWk σ A _ eq) full := by
  refine ((CSb.wk _ _ false).comp sσ).snoc' _ _ (.bvar 0) (by simp) _ ?_
  simp [UHomSeq.CObj.var, UHomSeq.ExtSeq.var]

@[simp] theorem up_toSb {Δ Γ σ full} (sσ : I.CSb Δ Γ σ full)
     {l} {llen : l < s.length + 1} {A A'} {eq : ym(σ) ≫ A = A'} :
    (up sσ llen A _ eq).toSb = Expr.up sσ.toSb := by
  simp [up, toSb, Expr.up_eq_snoc]

end CSb

/-! ## Admissibility of substitution -/

open UHomSeq
variable (slen : univMax ≤ s.length)

theorem mem_ofType_ofTerm_subst' {full}
    (IH : full = true → ∀ {Δ Γ l} (llen : l < s.length + 1) {sσ} (σ : I.CSb Δ Γ sσ false) {se e},
      se ∈ I.ofTerm Γ l e llen → ym(sσ) ≫ se ∈ I.ofTerm Δ l (Expr.subst σ.toSb e) llen)
    {e l} (llen : l < s.length + 1)
    {Δ Γ : s.CObj} {sσ} (σ : I.CSb Δ Γ sσ full) {σ'} (eq : σ.toSb = σ') :
    (∀ {sA}, sA ∈ I.ofType Γ l e llen →
      ym(sσ) ≫ sA ∈ I.ofType Δ l (Expr.subst σ' e) llen) ∧
    (∀ {se}, se ∈ I.ofTerm Γ l e llen →
      ym(sσ) ≫ se ∈ I.ofTerm Δ l (Expr.subst σ' e) llen) := by
  subst σ'
  induction e generalizing Δ Γ l <;>
    (constructor <;> [intro sA H; intro se H] <;> try cases Part.notMem_none _ H)
  case pi.left ihA ihB =>
    obtain ⟨rfl, H⟩ := I.mem_ofType_pi.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkPi, mem_ofType_pi, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).1 hB
  case sigma.left ihA ihB =>
    obtain ⟨rfl, H⟩ := I.mem_ofType_sigma.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkSig, mem_ofType_sigma, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).1 hB
  case Id.left ihA iha ihb =>
    obtain := I.mem_ofType_Id.1 H; simp at H llen
    obtain ⟨A, hA, a, ha, b, hb, eq, eq', rfl⟩ := H
    simp only [Expr.subst, comp_mkId, mem_ofType_Id]
    refine ⟨_, (ihA llen σ).1 hA, _, (iha llen σ).2 ha, _, (ihb llen σ).2 hb, ?_, ?_, rfl⟩
      <;> simp [eq, eq']
  case el.left ih =>
    obtain ⟨llen', A, hA, tp, rfl⟩ := I.mem_ofType_el.1 H
    simp only [Expr.subst, mem_ofType_el, UHomSeq.comp_el, exists_true_left, llen']
    exact ⟨_, (ih (by omega) σ).2 hA, by simp [tp], rfl⟩
  case univ.left =>
    obtain ⟨rfl, H⟩ := I.mem_ofType_univ.1 H; simp at H llen; subst H
    simp only [Expr.subst, mem_ofType_univ, exists_true_left, UHom.comp_wkU]

  case ax =>
    simp only [Expr.subst, mem_ofTerm_ax] at H ⊢
    have ⟨_, ceq, ueq⟩ := H
    exact ⟨_, ceq, by simp [ueq]⟩
  case bvar i =>
    simp [ofTerm_bvar] at H
    simp [Expr.subst]
    induction σ generalizing i with simp [CSb.toSb, *]
    | wk => exact CObj.mem_var_succ.2 ⟨_, ‹_›, rfl⟩
    | @comp _ _ _ _ _ full σ τ ih1 ih2 =>
      simp [Expr.comp]
      cases full with
      | false =>
        simp at ih1 ih2; clear IH
        have ⟨j, eq⟩ := CSb.toSb_is_bvar τ i
        simp [eq, Expr.subst]
        refine ih1 _ ?_
        rw [← ofTerm_bvar, ← eq]
        exact ih2 _ H
      | true => exact IH rfl _ _ (ih2 IH _ H)
    | snoc' _ _ _ _ _ _ _ ih1 =>
      induction i with
      | zero =>
        obtain ⟨rfl, H⟩ := CObj.mem_var_zero.1 H
        simp at H; subst H; simpa
      | succ i ih2 =>
        obtain ⟨_, H', rfl⟩ := CObj.mem_var_succ.1 H
        simp [ih1 IH i H']
  case lam ihA ihB =>
    obtain ⟨rfl, H⟩ := I.mem_ofTerm_lam.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkLam, mem_ofTerm_lam, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).2 hB
  case app ihB ihf iha =>
    obtain ⟨llen', f, hf, a, ha, _, rfl, B, hB, eq, rfl⟩ := I.mem_ofTerm_app.1 H
    simp only [Expr.subst, comp_mkApp, mem_ofTerm_app]
    refine ⟨‹_›, _, (ihf (by simp [*]) σ).2 hf, _, (iha llen' σ).2 ha, _, rfl, _, ?_, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen (σ.up llen' _ _ (Category.assoc ..).symm)).1 hB
    · simp [*, comp_mkPi]
      congr! 1
  case pair ihB iht ihu =>
    obtain ⟨rfl, H⟩ := I.mem_ofTerm_pair.1 H; simp at H llen
    obtain ⟨t, ht, B, hB, u, hu, eq, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkPair, mem_ofTerm_pair, exists_true_left]
    refine ⟨_, (iht llen.1 σ).2 ht, _, rfl, _, ?_, _, (ihu llen.2 σ).2 hu, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 _ _ (Category.assoc ..).symm)).1 hB
    · simp [*]; rw [← Functor.map_comp_assoc, comp_sec, ← Functor.map_comp_assoc]; congr! 0
  case fst ihA ihB ihp =>
    obtain ⟨jlen, A, hA, B, hB, p, hp, eq, rfl⟩ := I.mem_ofTerm_fst.1 H
    simp only [Expr.subst, comp_mkFst, mem_ofTerm_fst]
    refine ⟨jlen, _, (ihA llen σ).1 hA, _, ?_, _, (ihp (by simp [*]) σ).2 hp, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB jlen (σ.up llen _)).1 hB
    · simp [*, comp_mkSig]
  case snd ihA ihB ihp =>
    obtain ⟨ilen, A, hA, B, hB, p, hp, eq, rfl⟩ := I.mem_ofTerm_snd.1 H
    simp only [Expr.subst, comp_mkSnd, mem_ofTerm_snd]
    refine ⟨ilen, _, (ihA ilen σ).1 hA, _, ?_, _, (ihp (by simp [*]) σ).2 hp, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen (σ.up ilen _)).1 hB
    · simp [*, comp_mkSig]
  case refl iht =>
    obtain ⟨t, ht, rfl⟩ := I.mem_ofTerm_refl.1 H
    simp only [Expr.subst, comp_mkRefl, mem_ofTerm_refl]
    exact ⟨_, (iht llen σ).2 ht, rfl⟩
  case idRec iht ihM ihr ihu ihh =>
    obtain ⟨ilen, t, ht, A, Aeq, B, Beq, M, hM, r, hr, rtp, u, hu, utp, h, hh, htp, rfl⟩ :=
      I.mem_ofTerm_idRec.1 H
    simp only [Expr.subst, mem_ofTerm_idRec]
    refine ⟨ilen, _, (iht ilen σ).2 ht, _, by simp [Aeq], _, ?_, _, ?_,
      _, (ihr llen σ).2 hr, _, _, (ihu ilen σ).2 hu, _, _, (ihh ilen σ).2 hh, _,
      comp_mkIdRec (σA_eq := rfl) (σB_eq := rfl) ..⟩
    · simp [← Beq, comp_mkId (eq := rfl)]
      congr 1 <;> simp only [← Functor.map_comp_assoc, substWk_disp]
    · rw [← CSb.up_toSb, ← CSb.up_toSb]; exact (ihM llen ((σ.up ilen _).up ilen _ _ _)).1 hM
  case code ihA =>
    obtain ⟨l, rfl, H⟩ := I.mem_ofTerm_code.1 H; simp at H llen
    obtain ⟨A, hA, rfl⟩ := H; clear H
    simp only [Expr.subst, UHomSeq.comp_code, mem_ofTerm_code]
    refine ⟨_, rfl, _, (ihA (by omega) σ).1 hA, ?_⟩; simp

-- FIXME: I think `_ ∈ ofType/ofTerm _ l .. ⇒ l < s.length + 1`,
-- so we should be able to drop that argument everywhere;
-- semantic terms are 'well-universed'.

theorem mem_ofType_ofTerm_subst {e l} (llen : l < s.length + 1)
    {Δ Γ : s.CObj} {sσ full} (σ : I.CSb Δ Γ sσ full) {σ'} (eq : σ.toSb = σ') :
    (∀ {sA}, sA ∈ I.ofType Γ l e llen →
      ym(sσ) ≫ sA ∈ I.ofType Δ l (Expr.subst σ' e) llen) ∧
    (∀ {se}, se ∈ I.ofTerm Γ l e llen →
      ym(sσ) ≫ se ∈ I.ofTerm Δ l (Expr.subst σ' e) llen) := by
  refine I.mem_ofType_ofTerm_subst' (fun _ _ _ _ llen sσ σ se i => ?_) llen σ eq
  exact (I.mem_ofType_ofTerm_subst' (by simp) llen σ rfl).2

theorem mem_ofType_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ I.ofType Γ l e hl) :
    ym(s[l'].disp X) ≫ se ∈ I.ofType (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (I.mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).1 H

theorem mem_ofType_of_isClosed {e l} (e_cl : e.isClosed)
    (Γ : s.CObj) (hl : l < s.length + 1) {se} (se_mem : se ∈ I.ofType s.nilCObj l e hl) :
    isTerminal_yUnit.from y(Γ.1) ≫ se ∈ I.ofType Γ l e hl := by
  rcases Γ with ⟨_, ext⟩
  induction ext
  . convert se_mem; simp
  . rename_i X se_mem
    have := I.mem_ofType_wk (X := X) (by omega) se_mem
    convert this using 1 <;>
      simp [e.subst_of_isClosed _ e_cl, UHomSeq.CObj.snoc]

theorem mem_ofTerm_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ I.ofTerm Γ l e hl) :
    ym(s[l'].disp X) ≫ se ∈ I.ofTerm (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (I.mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).2 H

theorem mem_ofType_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ I.ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ I.ofType (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ I.ofType Γ l (Expr.subst a.toSb e) hl :=
  (I.mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).1 H

theorem mem_ofTerm_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ I.ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ I.ofTerm (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ I.ofTerm Γ l (Expr.subst a.toSb e) hl :=
  (I.mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).2 H

/-! ## Soundness of interpretation -/

theorem tp_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ I.ofCtx Γ) :
    ∃ llen, ∃ sA ∈ sΓ.tp llen i, sA ∈ I.ofType sΓ l A llen := by
  induction H generalizing sΓ with (
    obtain ⟨_, hΓ', _, _, hB, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ
    simp [UHomSeq.CObj.tp, UHomSeq.ExtSeq.tp, *] at *)
  | zero => exact I.mem_ofType_wk _ hB
  | succ _ _ _ ih =>
    have ⟨_, _, _, _⟩ := ih hΓ'
    exact ⟨‹_›, _, ⟨_, ‹_›, rfl⟩, I.mem_ofType_wk _ ‹_›⟩

theorem var_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ I.ofCtx Γ) :
    ∃ llen, ∃ st ∈ sΓ.var llen i, st ≫ s[l].tp ∈ I.ofType sΓ l A llen := by
  have ⟨llen, _, h1, h2⟩ := I.tp_sound H hΓ
  simp [← UHomSeq.CObj.var_tp] at h1
  obtain ⟨_, h1, rfl⟩ := h1
  exact ⟨llen, _, h1, h2⟩

/- The inductive soundness proof takes very long to typecheck,
so we state the inductive hypotheses as definitions
and break the inductive cases out into many small lemmas. -/

def WfCtxIH Γ := ∃ sΓ, sΓ ∈ I.ofCtx Γ
def WfTpIH Γ l A := ∃ sΓ ∈ I.ofCtx Γ, ∃ llen, ∃ sA, sA ∈ I.ofType sΓ l A llen
def EqTpIH Γ l A B := ∃ sΓ ∈ I.ofCtx Γ, ∃ llen,
  ∃ sA ∈ I.ofType sΓ l A llen, sA ∈ I.ofType sΓ l B llen
def WfTmIH Γ l A t := ∃ sΓ ∈ I.ofCtx Γ, ∃ llen,
  ∃ sA ∈ I.ofType sΓ l A llen, ∃ st ∈ I.ofTerm sΓ l t llen, st ≫ s[l].tp = sA
def EqTmIH Γ l A t u := ∃ sΓ ∈ I.ofCtx Γ, ∃ llen,
  ∃ sA ∈ I.ofType sΓ l A llen, ∃ st ∈ I.ofTerm sΓ l t llen,
    st ∈ I.ofTerm sΓ l u llen ∧ st ≫ s[l].tp = sA

variable {I}

theorem EqTpIH.left {Γ l A B} : I.EqTpIH Γ l A B → I.WfTpIH Γ l A
  | ⟨_, hΓ, _, _, hA, _⟩ => ⟨_, hΓ, _, _, hA⟩

theorem WfTpIH.refl {Γ l A} : I.WfTpIH Γ l A → I.EqTpIH Γ l A A
  | ⟨_, hΓ, _, _, hA⟩ => ⟨_, hΓ, _, _, hA, hA⟩

theorem EqTpIH.symm {Γ A A' l} : I.EqTpIH Γ l A A' → I.EqTpIH Γ l A' A
  | ⟨_, hΓ, hl, _, hA, hA'⟩ => ⟨_, hΓ, hl, _, hA', hA⟩

theorem EqTmIH.left {Γ l A t u} : I.EqTmIH Γ l A t u → I.WfTmIH Γ l A t
  | ⟨_, hΓ, _, _, hA, _, ht, _, eq⟩ => ⟨_, hΓ, _, _, hA, _, ht, eq⟩

theorem WfTmIH.refl {Γ l A t} : I.WfTmIH Γ l A t → I.EqTmIH Γ l A t t
  | ⟨_, hΓ, _, _, hA, _, ht, eq⟩ => ⟨_, hΓ, _, _, hA, _, ht, ht, eq⟩

theorem EqTmIH.symm {Γ l A t u} : I.EqTmIH Γ l A t u → I.EqTmIH Γ l A u t
  | ⟨_, hΓ, _, _, hA, _, ht, hu, tp⟩ => ⟨_, hΓ, _, _, hA, _, hu, ht, tp⟩

theorem WfCtxIH.nil : I.WfCtxIH [] := by simp [WfCtxIH]

theorem WfCtxIH.snoc {Γ A l} : I.WfTpIH Γ l A → I.WfCtxIH ((A, l) :: Γ)
  | ⟨_, hΓ, llen, _, hA⟩ => ⟨_, I.mem_ofCtx_snoc.2 ⟨_, hΓ, llen, _, hA, rfl⟩⟩

include slen in
theorem WfTpIH.univ {Γ l} (_ : l < univMax) : I.WfCtxIH Γ → I.WfTpIH Γ (l + 1) (Expr.univ l)
  | ⟨_, hΓ⟩ => ⟨_, hΓ, by omega, _, I.mem_ofType_univ.2 ⟨rfl, rfl⟩⟩

theorem EqTpIH.pi {Γ A A' B B' l l'} :
    I.EqTpIH Γ l A A' → I.EqTpIH ((A, l) :: Γ) l' B B' →
    I.EqTpIH Γ (max l l') (Expr.pi l l' A B) (Expr.pi l l' A' B')
  | ⟨_, hΓ, _, _, hA, hA'⟩, ⟨_, hΓ', _, _, hB, hB'⟩ => by
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA₁ hA
    exact ⟨_, hΓ, by omega, _,
      I.mem_ofType_pi.2 ⟨rfl, _, hA, _, hB, rfl⟩,
      I.mem_ofType_pi.2 ⟨rfl, _, hA', _, hB', rfl⟩⟩

theorem EqTpIH.sigma {Γ A A' B B' l l'} :
    I.EqTpIH Γ l A A' → I.EqTpIH ((A, l) :: Γ) l' B B' →
    I.EqTpIH Γ (max l l') (Expr.sigma l l' A B) (Expr.sigma l l' A' B')
  | ⟨_, hΓ, _, _, hA, hA'⟩, ⟨_, hΓ', _, _, hB, hB'⟩ => by
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA₁ hA
    exact ⟨_, hΓ, by omega, _,
      I.mem_ofType_sigma.2 ⟨rfl, _, hA, _, hB, rfl⟩,
      I.mem_ofType_sigma.2 ⟨rfl, _, hA', _, hB', rfl⟩⟩

theorem EqTpIH.Id {Γ A A' t t' u u' l} :
    I.EqTpIH Γ l A A' → I.EqTmIH Γ l A t t' → I.EqTmIH Γ l A u u' →
    I.EqTpIH Γ l (Expr.Id l A t u) (Expr.Id l A' t' u')
  | ⟨_, hΓ, _, _, hA, hA'⟩,
    ⟨_, hΓ₁, _, _, hA₁, _, ht, ht', ttp⟩,
    ⟨_, hΓ₂, _, _, hA₂, _, hu, hu', utp⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hΓ hΓ₂
    cases Part.mem_unique hA hA₂
    exact ⟨_, hΓ, ‹_›, _,
      I.mem_ofType_Id.2 ⟨_, hA, _, ht, _, hu, ttp, utp, rfl⟩,
      I.mem_ofType_Id.2 ⟨_, hA', _, ht', _, hu', ttp, utp, rfl⟩⟩

theorem EqTpIH.el {Γ A A' l} : I.EqTmIH Γ (l + 1) (Expr.univ l) A A' → I.EqTpIH Γ l A.el A'.el
  | ⟨_, hΓ, _, _, hA, _, ht, ht', ttp⟩ => by
    obtain ⟨_, eq⟩ := I.mem_ofType_univ.1 hA
    simp at eq; subst eq
    exact ⟨_, ‹_›, _, _,
      I.mem_ofType_el.2 ⟨_, _, ht, ttp, rfl⟩,
      I.mem_ofType_el.2 ⟨_, _, ht', ttp, rfl⟩⟩

include slen in
theorem EqTpIH.el_code {Γ A l} (_ : l < univMax) : I.WfTpIH Γ l A → I.EqTpIH Γ l A.code.el A
  | ⟨_, hΓ', _, _, hA⟩ =>
    ⟨_, ‹_›, ‹_›, _,
      I.mem_ofType_el.2 ⟨by omega, _,
        I.mem_ofTerm_code.2 ⟨_, rfl, _, hA, by simp; rfl⟩, s.code_tp .., rfl⟩,
      by rwa [s.el_code]⟩

theorem EqTpIH.trans {Γ A A' A'' l} : I.EqTpIH Γ l A A' → I.EqTpIH Γ l A' A'' → I.EqTpIH Γ l A A''
  | ⟨_, hΓ, hl, _, hA, hA'⟩, ⟨_, hΓ₁, _, _, hA'₁, hA''⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA' hA'₁
    exact ⟨_, hΓ, hl, _, hA, hA''⟩

theorem WfTmIH.bvar {Γ A i l} (H : Lookup Γ i A l) : I.WfCtxIH Γ → I.WfTmIH Γ l A (Expr.bvar i)
  | ⟨_, hΓ⟩ =>
    have ⟨llen, _, h1, h2⟩ := I.var_sound H hΓ
    ⟨_, ‹_›, llen, _, h2, _, h1, rfl⟩

theorem EqTmIH.lam {Γ A A' B t t' l l'} :
    I.EqTpIH Γ l A A' → I.EqTmIH ((A, l) :: Γ) l' B t t' →
    I.EqTmIH Γ (max l l') (Expr.pi l l' A B) (Expr.lam l l' A t) (Expr.lam l l' A' t')
  | ⟨_, hΓ, _, _, hA, hA'⟩, ⟨_, hΓ', _, _, hB, _, ht, ht', ttp⟩ => by
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    exact ⟨_, hΓ, _, _, I.mem_ofType_pi.2 ⟨rfl, _, hA, _, hB, by simp⟩, _,
      I.mem_ofTerm_lam.2 ⟨rfl, _, hA, _, ht, by simp⟩,
      I.mem_ofTerm_lam.2 ⟨rfl, _, hA', _, ht', by simp⟩, mkLam_tp (t_tp := ttp) ..⟩

theorem EqTmIH.app {Γ A B B' f f' a a' l l'} :
    I.EqTpIH ((A, l) :: Γ) l' B B' →
    I.EqTmIH Γ (max l l') (Expr.pi l l' A B) f f' → I.EqTmIH Γ l A a a' →
    I.EqTmIH Γ l' (Expr.subst a.toSb B) (Expr.app l l' B f a) (Expr.app l l' B' f' a')
  | ⟨_, hΓ', _, _, hB, hB'⟩, ⟨_, hΓ, _, _, hF, _, hf, hf', ftp⟩,
    ⟨_, hΓ₁, _, _, hA, _, ha, ha', atp⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    refine ⟨_, hΓ, _, _, I.mem_ofType_toSb _ ha _ hB, _,
      I.mem_ofTerm_app.2 ⟨_, _, hf, _, ha, _, atp, _, hB, ?a, rfl⟩,
      I.mem_ofTerm_app.2 ⟨_, _, hf', _, ha', _, atp, _, hB', ?a, rfl⟩,
      mkApp_tp ..⟩
    obtain ⟨_, _, hA₁, _, hB₁, eq⟩ := I.mem_ofType_pi.1 hF; simp at eq
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hB hB₁
    rwa [ftp]

theorem EqTmIH.pair {Γ A B B' t t' u u' l l'} :
    I.EqTpIH ((A, l) :: Γ) l' B B' →
    I.EqTmIH Γ l A t t' → I.EqTmIH Γ l' (Expr.subst t.toSb B) u u' →
    I.EqTmIH Γ (max l l') (Expr.sigma l l' A B) (Expr.pair l l' B t u) (Expr.pair l l' B' t' u')
  | ⟨_, hΓ', _, _, hB, hB'⟩, ⟨_, hΓ, _, _, hA, _, ht, ht', ttp⟩,
    ⟨_, hΓ₁, _, _, hBt, _, hu, hu', utp⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    refine ⟨_, hΓ, by omega, _,
      I.mem_ofType_sigma.2 ⟨rfl, _, hA, _, hB, by simp; rfl⟩, _,
      I.mem_ofTerm_pair.2 ⟨rfl, _, ht, _, ttp, _, hB, _, hu, ?a, by simp; rfl⟩,
      I.mem_ofTerm_pair.2 ⟨rfl, _, ht', _, ttp, _, hB', _, hu', ?a, by simp⟩,
      mkPair_tp ..⟩
    exact utp ▸ Part.mem_unique hBt (I.mem_ofType_toSb _ ht _ hB)

theorem EqTmIH.fst_snd {Γ A A' B B' p p' l l'} :
    I.EqTpIH Γ l A A' → I.EqTpIH ((A, l) :: Γ) l' B B' →
    I.EqTmIH Γ (max l l') (Expr.sigma l l' A B) p p' →
    I.EqTmIH Γ l A (Expr.fst l l' A B p) (Expr.fst l l' A' B' p') ∧
    I.EqTmIH Γ l' (Expr.subst (Expr.fst l l' A B p).toSb B)
      (Expr.snd l l' A B p) (Expr.snd l l' A' B' p')
  | ⟨_, hΓ, _, _, hA, hA'⟩, ⟨_, hΓ', _, _, hB, hB'⟩,
    ⟨_, hΓ₁, _, _, hP, _, hp, hp', ptp⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    refine ⟨
      ⟨_, hΓ, _, _, hA, _,
        I.mem_ofTerm_fst.2 ⟨_, _, hA, _, hB, _, hp, ?a, rfl⟩,
        I.mem_ofTerm_fst.2 ⟨_, _, hA', _, hB', _, hp', ?a, rfl⟩,
        mkFst_tp ..⟩,
      ⟨_, hΓ, _, _,
        I.mem_ofType_toSb _ (I.mem_ofTerm_fst.2 ⟨_, _, hA, _, hB, _, hp, ?a, rfl⟩) _ hB, _,
        I.mem_ofTerm_snd.2 ⟨_, _, hA, _, hB, _, hp, ?a, rfl⟩,
        I.mem_ofTerm_snd.2 ⟨_, _, hA', _, hB', _, hp', ?a, rfl⟩,
        mkSnd_tp ..⟩⟩
    obtain ⟨_, _, hA₁, _, hB₁, eq⟩ := I.mem_ofType_sigma.1 hP; simp at eq
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hB hB₁
    rwa [ptp]

theorem EqTmIH.refl_tm {Γ A t t' l} :
    I.EqTmIH Γ l A t t' → I.EqTmIH Γ l (Expr.Id l A t t) (Expr.refl l t) (Expr.refl l t')
  | ⟨_, hΓ, _, _, hA, _, ht, ht', ttp⟩ => by
    exact ⟨_, hΓ, _, _,
      I.mem_ofType_Id.2 ⟨_, hA, _, ht, _, ht, ttp, ttp, rfl⟩, _,
      I.mem_ofTerm_refl.2 ⟨_, ht, rfl⟩,
      I.mem_ofTerm_refl.2 ⟨_, ht', rfl⟩,
      mkRefl_tp ..⟩

theorem EqTmIH.idRec {Γ A M M' t t' r r' u u' h h' l l'} :
    I.EqTmIH Γ l A t t' →
    I.EqTpIH ((.Id l (.subst .wk A) (.subst .wk t) (.bvar 0), l) :: (A, l) :: Γ) l' M M' →
    I.EqTmIH Γ l' (.subst (.snoc t.toSb (.refl l t)) M) r r' →
    I.EqTmIH Γ l A u u' →
    I.EqTmIH Γ l (.Id l A t u) h h' →
    I.EqTmIH Γ l' (.subst (.snoc u.toSb h) M)
      (.idRec l l' t M r u h) (.idRec l l' t' M' r' u' h') := by
  intro ⟨_, hΓ, _, _, hA, _, ht, ht', ttp⟩ ⟨_, hΓ', _, _, hM, hM'⟩
    ⟨_, hΓ₁, _, _, hR, _, hr, hr', rtp⟩ ⟨_, hΓ₂, _, _, hA₁, _, hu, hu', utp⟩
    ⟨_, hΓ₃, _, _, hH, _, hh, hh', htp⟩
  cases Part.mem_unique hΓ hΓ₁
  cases Part.mem_unique hΓ hΓ₂
  cases Part.mem_unique hΓ hΓ₃
  cases Part.mem_unique hA hA₁
  obtain ⟨_, hΓ'', _, B, hB, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
  obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ''
  cases Part.mem_unique hΓ hΓ₁
  cases Part.mem_unique hA hA₁
  obtain ⟨_, sA, _, st, _, hv, stp, vtp, Beq⟩ := I.mem_ofType_Id.1 hB
  have sAeq := Part.mem_unique sA (I.mem_ofType_wk _ hA)
  cases Part.mem_unique (I.mem_ofTerm_wk _ ht) st
  obtain ⟨_, hv⟩ := CObj.mem_var_zero.1 (I.ofTerm_bvar ▸ hv :); simp at hv; subst hv
  obtain ⟨_, hA₁, _, ht₁, _, hu₁, _, _, rfl⟩ := I.mem_ofType_Id.1 hH
  cases Part.mem_unique hA hA₁
  cases Part.mem_unique ht ht₁
  cases Part.mem_unique hu hu₁
  refine ⟨_, hΓ, _, _,
    (I.mem_ofType_ofTerm_subst _ (.snoc (.sub1 _ _ _ utp hu) _ _ _ ?_ hh) ?_).1 hM, _,
    I.mem_ofTerm_idRec.2 ⟨_, _, ht, _, ttp, B, ?b, _, hM, _, hr, ?a, _, hu, utp, _, hh, htp, rfl⟩,
    I.mem_ofTerm_idRec.2 ⟨_, _, ht', _, ttp, B, ?b, _, hM', _, hr', ?a, _, hu', utp, _, hh', htp, rfl⟩,
    mkIdRec_tp ..⟩
  · rw [htp, Beq, comp_mkId]
    · congr 1 <;> simp
    · simp [sAeq]
  · simp
  · simp [Beq, sAeq]
  · refine rtp ▸ Part.mem_unique hR ?_
    refine (I.mem_ofType_ofTerm_subst _
      (.snoc (.sub1 _ _ _ ttp ht) _ _ (.refl l t) _ ?_) ?_).1 hM
    · exact I.mem_ofTerm_refl.2 ⟨_, ht, rfl⟩
    · simp

include slen in
theorem EqTmIH.code {Γ A A' l} (_ : l < univMax) :
    I.EqTpIH Γ l A A' → I.EqTmIH Γ (l + 1) (Expr.univ l) A.code A'.code
  | ⟨_, hΓ, _, _, hA, hA'⟩ =>
    ⟨_, hΓ, by omega, _,
      I.mem_ofType_univ.2 ⟨rfl, by simp⟩, _,
      I.mem_ofTerm_code.2 ⟨_, rfl, _, hA, by simp; rfl⟩,
      I.mem_ofTerm_code.2 ⟨_, rfl, _, hA', by simp⟩,
      s.code_tp ..⟩

theorem EqTmIH.app_lam {Γ A B t u l l'} :
    I.WfTmIH ((A, l) :: Γ) l' B t → I.WfTmIH Γ l A u →
    I.EqTmIH Γ l' (Expr.subst u.toSb B) (Expr.app l l' B (Expr.lam l l' A t) u)
      (Expr.subst u.toSb t)
  | ⟨_, hΓ', _, _, hB, _, ht, ttp⟩, ⟨_, hΓ, _, _, hA, _, hu, utp⟩ => by
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    exact ⟨_, hΓ, _, _, I.mem_ofType_toSb _ hu utp hB, _,
      I.mem_ofTerm_app.2 ⟨_, _,
        I.mem_ofTerm_lam.2 ⟨rfl, _, hA, _, ht, by simp⟩, _, hu, _, utp, _, hB,
        s.mkLam_tp (t_tp := ttp) ..,
        (s.mkApp_mkLam (t_tp := ttp) ..).symm⟩,
      I.mem_ofTerm_toSb _ hu _ ht, by simp [ttp]⟩

theorem EqTmIH.fst_snd_pair {Γ A B t u l l'} :
    I.WfTpIH ((A, l) :: Γ) l' B → I.WfTmIH Γ l A t → I.WfTmIH Γ l' (Expr.subst t.toSb B) u →
    I.EqTmIH Γ l A (Expr.fst l l' A B (Expr.pair l l' B t u)) t ∧
    I.EqTmIH Γ l' (Expr.subst t.toSb B) (Expr.snd l l' A B (Expr.pair l l' B t u)) u
  | ⟨_, hΓ', _, _, hB⟩, ⟨_, hΓ, _, _, hA, _, ht, ttp⟩, ⟨_, hΓ₁, _, _, hU, _, hu, utp⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hU (I.mem_ofType_toSb _ ht ttp hB)
    refine
      have hp := I.mem_ofTerm_pair.2 ⟨rfl, _, ht, _, ttp, _, hB, _, hu, utp, by simp⟩
      have tp := mkPair_tp (u_tp := utp) ..
      ⟨⟨_, hΓ, _, _, hA, _,
        I.mem_ofTerm_fst.2 ⟨_, _, hA, _, hB, _, hp, tp, (mkFst_mkPair ..).symm⟩, ht, ttp⟩,
       ⟨_, hΓ, _, _, I.mem_ofType_toSb _ ht ttp hB, _,
        I.mem_ofTerm_snd.2 ⟨_, _, hA, _, hB, _, hp, tp, (mkSnd_mkPair ..).symm⟩, hu, utp⟩⟩

theorem EqTmIH.idRec_refl {Γ A M t r l l'} :
    I.WfTmIH Γ l A t →
    I.WfTpIH ((.Id l (.subst .wk A) (.subst .wk t) (.bvar 0), l) :: (A, l) :: Γ) l' M →
    I.WfTmIH Γ l' (.subst (.snoc t.toSb (.refl l t)) M) r →
    I.EqTmIH Γ l' (.subst (.snoc t.toSb (.refl l t)) M)
      (.idRec l l' t M r t (.refl l t)) r := by
  intro ⟨_, hΓ, _, _, hA, _, ht, ttp⟩ ⟨_, hΓ', _, _, hM⟩ ⟨_, hΓ₁, _, _, hR, _, hr, rtp⟩
  cases Part.mem_unique hΓ hΓ₁
  obtain ⟨_, hΓ'', _, B, hB, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ'
  obtain ⟨_, hΓ₁, _, _, hA₁, rfl⟩ := I.mem_ofCtx_snoc.1 hΓ''
  cases Part.mem_unique hΓ hΓ₁
  cases Part.mem_unique hA hA₁
  obtain ⟨_, sA, _, st, _, hv, stp, vtp, Beq⟩ := I.mem_ofType_Id.1 hB
  have sAeq := Part.mem_unique sA (I.mem_ofType_wk _ hA)
  cases Part.mem_unique (I.mem_ofTerm_wk _ ht) st
  obtain ⟨_, hv⟩ := CObj.mem_var_zero.1 (I.ofTerm_bvar ▸ hv :); simp at hv; subst hv
  refine
    have h1 := I.mem_ofTerm_refl.2 ⟨_, ht, rfl⟩
    have h2 := mkRefl_tp ..
    have sM := (I.mem_ofType_ofTerm_subst _
      (.snoc (.sub1 _ _ _ ttp ht) _ _ (.refl l t) (h2 ▸ ?_) h1) (by simp)).1 hM
    have sr := rtp ▸ Part.mem_unique hR sM
    have ir := I.mem_ofTerm_idRec.2 ⟨_, _, ht, _, ttp, B, by simp [Beq, sAeq],
      _, hM, _, hr, sr, _, ht, ttp, _, h1, h2, (mkIdRec_mkRefl ..).symm⟩
    ⟨_, hΓ, _, _, sM, _, ir, hr, sr⟩
  simp [Beq, comp_mkId, sAeq]

theorem EqTmIH.lam_app {Γ A B f l l'} :
    I.WfTmIH Γ (max l l') (.pi l l' A B) f →
    I.EqTmIH Γ (max l l') (.pi l l' A B) f
      (.lam l l' A (.app l l' (.subst (.up .wk) B) (.subst .wk f) (.bvar 0)))
  | ⟨_, hΓ, _, _, hF, _, hf, ftp⟩ => by
    obtain ⟨_, _, hA, _, hB, eq⟩ := I.mem_ofType_pi.1 hF; simp at eq; subst eq
    refine
      have sB := (I.mem_ofType_ofTerm_subst _ (.up (.wk _ _) _ _ _ rfl) (CSb.up_toSb _)).1 hB
      have hv := I.ofTerm_bvar ▸ CObj.mem_var_zero.2 ⟨rfl, by simp⟩
      have hl := I.mem_ofTerm_lam.2 ⟨rfl, _, hA, _,
        I.mem_ofTerm_app.2 ⟨_, _, I.mem_ofTerm_wk _ hf, _, hv, _, by simp, _, sB, ?_, rfl⟩,
        (s.etaExpand_eq (f_tp := ftp) ..).symm⟩
      ⟨_, hΓ, _, _, hF, _, hf, hl, ftp⟩
    simp [ftp, comp_mkPi]

theorem EqTmIH.pair_fst_snd {Γ A B p l l'} :
    I.WfTmIH Γ (max l l') (Expr.sigma l l' A B) p →
    I.EqTmIH Γ (max l l') (Expr.sigma l l' A B) p
      (Expr.pair l l' B (Expr.fst l l' A B p) (Expr.snd l l' A B p))
  | ⟨_, hΓ, _, _, hP, _, hp, ptp⟩ => by
    obtain ⟨_, _, hA, _, hB, eq⟩ := I.mem_ofType_sigma.1 hP; simp at eq; subst eq
    exact
      have h1 := I.mem_ofTerm_fst.2 ⟨by omega, _, hA, _, hB, _, hp, ptp, rfl⟩
      have h2 := I.mem_ofTerm_snd.2 ⟨by omega, _, hA, _, hB, _, hp, ptp, rfl⟩
      have pr := I.mem_ofTerm_pair.2 ⟨rfl, _, h1, _, mkFst_tp .., _, hB, _, h2, mkSnd_tp .., by simp⟩
      ⟨_, hΓ, _, _, hP, _, hp, pr, ptp⟩

theorem EqTmIH.code_el {Γ a l} :
    I.WfTmIH Γ (l + 1) (Expr.univ l) a → I.EqTmIH Γ (l + 1) (Expr.univ l) a a.el.code
  | ⟨_, hΓ, _, _, hA, _, ha, atp⟩ => by
    obtain ⟨_, eq⟩ := I.mem_ofType_univ.1 hA; simp at eq; subst eq
    exact
      have h1 := I.mem_ofType_el.2 ⟨_, _, ha, atp, rfl⟩
      ⟨_, hΓ, by omega, _, hA, _, ha, I.mem_ofTerm_code.2 ⟨_, rfl, _, h1, by simp⟩, atp⟩

theorem EqTmIH.conv {Γ A A' t t' l} : I.EqTmIH Γ l A t t' → I.EqTpIH Γ l A A' → I.EqTmIH Γ l A' t t'
  | ⟨_, hΓ, _, _, hA, ht⟩, ⟨_, hΓ₁, _, _, hA₁, hA'⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    exact ⟨_, hΓ, _, _, hA', ht⟩

theorem EqTmIH.trans {Γ A t t' t'' l} :
    I.EqTmIH Γ l A t t' → I.EqTmIH Γ l A t' t'' → I.EqTmIH Γ l A t t''
  | ⟨_, hΓ, hl, _, hA, _, ht, ht', ttp⟩, ⟨_, hΓ₁, _, _, _, _, ht'₁, ht'', _⟩ => by
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique ht' ht'₁
    exact ⟨_, hΓ, hl, _, hA, _, ht, ht'', ttp⟩

/-- `I` is a well-formed interpretation of the axiom environment `E`. -/
structure Wf (I : Interpretation χ s) (E : Axioms χ) : Prop where
  ax {c Al} (Ec : E c = some Al) :
    ∃ sc, I.ax c Al.1.2 = some sc ∧
    ∃ sA : y(𝟙_ 𝒞) ⟶ s[Al.1.2].Ty,
      sA ∈ I.ofType s.nilCObj Al.1.2 Al.1.1 ∧
      sc ≫ s[Al.1.2].tp = sA

variable {E : Axioms χ} {slen} [Iwf : Fact (I.Wf slen E)]
include Iwf

theorem WfTmIH.ax {Γ c Al} (Ec : E c = some Al) :
    I.WfCtxIH Γ → I.WfTmIH Γ Al.val.2 Al.val.1 (Expr.ax c Al.val.1)
  | ⟨Γ, hΓ⟩ => by
    have ⟨_, eq, _, sA, sA_tp⟩ := Iwf.out.ax Ec
    have := I.mem_ofType_of_isClosed Al.2.1 Γ (by omega) sA
    refine ⟨_, hΓ, by omega, _, this, ?_⟩
    simp [ofTerm, eq, sA_tp]

theorem ofType_ofTerm_sound :
    (∀ {Γ}, WfCtx E Γ → I.WfCtxIH Γ) ∧
    (∀ {Γ l A}, (Awf : E ∣ Γ ⊢[l] A) → I.WfTpIH Γ l A) ∧
    (∀ {Γ l A B}, (Aeq : E ∣ Γ ⊢[l] A ≡ B) → I.EqTpIH Γ l A B) ∧
    (∀ {Γ l A t}, (twf : E ∣ Γ ⊢[l] t : A) → I.WfTmIH Γ l A t) ∧
    (∀ {Γ l A t u}, (teq : E ∣ Γ ⊢[l] t ≡ u : A) → I.EqTmIH Γ l A t u) := by
  mutual_induction WfCtx

  case nil => exact .nil
  case snoc => exact fun _ _ _ => .snoc

  case pi' => exact fun _ _ h1 h2 => (h1.refl.pi h2.refl).left
  case sigma' => exact fun _ _ h1 h2 => (h1.refl.sigma h2.refl).left
  case Id' => exact fun _ _ _ h1 h2 h3 => (h1.refl.Id h2.refl h3.refl).left
  case univ => exact fun _ => .univ slen
  case el => exact fun _ h1 => (EqTpIH.el h1.refl).left

  case cong_pi' => exact fun _ _ _ _ _ _ => .pi
  case cong_sigma' => exact fun _ _ _ _ _ _ => .sigma
  case cong_Id => exact fun _ _ _ => .Id
  case cong_el => exact fun _ => .el
  case el_code => exact fun h _ => .el_code slen h
  case refl_tp => exact fun _ h => h.refl
  case symm_tp => exact fun _ => .symm
  case trans_tp => exact fun _ _ => .trans

  case ax => exact fun _ Ec _ h _ => .ax Ec h
  case bvar => exact fun _ => .bvar
  case lam' => exact fun _ _ h1 h2 => (h2.refl.lam h1.refl).left
  case app' => exact fun _ _ _ _ _ h1 h2 h3 => (h2.refl.app h1.refl h3.refl).left
  case pair' => exact fun _ _ _ _ _ h1 h2 h3 => (h2.refl.pair h1.refl h3.refl).left
  case fst' => exact fun _ _ _ h1 h2 h3 => (h3.refl.fst_snd h1.refl h2.refl).1.left
  case snd' => exact fun _ _ _ h1 h2 h3 => (h3.refl.fst_snd h1.refl h2.refl).2.left
  case refl' => exact fun _ _ _ h1 => h1.refl.refl_tm.left
  case idRec' => exact fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    (h1.refl.idRec h2.refl h3.refl h4.refl h5.refl).left
  case code => exact fun h _ h1 => (EqTmIH.code slen h h1.refl).left
  case conv => exact fun _ _ h1 h2 => (h1.refl.conv h2).left

  case cong_lam' => exact fun _ _ _ _ _ _ => .lam
  case cong_app' => exact fun _ _ _ _ _ => .app
  case cong_pair' => exact fun _ _ _ _ _ => .pair
  case cong_fst' => exact fun _ _ _ _ _ h1 h2 h3 => (h3.fst_snd h1 h2).1
  case cong_snd' => exact fun _ _ _ _ _ h1 h2 h3 => (h3.fst_snd h1 h2).2
  case cong_refl' => exact fun _ _ _ => .refl_tm
  case cong_idRec' => exact fun _ _ _ _ _ _ _ _ _ => .idRec
  case cong_code => exact fun h _ => .code slen h
  case app_lam' => exact fun _ _ _ _ _ _ => .app_lam
  case fst_pair' => exact fun _ _ _ _ _ h1 h2 h3 => (EqTmIH.fst_snd_pair h1 h2 h3).1
  case snd_pair' => exact fun _ _ _ _ _ h1 h2 h3 => (EqTmIH.fst_snd_pair h1 h2 h3).2
  case idRec_refl' => exact fun _ _ _ _ _ => .idRec_refl
  case lam_app' => exact fun _ _ _ _ _ => .lam_app
  case pair_fst_snd' => exact fun _ _ _ _ _ => .pair_fst_snd
  case code_el => exact fun _ => .code_el
  case conv_eq => exact fun _ _ => .conv
  case refl_tm => exact fun _ h => h.refl
  case symm_tm' => exact fun _ _ _ => .symm
  case trans_tm' => exact fun _ _ _ _ => .trans

/-! ## Interpretation API -/

variable {Γ : Ctx χ} {A B t u : Expr χ} {l : Nat}

/-- Given `Γ` s.t. `WfCtx Γ`, return `⟦Γ⟧`. -/
def interpCtx (H : WfCtx E Γ) : s.CObj :=
  (I.ofCtx Γ).get <| Part.dom_iff_mem.mpr (I.ofType_ofTerm_sound.1 H)

@[simp] theorem interpCtx_mem (H : WfCtx E Γ) : I.interpCtx H ∈ I.ofCtx Γ :=
  Part.get_mem ..

/-- Given `Γ, l, A` s.t. `Γ ⊢[l] A`, return `⟦A⟧_⟦Γ⟧`. -/
def interpTy (H : E ∣ Γ ⊢[l] A) : y(I.interpCtx H.wf_ctx |>.1) ⟶ (s[l]'(H.lt_slen slen)).Ty :=
  (I.ofType _ l A (H.lt_slen slen)).get <| by
    have ⟨_, h1, _, h2⟩ := I.ofType_ofTerm_sound.2.1 H
    cases Part.mem_unique (I.interpCtx_mem H.wf_ctx) h1
    apply Part.dom_iff_mem.mpr h2

@[simp] theorem interpTy_mem (H : E ∣ Γ ⊢[l] A) : I.interpTy H ∈ I.ofType _ l A :=
  Part.get_mem ..

theorem interpTy_eq (H : E ∣ Γ ⊢[l] A ≡ B) :
    I.interpTy H.wf_left = I.interpTy H.wf_right := by
  have ⟨_, h1, _, _, ⟨_, eq⟩, _, rfl⟩ := I.ofType_ofTerm_sound.2.2.1 H
  unfold interpTy
  cases Part.mem_unique (I.interpCtx_mem H.wf_ctx) h1
  exact eq

/-- Given `Γ, l, t, A` s.t. `Γ ⊢[l] t : A`, return `⟦t⟧_⟦Γ⟧`. -/
def interpTm (H : E ∣ Γ ⊢[l] t : A) :
    y(I.interpCtx H.wf_ctx |>.1) ⟶ (s[l]'(H.lt_slen slen)).Tm :=
  (I.ofTerm _ l t (H.lt_slen slen)).get <| by
    have ⟨_, h1, _, _, _, _, ⟨h2, rfl⟩, _⟩ := I.ofType_ofTerm_sound.2.2.2.1 H
    cases Part.mem_unique (I.interpCtx_mem H.wf_ctx) h1
    exact h2

@[simp] theorem interpTm_mem (H : E ∣ Γ ⊢[l] t : A) : I.interpTm H ∈ I.ofTerm _ l t :=
  Part.get_mem ..

@[simp] theorem interpTm_tp (H : E ∣ Γ ⊢[l] t : A) :
    I.interpTm H ≫ (s[l]'(H.lt_slen slen)).tp = I.interpTy H.wf_tp := by
  have ⟨_, h1, _, _, ⟨_, rfl⟩, _, ⟨_, rfl⟩, h2⟩ := I.ofType_ofTerm_sound.2.2.2.1 H
  cases Part.mem_unique (I.interpCtx_mem H.wf_ctx) h1
  exact h2

theorem interpTm_eq (H : E ∣ Γ ⊢[l] t ≡ u : A) :
    I.interpTm H.wf_left = I.interpTm H.wf_right := by
  have ⟨_, h1, _, _, _, _, ⟨_, h2⟩, ⟨_, rfl⟩, _⟩ := I.ofType_ofTerm_sound.2.2.2.2 H
  cases Part.mem_unique (I.interpCtx_mem H.wf_ctx) h1
  exact h2

def empty (χ : Type*) (s : UHomSeq 𝒞) : Interpretation χ s where
  ax _ _ _ := none

def snoc [DecidableEq χ] (I : Interpretation χ s) (c : χ) (l : Nat) (l_lt : l < s.length)
    (sc : y(𝟙_ 𝒞) ⟶ s[l].Tm) :
    Interpretation χ s where
  ax d k _ := if h : c = d ∧ k = l then some (h.2 ▸ sc) else I.ax d k

end Interpretation
end NaturalModel
