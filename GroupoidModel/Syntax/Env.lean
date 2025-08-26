import GroupoidModel.Syntax.Synth
import GroupoidModel.Syntax.Typechecker.Value

variable {χ : Type*} {E : Env χ}

theorem isClosed_all :
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A → A.isClosed Γ.length) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → t.isClosed Γ.length) := by
  mutual_induction WfTp
  all_goals try exact True.intro
  case bvar =>
    intros; rename_i lk _
    simp [Expr.isClosed, lk.lt_length]
  all_goals grind [Expr.isClosed]

theorem WfTp.isClosed {l A} : E ∣ [] ⊢[l] A → A.isClosed := isClosed_all.1
theorem WfTm.isClosed {l A t} : E ∣ [] ⊢[l] t : A → t.isClosed := isClosed_all.2

/-! ## Constant environments -/

namespace Env

def empty (χ) : Env χ := fun _ => none

theorem Wf.empty (χ) : (empty χ).Wf := nofun

open Classical

instance : LE (Env χ) where
  le E E' := ∀ ⦃c p⦄, (E c) = some p → (E' c) = some p

noncomputable def snoc (E : Env χ)
    (l : Nat) (c : χ) (A : Expr χ)
    (l_le : l ≤ univMax) (A_cl : A.isClosed) : Env χ :=
  fun d => if d = c then some ⟨(A, l), ⟨A_cl, l_le⟩⟩ else E d

@[simp]
theorem snoc_get (E : Env χ)
    (l : Nat) (c : χ) (A : Expr χ)
    (l_le : l ≤ univMax) (A_cl : A.isClosed) :
    E.snoc l c A l_le A_cl c = some ⟨(A, l), ⟨A_cl, l_le⟩⟩ := by
  simp [snoc]

theorem le_snoc (E : Env χ)
    (l : Nat) (c : χ) (A : Expr χ)
    (l_le : l ≤ univMax) (A_cl : A.isClosed)
    (Ec : E c = none) :
    E ≤ E.snoc l c A l_le A_cl := by
  intro d Al Ed
  have : d ≠ c := by grind
  simp only [snoc, this, ↓reduceIte, Ed]

theorem _root_.of_env_le_all {E E' : Env χ} (le : E ≤ E') :
    (∀ {Γ}, WfCtx E Γ → WfCtx E' Γ) ∧
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A → E' ∣ Γ ⊢[l] A) ∧
    (∀ {Γ l A B}, E ∣ Γ ⊢[l] A ≡ B → E' ∣ Γ ⊢[l] A ≡ B) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → E' ∣ Γ ⊢[l] t : A) ∧
    (∀ {Γ l A t u}, E ∣ Γ ⊢[l] t ≡ u : A → E' ∣ Γ ⊢[l] t ≡ u : A) := by
  mutual_induction WfCtx
  case const =>
    intros; rename_i Ec Γ
    apply WfTm.const Γ (le Ec)
  grind_cases

theorem Wf.snoc {E : Env χ} {A l}
    (Ewf : E.Wf) (c : χ) (Awf : E ∣ [] ⊢[l] A) (Ec : E c = none) :
    (E.snoc l c A Awf.le_univMax Awf.isClosed).Wf := by
  intro d Al Ed
  simp only [Env.snoc] at Ed
  have le := E.le_snoc l c A Awf.le_univMax Awf.isClosed Ec
  by_cases eq : d = c <;> simp only [eq, ↓reduceIte] at Ed
  . cases Ed
    exact of_env_le_all le |>.2.1 Awf
  . exact of_env_le_all le |>.2.1 <| Ewf Ed

end Env

/-- An axiom checked with respect to the axioms in `E`. -/
structure CheckedAx (E : Env χ) where
  name : χ
  get_name : E name = none
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp E [] l nfTp tp

namespace CheckedAx
variable [Ewf : Fact E.Wf]

theorem wf_tp (a : CheckedAx E) : E ∣ [] ⊢[a.l] a.tp :=
  a.wf_nfTp.wf_tp

/-- The set of axioms extended by this one. -/
noncomputable def snocEnv (a : CheckedAx E) : Env χ :=
  E.snoc a.l a.name a.tp a.wf_tp.le_univMax a.wf_tp.isClosed

theorem wf_snocEnv (a : CheckedAx E) : a.snocEnv.Wf :=
  Ewf.out.snoc a.name a.wf_tp a.get_name

/-- The axiom as an expression. -/
def val (a : CheckedAx E) : Expr χ :=
  .const a.name

theorem wf_val (a : CheckedAx E) : a.snocEnv ∣ [] ⊢[a.l] a.val : a.tp := by
  unfold val
  have := E.snoc_get a.l a.name a.tp a.wf_tp.le_univMax a.wf_tp.isClosed
  apply WfTm.const .nil this

end CheckedAx

/-- A definition checked with respect to the axioms in `E`. -/
structure CheckedDef (E : Env χ) where
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp E [] l nfTp tp
  val : Expr χ
  -- nfVal?
  wf_val : E ∣ [] ⊢[l] val : tp

namespace CheckedDef
variable [Fact E.Wf]

theorem wf_tp (d : CheckedDef E) : E ∣ [] ⊢[d.l] d.tp :=
  d.wf_val.wf_tp

end CheckedDef
