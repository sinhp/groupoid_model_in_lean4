import HoTTLean.Syntax.Synth

namespace SynthLean

variable {χ : Type*}

/-! ## Axiom environments -/

namespace Axioms

def empty (χ) : Axioms χ := fun _ => none

theorem empty_wf (χ) : (empty χ).Wf := nofun

section
variable [DecidableEq χ]

/- Remark: we require `E c = none` because it is convenient to have around later.
We do not require `E ∣ [] ⊢[l] A` so that `@[reflect]` doesn't have to prove it. -/
def snoc (E : Axioms χ)
    (l : Nat) (c : χ) (A : Expr χ)
    (l_le : l ≤ univMax) (_Ec : E c = none) (A_cl : A.isClosed) : Axioms χ :=
  fun d => if d = c then some ⟨(A, l), ⟨A_cl, l_le⟩⟩ else E d

@[simp]
theorem snoc_get (E : Axioms χ) (l c A l_le Ec A_cl) :
    E.snoc l c A l_le Ec A_cl c = some ⟨(A, l), ⟨A_cl, l_le⟩⟩ := by
  simp [snoc]

end

/-! ## Theory inclusions -/

instance : LE (Axioms χ) where
  le E E' := ∀ ⦃c p⦄, (E c) = some p → (E' c) = some p

instance : @Std.Refl (Axioms χ) (· ≤ ·) where
  refl _ _ _ := id

instance : IsTrans (Axioms χ) (· ≤ ·) where
  trans _ _ _ h h' _ _ Ec := h' (h Ec)

theorem empty_le (E : Axioms χ) : empty χ ≤ E := nofun

theorem eq_none_of_le {E E' : Axioms χ} (le : E ≤ E') {c} (E'c : E' c = none) : E c = none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro _ h
  simp [le h] at E'c

section
variable [DecidableEq χ] {𝕋 𝕋' : Axioms χ} (le : 𝕋 ≤ 𝕋')

include le in
theorem le_snoc (l c A l_le 𝕋'c A_cl) : 𝕋 ≤ 𝕋'.snoc l c A l_le 𝕋'c A_cl := by
  intro d Al 𝕋d
  have : d ≠ c := fun h => nomatch (h ▸ le 𝕋d) ▸ 𝕋'c
  simpa [snoc, this, ↓reduceIte] using le 𝕋d

include le in
theorem snoc_le (l c A l_le 𝕋c A_cl) (𝕋'c : 𝕋' c = some ⟨(A, l), ⟨A_cl, l_le⟩⟩) :
    𝕋.snoc l c A l_le 𝕋c A_cl ≤ 𝕋' := by
  intro d Al 𝕋d
  by_cases eq : d = c
  . cases eq; convert 𝕋'c using 2; simpa [snoc] using 𝕋d.symm
  . simp only [snoc, eq, ↓reduceIte] at 𝕋d; exact le 𝕋d

theorem le_snoc_self (𝕋 : Axioms χ) (l c A l_le 𝕋c A_cl) :
    𝕋 ≤ 𝕋.snoc l c A l_le 𝕋c A_cl :=
  le_snoc (refl _) l c A l_le 𝕋c A_cl

include le in
theorem snoc_le_snoc (l c A l_le 𝕋'c A_cl) :
    𝕋.snoc l c A l_le (eq_none_of_le le 𝕋'c) A_cl ≤ 𝕋'.snoc l c A l_le 𝕋'c A_cl := by
  simp [snoc_le (le_snoc le ..)]

end
end Axioms

/-! ## Theory maps (translations) -/

variable {χ χ' : Type*} {𝕋 : Axioms χ} {f : χ → χ'} {𝕋' : Axioms χ'}

/-- A map `f` of signatures is well-formed as a map of theories
when it preserves the types of those base constants
that are present in the domain. -/
structure WfTheoryMap (𝕋 : Axioms χ) (f : χ → χ') (𝕋' : Axioms χ') : Prop where
  get_eq (c : χ) (h : (𝕋 c).isSome) :
    𝕋' (f c) = (𝕋 c).map fun ⟨(A, l), h⟩ => ⟨(A.map f, l), by simp [h]⟩

theorem WfTheoryMap.of_le {𝕋 𝕋' : Axioms χ} (le : 𝕋 ≤ 𝕋') : WfTheoryMap 𝕋 id 𝕋' :=
  ⟨by
    intro _ 𝕋c
    simp [le <| Option.eq_some_of_isSome 𝕋c]⟩

section
variable (H : WfTheoryMap 𝕋 f 𝕋') {Γ l A B t u}
include H

private theorem map_all :
    (∀ {Γ}, WfCtx 𝕋 Γ → WfCtx 𝕋' (Γ.map f)) ∧
    (∀ {Γ l A}, 𝕋 ∣ Γ ⊢[l] A → 𝕋' ∣ Γ.map f ⊢[l] A.map f) ∧
    (∀ {Γ l A B}, 𝕋 ∣ Γ ⊢[l] A ≡ B → 𝕋' ∣ Γ.map f ⊢[l] A.map f ≡ B.map f) ∧
    (∀ {Γ l A t}, 𝕋 ∣ Γ ⊢[l] t : A → 𝕋' ∣ Γ.map f ⊢[l] t.map f : A.map f) ∧
    (∀ {Γ l A t u}, 𝕋 ∣ Γ ⊢[l] t ≡ u : A → 𝕋' ∣ Γ.map f ⊢[l] t.map f ≡ u.map f : A.map f) := by
  mutual_induction WfCtx
  case ax =>
    intro _ _ Al _ 𝕋c _ _
    apply WfTm.ax (Al := ⟨(Al.1.1.map f, Al.1.2), by simp [Al.2]⟩)
    . assumption
    . apply 𝕋c ▸ H.get_eq _ (Option.isSome_iff_exists.mpr ⟨_, 𝕋c⟩)
  case bvar =>
    introv _ lk _
    apply WfTm.bvar ‹_› (lk.map f)

  all_goals (
    dsimp [Expr.map]; intros
    try simp only [Expr.subst_map, ← Expr.up_map_comp, ← Expr.snoc_map_comp, ← Expr.map_toSb] at *)
  case lam_app' => apply EqTm.lam_app; assumption
  case idRec_refl' => apply EqTm.idRec_refl <;> assumption
  case cong_idRec' => apply EqTm.cong_idRec <;> assumption
  case cong_snd' => apply EqTm.cong_snd <;> assumption
  case idRec' => apply WfTm.idRec <;> assumption
  case snd' => apply WfTm.snd; assumption
  grind_cases

theorem WfCtx.map (W : WfCtx 𝕋 Γ) : WfCtx 𝕋' (Γ.map f) := (map_all H).1 W
theorem WfTp.map (W : 𝕋 ∣ Γ ⊢[l] A) : 𝕋' ∣ Γ.map f ⊢[l] A.map f := (map_all H).2.1 W
theorem EqTp.map (W : 𝕋 ∣ Γ ⊢[l] A ≡ B) : 𝕋' ∣ Γ.map f ⊢[l] A.map f ≡ B.map f :=
  (map_all H).2.2.1 W
theorem WfTm.map (W : 𝕋 ∣ Γ ⊢[l] t : A) : 𝕋' ∣ Γ.map f ⊢[l] t.map f : A.map f :=
  (map_all H).2.2.2.1 W
theorem EqTm.map (W : 𝕋 ∣ Γ ⊢[l] t ≡ u : A) : 𝕋' ∣ Γ.map f ⊢[l] t.map f ≡ u.map f : A.map f :=
  (map_all H).2.2.2.2 W

end

section
variable {𝕋 𝕋' : Axioms χ} (le : 𝕋 ≤ 𝕋') {Γ l A B t u}
include le

theorem WfCtx.of_axioms_le (Γwf : WfCtx 𝕋 Γ) : WfCtx 𝕋' Γ := by
  simpa using Γwf.map (WfTheoryMap.of_le le)
theorem WfTp.of_axioms_le (ΓA : 𝕋 ∣ Γ ⊢[l] A) : 𝕋' ∣ Γ ⊢[l] A := by
  simpa using ΓA.map (WfTheoryMap.of_le le)
theorem EqTp.of_axioms_le (ΓAB : 𝕋 ∣ Γ ⊢[l] A ≡ B) : 𝕋' ∣ Γ ⊢[l] A ≡ B := by
  simpa using ΓAB.map (WfTheoryMap.of_le le)
theorem WfTm.of_axioms_le (Γt : 𝕋 ∣ Γ ⊢[l] t : A) : 𝕋' ∣ Γ ⊢[l] t : A := by
  simpa using Γt.map (WfTheoryMap.of_le le)
theorem EqTm.of_axioms_le (Γtu : 𝕋 ∣ Γ ⊢[l] t ≡ u : A) : 𝕋' ∣ Γ ⊢[l] t ≡ u : A := by
  simpa using Γtu.map (WfTheoryMap.of_le le)

end

theorem Axioms.Wf.snoc [DecidableEq χ] {𝕋 : Axioms χ} {A l}
    (𝕋wf : 𝕋.Wf) (c : χ) (Awf : 𝕋 ∣ [] ⊢[l] A) (𝕋c : 𝕋 c = none) :
    (𝕋.snoc l c A Awf.le_univMax 𝕋c Awf.isClosed).Wf := by
  intro d Al 𝕋d
  simp only [Axioms.snoc] at 𝕋d
  have le := 𝕋.le_snoc_self l c A Awf.le_univMax 𝕋c Awf.isClosed
  by_cases eq : d = c <;> simp only [eq, ↓reduceIte] at 𝕋d
  . cases 𝕋d
    exact Awf.of_axioms_le le
  . exact (𝕋wf 𝕋d).of_axioms_le le

end SynthLean
