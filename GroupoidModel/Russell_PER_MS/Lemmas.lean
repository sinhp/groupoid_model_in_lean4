import GroupoidModel.Russell_PER_MS.Typing

/-! Basic syntactic metatheory. -/

/-! ## Inversion -/

theorem EqTp.le_univMax {Γ A B l} : Γ ⊢[l] A ≡ B → l ≤ univMax := by
  apply @EqTp.rec (fun _ l _ _ _ => l ≤ univMax) (fun _ l _ _ _ _ => l ≤ univMax)
  all_goals intros; first| trivial | omega

theorem EqTm.le_univMax {Γ A t u l} : Γ ⊢[l] t ≡ u : A → l ≤ univMax := by
  apply @EqTm.rec (fun _ l _ _ _ => l ≤ univMax) (fun _ l _ _ _ _ => l ≤ univMax)
  all_goals intros; first| trivial | omega

theorem EqTp.wf_left {Γ A B l} : Γ ⊢[l] A ≡ B → Γ ⊢[l] A :=
  fun h => .trans h (.symm h)

theorem EqTp.wf_right {Γ A B l} : Γ ⊢[l] A ≡ B → Γ ⊢[l] B :=
  fun h => .trans (.symm h) h

theorem EqTm.wf_left {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] t : A :=
  fun h => .trans h (.symm h)

theorem EqTm.wf_right {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] u : A :=
  fun h => .trans (.symm h) h

theorem EqTm.wf_tp {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] A := by
  apply @EqTm.rec
    (fun _ _ _ _ _ => True)
    (fun Γ l _ _ A _ => Γ ⊢[l] A)
  all_goals intros; try trivial
  case cong_lam A_eq _ _ B_wf =>
    exact .cong_pi A_eq.wf_left B_wf
  case cong_app B_eq _ a_eq _ _ _ =>
    exact (EqTp.inst_tp B_eq a_eq).wf_left
  case cong_code =>
    apply EqTp.cong_univ; assumption
  case inst_tm a_eq B_wf _ =>
    exact (EqTp.inst_tp B_wf a_eq).wf_left
  case app_lam u_wf B_wf _ =>
    exact EqTp.inst_tp B_wf u_wf
  case conv A_eq _ _ _ =>
    exact A_eq.wf_right

-- Oh no, this is a conjecture in L4L. Maybe need a logrel
theorem EqTp.pi_inv {Γ A A' B B' l} : Γ ⊢[l] A.pi B ≡ A'.pi B' →
    ∃ l₁ l₂, l = max l₁ l₂ ∧ (Γ ⊢[l₁] A ≡ A') ∧ (A :: Γ ⊢[l₂] B ≡ B') := by
  sorry

-- This seems to need difficult inversion lemmas
theorem EqTp.eq_lvl {Γ A A' l} : Γ ⊢[l] A ≡ A' → ∀ l', Γ ⊢[l'] A ≡ A' → l = l' := by
  apply @EqTp.rec
    (fun Γ l A A' _ => ∀ l', Γ ⊢[l'] A ≡ A' → l = l')
    (fun Γ l t u A _ => ∀ l', Γ ⊢[l'] t ≡ u : A → l = l')
  all_goals try intros
  case cong_pi l' l'' _ _ ihA ihB _ ABeq =>
    have ⟨l₁, l₂, leq, Aeq, Beq⟩ := pi_inv ABeq
    have := ihA _ Aeq
    have := ihB _ Beq
    omega
  all_goals sorry

/-! ## Attempt at stability under equality of contexts -/

/-- The two contexts are definitionally equal,
and in particular they are well-formed.
This is a derived judgment (not one of the mutually inductive judgments defining HoTT₀). -/
inductive EqCtx : List Expr → List Expr → Prop
  | nil : EqCtx [] []
  | cons {Γ Γ' A A' l} : EqCtx Γ Γ' → Γ ⊢[l] A ≡ A' → EqCtx (A :: Γ) (A' :: Γ')

theorem Lookup.cong_eqCtx {Γ Γ' A i} : Lookup Γ i A → EqCtx Γ Γ' →
    ∃ A' l, (Γ' ⊢[l] A' ≡ A) ∧ Lookup Γ' i A' :=
  sorry

-- TODO: annoying to copy the same proof; define a better recursion principle
-- which gives both conclusions at once.
open EqTm in
theorem EqTp.cong_eqCtx {Γ B B' l} : Γ ⊢[l] B ≡ B' → ∀ Γ', EqCtx Γ Γ' → Γ' ⊢[l] B ≡ B' := by
  apply @EqTp.rec
    (fun Γ l B B' _ => ∀ Γ', EqCtx Γ Γ' → Γ' ⊢[l] B ≡ B')
    (fun Γ l t u A _ => ∀ Γ', EqCtx Γ Γ' → Γ' ⊢[l] t ≡ u : A)
  all_goals intros
  case cong_pi Aeq Beq ihA ihB _ Γeq =>
    exact cong_pi (ihA _ Γeq) (ihB _ <| Γeq.cons Aeq.wf_left)
  case cong_univ =>
    constructor; assumption
  case cong_el ih _ Γeq =>
    exact cong_el (ih _ Γeq)
  case inst_tp teq ihB iht _ Γeq =>
    exact inst_tp (ihB _ <| Γeq.cons teq.wf_tp) (iht _ Γeq)
  case symm ih _ Γeq =>
    exact symm (ih _ Γeq)
  case trans ih ih' _ Γeq =>
    exact trans (ih _ Γeq) (ih' _ Γeq)
  case cong_bvar Aeq lk ih _ Γeq =>
    have ⟨A', l', A'eq, lk'⟩ := lk.cong_eqCtx Γeq
    have := A'eq.wf_right.eq_lvl _ (ih _ Γeq)
    exact .conv (this ▸ A'eq) (cong_bvar (this ▸ A'eq.wf_left) lk')
  all_goals sorry

/-! ## Level inference -/

theorem EqTp.inferLvl_inst {Γ A B B' t u l l'} : A :: Γ ⊢[l] B ≡ B' → Γ ⊢[l'] t ≡ u : A →
    B.inferLvl (A :: Γ) = (B.inst t).inferLvl Γ :=
  sorry

theorem EqTp.cong_inferLvl {Γ A B l} : Γ ⊢[l] A ≡ B → A.inferLvl Γ = B.inferLvl Γ :=
  sorry

theorem EqTp.eq_inferLvl {Γ A B l} : Γ ⊢[l] A ≡ B → A.inferLvl Γ = l ∧ B.inferLvl Γ = l := by
  apply @EqTp.rec
    (fun Γ l A B _ => A.inferLvl Γ = l ∧ B.inferLvl Γ = l)
    (fun Γ l t u A _ => t.inferLvl Γ = l ∧ u.inferLvl Γ = l) -- ∧ A.inferLvl Γ = l ?
  all_goals try simp +contextual [Expr.inferLvl]; try omega
  case inst_tp => sorry -- closure of inferLvl under well-typed substitution
  case inst_tm => sorry -- same
  case cong_pi =>
    intros
    rename_i h
    sorry
  all_goals sorry
