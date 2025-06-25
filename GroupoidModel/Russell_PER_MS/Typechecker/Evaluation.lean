import Qq

import GroupoidModel.Russell_PER_MS.GCongr
import GroupoidModel.Russell_PER_MS.Injectivity
import GroupoidModel.Russell_PER_MS.Typechecker.Value

-- This instance breaks `grind`.
attribute [-instance] Nat.instMax_mathlib

/-- Shorthand for `List.length` which is used a lot in this file. -/
local notation "‖" l "‖" => List.length l

open Qq

/-! ## Evaluation -/

private lemma extracted_1 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (k k' : ℕ) (C b : Expr) (Γt : Γ ⊢[l] .lam k k' C b : A)
    (vC : Val) (vCwf : WfValTp Δ k vC) (vCeq : Δ ⊢[k] vC.toExpr ‖Δ‖ ≡ C.subst (sbOfEnv ‖Δ‖ env))
    (m m' : ℕ) (vA : Val) (vB : Clos) (vPwf : WfValTp Γ l (.pi m m' vA vB))
    (vAvBA : Γ ⊢[l] (Val.pi m m' vA vB).toExpr ‖Γ‖ ≡ A.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖))) :
    WfValTm Δ l
      (.lam k k' vC (.mk_tm Γ k k' (vA.toExpr ‖Γ‖) (vB.toExpr ‖Γ‖) env b))
      (A.subst (sbOfEnv ‖Δ‖ env)) := by
  obtain ⟨rfl, D, b, ACD⟩ := Γt.inv_lam
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vAvBA
  obtain ⟨_, rfl, rfl, vAC, vBD⟩ := vAvBA.trans_tp ACD |>.inv_pi
  have ΔvAvC := vAC.subst Δenv.wf_sbOfEnv |>.trans_tp vCeq.symm_tp
  have vCΔvB := vBD.wf_left.subst (Δenv.wf_sbOfEnv.up vAC.wf_left) |>.conv_binder ΔvAvC
  have := WfClosTm.clos_tm
    ΔvAvC
    (EqTp.refl_tp vCΔvB)
    Δenv
    (b.conv_binder vAC.symm_tp |>.conv vBD.symm_tp)
  apply WfValTm.conv_nf (WfValTm.lam vCwf this)
  apply EqTp.trans_tp _ (vAvBA.subst Δenv.wf_sbOfEnv)
  rw [Expr.subst]
  gcongr
  assumption

private lemma extracted_2 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (k k' : ℕ) (C b : Expr) (Γt : Γ ⊢[l] Expr.lam k k' C b : A)
    (vC : Val) (vCwf : WfValTp Δ k vC) (vCeq : Δ ⊢[k] vC.toExpr ‖Δ‖ ≡ C.subst (sbOfEnv ‖Δ‖ env))
    (m m' : ℕ) (vA : Val) (vB : Clos) (vPwf : WfValTp Γ l (Val.pi m m' vA vB))
    (vAvBA : Γ ⊢[l] (Val.pi m m' vA vB).toExpr ‖Γ‖ ≡ A.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖))) :
    Δ ⊢[l] (Val.lam k k' vC (.mk_tm Γ k k' (vA.toExpr ‖Γ‖) (vB.toExpr ‖Γ‖) env b)).toExpr ‖Δ‖ ≡
      (Expr.lam k k' C b).subst (sbOfEnv ‖Δ‖ env) :
      A.subst (sbOfEnv ‖Δ‖ env) := by
  obtain ⟨rfl, D, b, ACD⟩ := Γt.inv_lam
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vAvBA
  obtain ⟨_, rfl, rfl, vAC, vBD⟩ := vAvBA.trans_tp ACD |>.inv_pi
  rw [Val.toExpr, Expr.subst, Clos.toExpr]
  apply EqTm.symm_tm
  apply EqTm.conv_eq _ (ACD.symm_tp.subst Δenv.wf_sbOfEnv)
  rw [Expr.subst]
  gcongr
  . exact (b.subst <| Δenv.wf_sbOfEnv.up b.wf_ctx.inv_snoc)

private lemma extracted_5 {Δ : Ctx} {A : Expr} {B : Clos} {l l' m m' k k' : ℕ} {A' : Val}
    {Γ : Ctx} {C D : Expr} {env : List Val} {b : Expr}
    (Δf :
      WfValTm Δ (max l l') (Val.lam m m' A' (Clos.mk_tm Γ k k' C D env b))
        (Expr.pi l l' A (Clos.toExpr ‖Δ‖ B))) :
    (Δ ⊢[l] Expr.subst (sbOfEnv ‖Δ‖ env) C ≡ A) ∧
      ((A, l) :: Δ ⊢[l'] Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) D ≡ Clos.toExpr ‖Δ‖ B) ∧
        WfEnv Δ env Γ ∧ ((C, l) :: Γ ⊢[l'] b : D) := by
  have ⟨_, _, _, b, h⟩ := Δf.inv_lam
  obtain ⟨_, rfl, rfl, _, _⟩ := h.inv_pi
  cases b
  grind [EqTp.conv_binder, EqTp.symm_tp, EqTp.trans_tp]

private lemma extracted_3 {Δ : Ctx} {A : Expr} {B : Clos} {a : Val} {l l' m m' k k' : ℕ} {A' : Val}
    (Δa : WfValTm Δ l a A) (Γ : Ctx) (C D : Expr) (env : List Val) (b : Expr)
    (Δf :
      WfValTm Δ (max l l') (Val.lam m m' A' (Clos.mk_tm Γ k k' C D env b))
        (Expr.pi l l' A (Clos.toExpr ‖Δ‖ B)))
    (v : Val) (vwf : WfValTm Δ l' v (Expr.subst (sbOfEnv ‖Δ‖ (a :: env)) D)) :
    WfValTm Δ l' v (Expr.subst (Val.toExpr ‖Δ‖ a).toSb (Clos.toExpr ‖Δ‖ B)) := by
  apply vwf.conv_nf
  have ⟨_, Beq, env, b⟩ := extracted_5 Δf
  have := Δa.wf_toExpr
  convert
    Beq.subst (env.wf_sbOfEnv.wf_dom.sb_self.snoc this.wf_tp (by convert this; autosubst))
    using 1
  autosubst
  apply sb_irrel.1 b.wf_tp
  intro i lt
  cases i
  . simp
  . dsimp; apply sbOfEnv_get_eq; simpa [env.eq_length] using lt

private lemma extracted_9 {Δ : Ctx} {A : Val} {B : Clos} {a : Val} {l l' : ℕ}
    (Δa : WfValTm Δ l a (Val.toExpr ‖Δ‖ A)) (m m' : ℕ) (A' : Val) (Γ : Ctx) (k k' : ℕ)
    (C D : Expr) (env : List Val) (b : Expr)
    (Δf :
      WfValTm Δ (max l l') (Val.lam m m' A' (Clos.mk_tm Γ k k' C D env b))
        (Expr.pi l l' (Val.toExpr ‖Δ‖ A) (Clos.toExpr ‖Δ‖ B)))
    (v : Val)
    (veq :
      Δ ⊢[l']
        Val.toExpr ‖Δ‖ v ≡ Expr.subst (sbOfEnv ‖Δ‖ (a :: env)) b :
          Expr.subst (sbOfEnv ‖Δ‖ (a :: env)) D) :
    Δ ⊢[l']
      Val.toExpr ‖Δ‖ v ≡
        Expr.app l l' (Val.toExpr ‖Δ‖ A) (Clos.toExpr ‖Δ‖ B)
          (Val.toExpr ‖Δ‖ (Val.lam m m' A' (Clos.mk_tm Γ k k' C D env b)))
          (Val.toExpr ‖Δ‖ a) :
        Expr.subst (Val.toExpr ‖Δ‖ a).toSb (Clos.toExpr ‖Δ‖ B) := by
  obtain ⟨_, A', _, ⟨ΔCA', ΔDB', env, b⟩, eq⟩ := Δf.inv_lam
  obtain ⟨_, rfl, rfl, AA', BB'⟩ := eq.inv_pi
  clear eq
  rw [Val.toExpr, Clos.toExpr]
  replace ΔDB' := ΔDB'.conv_binder AA'.symm_tp |>.trans_tp BB'.symm_tp
  have Δb := b.subst (env.wf_sbOfEnv.up b.wf_ctx.inv_snoc) |>.conv_binder (ΔCA'.trans_tp AA'.symm_tp)
    |>.conv ΔDB'
  have := EqTm.app_lam Δb Δa.wf_toExpr
  apply EqTm.trans_tm _ (EqTm.trans_tm this.symm_tm _)
  . have := (WfSb.id env.wf_dom |>.snoc AA'.wf_left (by convert Δa.wf_toExpr; autosubst))
    convert EqTm.conv_eq _ (ΔDB'.subst this) using 1
    convert veq using 1
    . autosubst
      apply sb_irrel.1 b.wf_tp
      intro i lt
      cases i
      . simp
      . dsimp; symm; apply sbOfEnv_get_eq; simpa [env.eq_length] using lt
    . autosubst
      apply sb_irrel.2 b
      intro i lt
      cases i
      . simp
      . dsimp; symm; apply sbOfEnv_get_eq; simpa [env.eq_length] using lt
  . apply EqTm.cong_app
      (EqTp.refl_tp AA'.wf_left)
      (EqTp.refl_tp BB'.wf_left)
      _
      (EqTm.refl_tm Δa.wf_toExpr)
    exact EqTm.cong_lam AA' (EqTm.refl_tm Δb)

private lemma extracted_6 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (i : ℕ) (Γt : Γ ⊢[l] Expr.bvar i : A) :
    let v : Val := env[i]?.getD default
    WfValTm Δ l v (Expr.subst (sbOfEnv ‖Δ‖ env) A) := by
  dsimp
  have ⟨_, lk, eq⟩ := Γt.inv_bvar
  have := Δenv.lookup_wf lk
  convert this.conv_nf (eq.symm_tp.subst Δenv.wf_sbOfEnv) using 1
  simp [List.getElem?_eq_some_iff.mpr ⟨Δenv.lookup_lt lk, rfl⟩]

private lemma extracted_7 {Δ : Ctx} {A : Expr} {B : Clos} {a : Val} {l l' : ℕ}
    (Δa : WfValTm Δ l a A) (m m' : ℕ) (A' : Val)
    (Γ : Ctx) (k k' : ℕ) (C D : Expr) (env : List Val) (b : Expr)
    (Δf :
      WfValTm Δ (max l l') (Val.lam m m' A' (Clos.mk_tm Γ k k' C D env b))
        (Expr.pi l l' A (Clos.toExpr ‖Δ‖ B))) :
    WfEnv Δ (a :: env) ((C, l) :: Γ) := by
  have ⟨Aeq, _, env, b⟩ := extracted_5 Δf
  apply env.snoc b.wf_ctx.inv_snoc
  exact Δa.conv_nf Aeq.symm_tp

private lemma extracted_8 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (i : ℕ) (Γt : Γ ⊢[l] Expr.bvar i : A) :
    let v : Val := env[i]?.getD default
    Δ ⊢[l] Val.toExpr ‖Δ‖ v ≡ Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.bvar i) :
      Expr.subst (sbOfEnv ‖Δ‖ env) A := by
  dsimp
  have ⟨_, lk, eq⟩ := Γt.inv_bvar
  have := EqTm.refl_tm <| (Δenv.lookup_wf lk).wf_toExpr
  rw [List.getElem?_eq_some_iff.mpr ⟨Δenv.lookup_lt lk, rfl⟩,
    Expr.subst, Δenv.sbOfEnv_app lk]
  exact this.conv_eq (eq.symm_tp.subst Δenv.wf_sbOfEnv)

private lemma extracted_11 {Γ : Ctx} {A : Expr} {l : ℕ}
    (k k' : ℕ) (B t u : Expr) (Γt : Γ ⊢[l] Expr.pair k k' B t u : A)
    (l_1 l' : ℕ) (vA : Val) (vB : Clos)
    (vSeq : Γ ⊢[l] Val.toExpr ‖Γ‖ (Val.sigma l_1 l' vA vB) ≡
      Expr.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖)) A) :
    Γ ⊢[k] t : Val.toExpr ‖Γ‖ vA := by
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vSeq
  have ⟨_, _, t, _, eq⟩ := Γt.conv vSeq.symm_tp |>.inv_pair
  obtain ⟨_, rfl, rfl, vAA, _⟩ := eq.inv_sigma
  exact t.conv vAA.symm_tp

private lemma extracted_4 {Γ : Ctx} {A : Expr} {l : ℕ}
    (k k' : ℕ) (B t u : Expr) (Γt : Γ ⊢[l] Expr.pair k k' B t u : A)
    (l_1 l' : ℕ) (vA : Val) (vB : Clos)
    (vSeq : Γ ⊢[l] Val.toExpr ‖Γ‖ (Val.sigma l_1 l' vA vB) ≡
      Expr.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖)) A) :
    Γ ⊢[k'] u : Expr.subst t.toSb B := by
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vSeq
  have ⟨_, _, _, u, _⟩ := Γt.conv vSeq.symm_tp |>.inv_pair
  exact u

private lemma extracted_10 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (k k' : ℕ) (B t u : Expr) (Γt : Γ ⊢[l] Expr.pair k k' B t u : A)
    (l_1 l' : ℕ) (vA : Val) (vB : Clos) (vSwf : WfValTp Γ l (Val.sigma l_1 l' vA vB))
    (vSeq :
      Γ ⊢[l]
        Val.toExpr ‖Γ‖ (Val.sigma l_1 l' vA vB) ≡ Expr.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖)) A)
    (vt : Val) (vtwf : WfValTm Δ k vt (Expr.subst (sbOfEnv ‖Δ‖ env) (Val.toExpr ‖Γ‖ vA)))
    (vteq :
      Δ ⊢[k]
        Val.toExpr ‖Δ‖ vt ≡ Expr.subst (sbOfEnv ‖Δ‖ env) t :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Val.toExpr ‖Γ‖ vA))
    (vu : Val) (vuwf : WfValTm Δ k' vu (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.subst t.toSb B)))
    (vueq :
      Δ ⊢[k']
        Val.toExpr ‖Δ‖ vu ≡ Expr.subst (sbOfEnv ‖Δ‖ env) u :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.subst t.toSb B)) :
    WfValTm Δ l (Val.pair k k' (Clos.mk_tp Γ (Val.toExpr ‖Γ‖ vA) env B) vt vu)
      (Expr.subst (sbOfEnv ‖Δ‖ env) A) := by
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vSeq
  obtain ⟨rfl, _, _, _, eq⟩ := Γt.conv vSeq.symm_tp |>.inv_pair
  obtain ⟨_, rfl, rfl, vAA, vBB⟩ := eq.inv_sigma
  have ΔvA := vtwf.wf_toExpr.wf_tp
  have ΔvSeq := EqTp.cong_sigma
      (EqTp.refl_tp ΔvA)
      (vBB.subst (Δenv.wf_sbOfEnv.up vAA.wf_left) |>.symm_tp)
      |>.trans_tp (vSeq.subst Δenv.wf_sbOfEnv)
  apply WfValTm.conv_nf _ ΔvSeq
  have := WfValTm.pair (WfClosTp.clos_tp (EqTp.refl_tp ΔvA) Δenv vBB.wf_right) vtwf (vuwf.conv_nf ?_)
  . rwa [Clos.toExpr] at this
  . rw [Clos.toExpr]; autosubst
    exact EqTp.refl_tp vBB.wf_right |>.subst_eq
      (EqSb.refl Δenv.wf_sbOfEnv |>.snoc vAA.wf_left vteq.symm_tm)

private lemma extracted_12 {Δ Γ : Ctx} {A : Expr} {env : List Val} {l : ℕ} (Δenv : WfEnv Δ env Γ)
    (k k' : ℕ) (B t u : Expr) (Γt : Γ ⊢[l] Expr.pair k k' B t u : A)
    (l_1 l' : ℕ) (vA : Val) (vB : Clos) (vSwf : WfValTp Γ l (Val.sigma l_1 l' vA vB))
    (vSeq :
      Γ ⊢[l]
        Val.toExpr ‖Γ‖ (Val.sigma l_1 l' vA vB) ≡ Expr.subst (sbOfEnv ‖Γ‖ (envOfLen ‖Γ‖)) A)
    (vt : Val) (vtwf : WfValTm Δ k vt (Expr.subst (sbOfEnv ‖Δ‖ env) (Val.toExpr ‖Γ‖ vA)))
    (vteq :
      Δ ⊢[k]
        Val.toExpr ‖Δ‖ vt ≡ Expr.subst (sbOfEnv ‖Δ‖ env) t :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Val.toExpr ‖Γ‖ vA))
    (vu : Val) (vuwf : WfValTm Δ k' vu (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.subst t.toSb B)))
    (vueq :
      Δ ⊢[k']
        Val.toExpr ‖Δ‖ vu ≡ Expr.subst (sbOfEnv ‖Δ‖ env) u :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.subst t.toSb B)) :
    Δ ⊢[l]
      Val.toExpr ‖Δ‖ (Val.pair k k' (Clos.mk_tp Γ (Val.toExpr ‖Γ‖ vA) env B) vt vu) ≡
        Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.pair k k' B t u) :
        Expr.subst (sbOfEnv ‖Δ‖ env) A := by
  rw [sbOfEnv_envOfLen, Expr.subst_bvar, id_eq, Val.toExpr] at vSeq
  obtain ⟨rfl, _, _, _, eq⟩ := Γt.conv vSeq.symm_tp |>.inv_pair
  obtain ⟨_, rfl, rfl, vAA, vBB⟩ := eq.inv_sigma
  have ΔvA := vtwf.wf_toExpr.wf_tp
  have ΔvSeq := EqTp.cong_sigma
    (EqTp.refl_tp ΔvA)
    (vBB.subst (Δenv.wf_sbOfEnv.up vAA.wf_left) |>.symm_tp)
    |>.trans_tp (vSeq.subst Δenv.wf_sbOfEnv)
  apply EqTm.conv_eq _ ΔvSeq
  rw [Val.toExpr, Clos.toExpr, Expr.subst]
  apply EqTm.cong_pair _ vteq
  . apply vueq.conv_eq
    autosubst
    exact EqTp.refl_tp vBB.wf_right |>.subst_eq
      (EqSb.refl Δenv.wf_sbOfEnv |>.snoc vAA.wf_left vteq.symm_tm)
  . exact EqTp.refl_tp <| vBB.wf_right.subst (Δenv.wf_sbOfEnv.up vAA.wf_left)

private lemma extracted_13 {Δ Γ : Ctx} {A_1 : Expr} {env : List Val} {l_1 : ℕ} (Δenv : WfEnv Δ env Γ)
    (l l' : ℕ) (A B f a : Expr)
    (Γt : Γ ⊢[l_1] Expr.app l l' A B f a : A_1) (vA : Val)
    (vf : Val)
    (vfwf : WfValTm Δ (max l l') vf (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.pi l l' A B)))
    (vfeq :
      Δ ⊢[max l l']
        Val.toExpr ‖Δ‖ vf ≡ Expr.subst (sbOfEnv ‖Δ‖ env) f :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.pi l l' A B))
    (va : Val)
    (vaeq :
      Δ ⊢[l]
        Val.toExpr ‖Δ‖ va ≡ Expr.subst (sbOfEnv ‖Δ‖ env) a : Expr.subst (sbOfEnv ‖Δ‖ env) A)
    (v : Val)
    (vwf :
      WfValTm Δ l' v
        (Expr.subst (Val.toExpr ‖Δ‖ va).toSb (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))))
    (veq :
      Δ ⊢[l']
        Val.toExpr ‖Δ‖ v ≡
          Expr.app l l' (Val.toExpr ‖Δ‖ vA) (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))
            (Val.toExpr ‖Δ‖ vf) (Val.toExpr ‖Δ‖ va) :
          Expr.subst (Val.toExpr ‖Δ‖ va).toSb (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))) :
    WfValTm Δ l_1 v (Expr.subst (sbOfEnv ‖Δ‖ env) A_1) := by
  obtain ⟨rfl, f, _, AB⟩ := Γt.inv_app
  have ⟨_, B⟩ := f.wf_tp.inv_pi
  have vaBA := EqTp.refl_tp B |>.subst_eq (EqSb.refl Δenv.wf_sbOfEnv |>.snoc B.wf_ctx.inv_snoc vaeq)
    |>.trans_tp (by convert (AB.subst Δenv.wf_sbOfEnv).symm_tp using 1; autosubst)
  apply vwf.conv_nf
  convert vaBA using 1
  simp [Clos.toExpr, autosubst]

private lemma extracted_14 {Δ Γ : Ctx} {A_1 : Expr} {env : List Val} {l_1 : ℕ} (Δenv : WfEnv Δ env Γ)
    (l l' : ℕ) (A B f a : Expr)
    (Γt : Γ ⊢[l_1] Expr.app l l' A B f a : A_1) (vA : Val)
    (vAeq : Δ ⊢[l] Val.toExpr ‖Δ‖ vA ≡ Expr.subst (sbOfEnv ‖Δ‖ env) A) (vf : Val)
    (vfwf : WfValTm Δ (max l l') vf (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.pi l l' A B)))
    (vfeq :
      Δ ⊢[max l l']
        Val.toExpr ‖Δ‖ vf ≡ Expr.subst (sbOfEnv ‖Δ‖ env) f :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.pi l l' A B))
    (va : Val)
    (vaeq :
      Δ ⊢[l]
        Val.toExpr ‖Δ‖ va ≡ Expr.subst (sbOfEnv ‖Δ‖ env) a : Expr.subst (sbOfEnv ‖Δ‖ env) A)
    (v : Val)
    (vwf :
      WfValTm Δ l' v
        (Expr.subst (Val.toExpr ‖Δ‖ va).toSb (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))))
    (veq :
      Δ ⊢[l']
        Val.toExpr ‖Δ‖ v ≡
          Expr.app l l' (Val.toExpr ‖Δ‖ vA) (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))
            (Val.toExpr ‖Δ‖ vf) (Val.toExpr ‖Δ‖ va) :
          Expr.subst (Val.toExpr ‖Δ‖ va).toSb (Clos.toExpr ‖Δ‖ (Clos.mk_tp Γ A env B))) :
    Δ ⊢[l_1]
      Val.toExpr ‖Δ‖ v ≡ Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.app l l' A B f a) :
        Expr.subst (sbOfEnv ‖Δ‖ env) A_1 := by
  obtain ⟨rfl, f, _, AB⟩ := Γt.inv_app
  have ⟨_, B⟩ := f.wf_tp.inv_pi
  have vaBA := EqTp.refl_tp B |>.subst_eq (EqSb.refl Δenv.wf_sbOfEnv |>.snoc B.wf_ctx.inv_snoc vaeq)
    |>.trans_tp (by convert (AB.subst Δenv.wf_sbOfEnv).symm_tp using 1; autosubst)
  apply EqTm.conv_eq _ vaBA
  convert veq.trans_tm _ using 1
  . simp [Clos.toExpr, autosubst]
  rw [Expr.subst, Clos.toExpr]
  have ΔB := B.subst (Δenv.wf_sbOfEnv.up B.wf_ctx.inv_snoc)
  apply EqTm.cong_app vAeq _ _ (vaeq.conv_eq vAeq.symm_tp)
  . exact EqTp.refl_tp ΔB |>.conv_binder vAeq.symm_tp
  . apply vfeq.conv_eq
    rw [Expr.subst]
    apply EqTp.cong_pi vAeq.symm_tp (EqTp.refl_tp ΔB)

private lemma extracted_17 {Δ : Ctx} {A B : Expr} {l l' : ℕ} (l_1 l'_1 : ℕ) (B_1 : Clos)
    (t u : Val)
    (Δp : WfValTm Δ (l ⊔ l') (Val.pair l_1 l'_1 B_1 t u) (Expr.sigma l l' A B)) :
    WfValTm Δ l t A := by
  have ⟨_, _, _, t, _, eq⟩ := Δp.inv_pair
  obtain ⟨_, rfl, rfl, Aeq, _⟩ := eq.inv_sigma
  exact t.conv_nf Aeq.symm_tp

private lemma extracted_18 {Δ : Ctx} {A B : Expr} {l l' : ℕ} (l_1 l'_1 : ℕ) (B_1 : Clos)
    (t u : Val)
    (Δp : WfValTm Δ (l ⊔ l') (Val.pair l_1 l'_1 B_1 t u) (Expr.sigma l l' A B)) :
    Δ ⊢[l]
      Val.toExpr ‖Δ‖ t ≡
        Expr.fst l l' A B (Val.toExpr ‖Δ‖ (Val.pair l_1 l'_1 B_1 t u)) : A := by
  have ⟨_, _, _, t, u, eq⟩ := Δp.inv_pair
  obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
  rw [Val.toExpr]
  replace t := t.wf_toExpr.conv Aeq.symm_tp
  have := EqTm.fst_pair Beq.wf_right t u.wf_toExpr
  apply this.symm_tm.trans_tm
  gcongr
  exact WfTm.pair Beq.wf_right t u.wf_toExpr

private lemma extracted_15 {Δ : Ctx} {A B : Expr} {l l' : ℕ} (l_1 l'_1 : ℕ) (B_1 : Clos)
    (t u : Val)
    (Δp : WfValTm Δ (l ⊔ l') (Val.pair l_1 l'_1 B_1 t u) (Expr.sigma l l' A B)) :
    WfValTm Δ l' u
      (Expr.subst (Expr.fst l l' A B (Val.toExpr ‖Δ‖ (Val.pair l_1 l'_1 B_1 t u))).toSb
        B) := by
  have ⟨_, _, _, t, u, eq⟩ := Δp.inv_pair
  obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
  apply u.conv_nf
  gcongr
  apply EqSb.toSb
  rw [Val.toExpr]
  replace Beq := Beq.conv_binder Aeq
  have := EqTm.fst_pair Beq.wf_right t.wf_toExpr u.wf_toExpr
  apply this.symm_tm.trans_tm _ |>.conv_eq Aeq.symm_tp
  apply EqTm.cong_fst Aeq.symm_tp Beq.symm_tp (EqTm.refl_tm _)
  exact WfTm.pair Beq.wf_right t.wf_toExpr u.wf_toExpr

private lemma extracted_16 {Δ : Ctx} {A B : Expr} {l l' : ℕ} (l_1 l'_1 : ℕ) (B_1 : Clos)
    (t u : Val)
    (Δp : WfValTm Δ (l ⊔ l') (Val.pair l_1 l'_1 B_1 t u) (Expr.sigma l l' A B)) :
    Δ ⊢[l']
      Val.toExpr ‖Δ‖ u ≡
        Expr.snd l l' A B (Val.toExpr ‖Δ‖ (Val.pair l_1 l'_1 B_1 t u)) :
        Expr.subst (Expr.fst l l' A B (Val.toExpr ‖Δ‖ (Val.pair l_1 l'_1 B_1 t u))).toSb
          B := by
  have ⟨_, _, _, t, u, eq⟩ := Δp.inv_pair
  obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
  rw [Val.toExpr]
  replace t := t.wf_toExpr.conv Aeq.symm_tp
  replace u := u.wf_toExpr
  have := EqTm.snd_pair Beq.wf_left t (u.conv (by gcongr; exact WfSb.toSb t))
  apply this.symm_tm.conv_eq _ |>.trans_tm
  . symm; gcongr
    symm; gcongr
    . exact t
    . apply u.conv
      gcongr
      exact WfSb.toSb t
  . apply WfTp.subst_eq Beq.wf_left
    apply EqSb.toSb
    simpa [Val.toExpr] using extracted_18 (Δp := Δp)

private lemma extracted_19 {Δ Γ : Ctx} {T : Expr} {env : List Val} {l_1 : ℕ} (Δenv : WfEnv Δ env Γ)
    (l l' : ℕ) (A B p : Expr) (Γt : Γ ⊢[l_1] Expr.snd l l' A B p : T)
    (vp : Val)
    (vpwf : WfValTm Δ (l ⊔ l') vp (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.sigma l l' A B)))
    (vpeq :
      Δ ⊢[l ⊔ l']
        Val.toExpr ‖Δ‖ vp ≡ Expr.subst (sbOfEnv ‖Δ‖ env) p :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.sigma l l' A B))
    (v : Val)
    (vwf :
      WfValTm Δ l' v
        (Expr.subst
          (Expr.fst l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
              (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp)).toSb
          (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B)))
    (veq :
      Δ ⊢[l']
        Val.toExpr ‖Δ‖ v ≡
          Expr.snd l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
            (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp) :
          Expr.subst
            (Expr.fst l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
                (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp)).toSb
            (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B)) :
    WfValTm Δ l_1 v (Expr.subst (sbOfEnv ‖Δ‖ env) T) := by
  obtain ⟨rfl, p, TB⟩ := Γt.inv_snd
  apply vwf.conv_nf
  apply EqTp.trans_tp _ (TB.symm_tp.subst Δenv.wf_sbOfEnv)
  autosubst
  have B := p.wf_tp.inv_sigma.2
  apply B.subst_eq
  apply EqSb.snoc (EqSb.refl Δenv.wf_sbOfEnv) B.wf_ctx.inv_snoc
  gcongr
  convert vpeq using 1; autosubst

private lemma extracted_20 {Δ Γ : Ctx} {T : Expr} {env : List Val} {l_1 : ℕ} (Δenv : WfEnv Δ env Γ)
    (l l' : ℕ) (A B p : Expr) (Γt : Γ ⊢[l_1] Expr.snd l l' A B p : T)
    (vp : Val)
    (vpwf : WfValTm Δ (l ⊔ l') vp (Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.sigma l l' A B)))
    (vpeq :
      Δ ⊢[l ⊔ l']
        Val.toExpr ‖Δ‖ vp ≡ Expr.subst (sbOfEnv ‖Δ‖ env) p :
          Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.sigma l l' A B))
    (v : Val)
    (vwf :
      WfValTm Δ l' v
        (Expr.subst
          (Expr.fst l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
              (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp)).toSb
          (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B)))
    (veq :
      Δ ⊢[l']
        Val.toExpr ‖Δ‖ v ≡
          Expr.snd l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
            (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp) :
          Expr.subst
            (Expr.fst l l' (Expr.subst (sbOfEnv ‖Δ‖ env) A)
                (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B) (Val.toExpr ‖Δ‖ vp)).toSb
            (Expr.subst (Expr.up (sbOfEnv ‖Δ‖ env)) B)) :
    Δ ⊢[l_1]
      Val.toExpr ‖Δ‖ v ≡ Expr.subst (sbOfEnv ‖Δ‖ env) (Expr.snd l l' A B p) :
        Expr.subst (sbOfEnv ‖Δ‖ env) T := by
  obtain ⟨rfl, p, TB⟩ := Γt.inv_snd
  rw [Expr.subst]
  apply EqTm.conv_eq _ (TB.symm_tp.subst Δenv.wf_sbOfEnv)
  apply veq.conv_eq ?eq |>.trans_tm (EqTm.cong_snd_pair vpeq |>.conv_eq ?eq)
  case eq =>
    have B := p.wf_tp.inv_sigma.2
    autosubst
    apply B.subst_eq
    apply EqSb.snoc (EqSb.refl Δenv.wf_sbOfEnv) B.wf_ctx.inv_snoc
    gcongr
    convert vpeq using 1; autosubst

-- Helpful regex for `extract_goal` with `Qq`: '<,'>s/«$\([^»]*\)»/\1/g

mutual
/-- Evaluate the type in an environment of values. -/
partial def evalTp {Δ Γ : Ctx} {T : Expr} {env : List Val} {l : Nat}
    (ΓA : Q($Γ ⊢[$l] ($T))) (Δenv : Q(WfEnv $Δ $env $Γ)) :
    Except String ((v : Val) ×
      Q(WfValTp $Δ $l $v) ×
      Q($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ ($T).subst (sbOfEnv ‖$Δ‖ $env))) :=
  match T with
  | .pi l l' A B => do
    let ⟨vA, vAwf, vAeq⟩ ← evalTp (T := A) (l := l) q(($ΓA).inv_pi.2.wf_ctx.inv_snoc) Δenv
    return ⟨.pi l l' vA (.mk_tp Γ A env B),
      q(by
        obtain ⟨rfl, B⟩ := ($ΓA).inv_pi
        apply WfValTp.pi ($vAwf)
        exact WfClosTp.clos_tp ($vAeq).symm_tp $Δenv B
      ),
      q(by
        unfold Val.toExpr Clos.toExpr
        dsimp [Expr.subst]
        obtain ⟨rfl, B⟩ := ($ΓA).inv_pi
        apply EqTp.cong_pi ($vAeq) (EqTp.refl_tp _)
        exact B.subst (WfSb.up ($Δenv).wf_sbOfEnv B.wf_ctx.inv_snoc) |>.conv_ctx
          (EqCtx.refl ($vAeq).wf_ctx |>.snoc ($vAeq).symm_tp)
      )⟩
  | .sigma l l' A B => do
    let ⟨vA, vAwf, vAeq⟩ ← evalTp (T := A) (l := l) q(($ΓA).inv_sigma.2.wf_ctx.inv_snoc) Δenv
    return ⟨.sigma l l' vA (.mk_tp Γ A env B),
      q(by
        obtain ⟨rfl, B⟩ := ($ΓA).inv_sigma
        apply WfValTp.sigma ($vAwf)
        exact WfClosTp.clos_tp ($vAeq).symm_tp $Δenv B
      ),
      q(by
        unfold Val.toExpr Clos.toExpr
        dsimp [Expr.subst]
        obtain ⟨rfl, B⟩ := ($ΓA).inv_sigma
        apply EqTp.cong_sigma ($vAeq) (EqTp.refl_tp _)
        exact B.subst (WfSb.up ($Δenv).wf_sbOfEnv B.wf_ctx.inv_snoc) |>.conv_ctx
          (EqCtx.refl ($vAeq).wf_ctx |>.snoc ($vAeq).symm_tp)
      )⟩
  | .el a => do
    let ⟨va, vawf, vaeq⟩ ← evalTm (t := a) (l := l+1) (T := .univ l) q(($ΓA).inv_el) Δenv
    return ⟨.el va,
      q(WfValTp.el ($vawf)),
      q(by
        unfold Val.toExpr Expr.subst
        exact EqTp.cong_el ($vaeq)
      )⟩
  | .univ l => return ⟨.univ l,
      q(by
        cases ($ΓA).inv_univ
        apply WfValTp.univ
        . exact ($Δenv).wf_sbOfEnv.wf_dom
        . have := ($ΓA).le_univMax; omega
      ),
      q(by
        unfold Val.toExpr Expr.subst
        cases ($ΓA).inv_univ
        apply EqTp.refl_tp
        apply WfTp.univ
        . exact ($Δenv).wf_sbOfEnv.wf_dom
        . have := ($ΓA).le_univMax; omega
      )⟩
  | A => throw s!"{repr A} is not a type"

/-- Evaluate the expression in an environment of values. -/
partial def evalTm {Δ Γ : Ctx} {t T : Expr} {env : List Val} {l : Nat}
    (Γt : Q($Γ ⊢[$l] ($t) : $T)) (Δenv : Q(WfEnv $Δ $env $Γ)) :
    Except String ((v : Val) ×
      /- 2025-06-17: try later:
      turn `Wf*` into equality judgments that combine normal forms
      with the original type/term.
      This is just to combine the two proof obligations into one. -/
      Q(WfValTm $Δ $l $v (($T).subst (sbOfEnv ‖$Δ‖ $env))) ×
      Q($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ ($t).subst (sbOfEnv ‖$Δ‖ $env) :
        ($T).subst (sbOfEnv ‖$Δ‖ $env))) :=
  match t with
  | .bvar i => do
    return ⟨env[i]?.getD default,
      q(by apply extracted_6 <;> assumption),
      q(by apply extracted_8 <;> assumption)⟩
  | .lam k k' C b => do
    let ⟨vC, vCwf, vCeq⟩ ← evalTp (T := C) (l := k) q(($Γt).inv_lam.2.2.1.wf_ctx.inv_snoc) Δenv
    /- Problem: we don't have the codomain type,
    but `mk_tm` needs it (it's later used in `evalApp`).
    So we evaluate the overall type _in context Γ_,
    match it against Π, and `toExpr`.
    Pretty suboptimal.
    Other options:
    1. Have `evalTm` take `T : Val`. Is this data already available in the typechecker?
    2. Annotate syntax: have `lam` store the codomain type.

    UPDATE 2025-06-18: we need to know that `T` is Π to apply `WfValTm.lam`!
    So we need the NF of `T` in any case. -/
    let ⟨vP, vPwf, vPeq⟩ ← evalTp (T := T) (Δ := Γ) (Γ := Γ) (env := envOfLen ‖Γ‖) (l := l)
      q(($Γt).wf_tp) q(envOfLen_wf ($Δenv).wf_cod)
    let .pi _ _ vA vB := vP | throw s!"{repr vP} is not a Π type"
    /- 2025-06-19: use `Val`s as args to `mk_tm`?
    Resist that refactor until a working MVP exists. -/
    return ⟨.lam k k' vC (.mk_tm Γ k k' (vA.toExpr ‖Γ‖) (vB.toExpr ‖Γ‖) env b),
      q(by apply extracted_1 <;> assumption),
      q(by apply extracted_2 <;> assumption)⟩
  | .app l l' A B f a => do
    -- 2025-06-24: `evalTp`ing A can possibly be avoided, see comment on `Neut.fst`
    let ⟨vA, vAwf, vAeq⟩ ← evalTp (T := A) (l := l) q(($Γt).inv_app.2.2.1.wf_tp) Δenv
    let ⟨vf, vfwf, vfeq⟩ ← evalTm (t := f) (T := .pi l l' A B) (l := max l l') q(($Γt).inv_app.2.1) Δenv
    let ⟨va, vawf, vaeq⟩ ← evalTm (t := a) (T := A) (l := l) q(($Γt).inv_app.2.2.1) Δenv
    let ⟨v, vwf, veq⟩ ← evalApp (A := vA) (B := .mk_tp Γ A env B) (f := vf) (a := va) (l := l) (l' := l')
      (ΔB := q(WfClosTp.clos_tp ($vAeq).symm_tp $Δenv ($Γt).inv_app.2.1.wf_tp.inv_pi.2))
      (Δf := vfwf) (Δa := vawf) (Δ := Δ)
    return ⟨v,
      q(by apply extracted_13 <;> assumption),
      q(by apply extracted_14 <;> assumption)⟩
  | .pair k k' B t u => do
    let ⟨vS, vSwf, vSeq⟩ ← evalTp (T := T) (Δ := Γ) (Γ := Γ) (env := envOfLen ‖Γ‖) (l := l)
      q(($Γt).wf_tp) q(envOfLen_wf ($Δenv).wf_cod)
    let .sigma _ _ vA vB := vS | throw s!"{repr vS} is not a Σ type"
    /- NOTE 2025-06-24: here using `T : Val` would be more efficient;
    shouldn't need to evaluate `vA.toExpr ‖Γ‖`. -/
    let ⟨vt, vtwf, vteq⟩ ← evalTm (t := t) (T := vA.toExpr ‖Γ‖) (l := k)
      q(by apply extracted_11 <;> assumption) Δenv
    let ⟨vu, vuwf, vueq⟩ ← evalTm (t := u) (T := B.subst t.toSb) (Γ := Γ)
      (l := k') q(by apply extracted_4 <;> assumption) Δenv
    return ⟨.pair k k' (.mk_tp Γ (vA.toExpr ‖Γ‖) env B) vt vu,
      q(by apply extracted_10 <;> assumption),
      q(by apply extracted_12 <;> assumption)⟩
  | .fst l l' A B p => do
    let ⟨vp, vpwf, vpeq⟩ ← evalTm (t := p) (T := .sigma l l' A B) (l := max l l')
      q(($Γt).inv_fst.2.1) Δenv
    let ⟨v, vwf, veq⟩ ←
      evalFst (Δ := Δ) (A := A.subst (sbOfEnv ‖Δ‖ env)) (B := B.subst (Expr.up (sbOfEnv ‖Δ‖ env)))
      (p := vp) (l := l) (l' := l') (Δp := q($vpwf))
    return ⟨v,
      q(by
        obtain ⟨rfl, _, TA⟩ := ($Γt).inv_fst
        exact ($vwf).conv_nf (TA.symm_tp.subst ($Δenv).wf_sbOfEnv)
      ),
      q(by
        obtain ⟨rfl, p, TA⟩ := ($Γt).inv_fst
        have ⟨_, B⟩ := p.wf_tp.inv_sigma
        dsimp [Expr.subst] at ($vpeq) ⊢
        apply ($veq).trans_tm _ |>.conv_eq (TA.symm_tp.subst ($Δenv).wf_sbOfEnv)
        apply EqTm.cong_fst
          (EqTp.refl_tp <| TA.wf_right.subst ($Δenv).wf_sbOfEnv)
          (EqTp.refl_tp <| B.subst <| ($Δenv).wf_sbOfEnv.up TA.wf_right)
          $vpeq
      )⟩
  | .snd l l' A B p => do
    let ⟨vp, vpwf, vpeq⟩ ← evalTm (t := p) (T := .sigma l l' A B) (l := max l l')
      q(($Γt).inv_snd.2.1) Δenv
    let ⟨v, vwf, veq⟩ ←
      evalSnd (Δ := Δ) (A := A.subst (sbOfEnv ‖Δ‖ env)) (B := B.subst (Expr.up (sbOfEnv ‖Δ‖ env)))
      (p := vp) (l := l) (l' := l') (Δp := q($vpwf))
    return ⟨v,
      q(by apply extracted_19 <;> assumption),
      q(by apply extracted_20 <;> assumption)⟩
  | .code A => do
    let ⟨vA, vAwf, vAeq⟩ ← evalTp (T := A) (l := l - 1)
      q(by obtain ⟨_, rfl, h, _⟩ := ($Γt).inv_code; exact h)
      Δenv
    return ⟨.code vA,
      q(by
        obtain ⟨_, rfl, _, Auniv⟩ := ($Γt).inv_code
        apply WfValTm.conv_nf _ (Auniv.symm_tp.subst ($Δenv).wf_sbOfEnv)
        have := ($Γt).le_univMax
        exact WfValTm.code (by omega) $vAwf
      ),
      q(by
        obtain ⟨_, rfl, _, Auniv⟩ := ($Γt).inv_code
        apply EqTm.conv_eq _ (Auniv.symm_tp.subst ($Δenv).wf_sbOfEnv)
        rw [Val.toExpr, Expr.subst]
        have := ($Γt).le_univMax
        apply EqTm.cong_code (by omega) $vAeq
      )⟩
  | t => throw s!"{repr t} is not a term"

partial def evalApp {Δ : Ctx} {A : Val} {B : Clos} {f a : Val} {l l' : Nat}
    (ΔB : Q(WfClosTp $Δ $l $l' (($A).toExpr ‖$Δ‖) $B))
    (Δf : Q(WfValTm $Δ (max $l $l') $f (.pi $l $l' (($A).toExpr ‖$Δ‖) (($B).toExpr ‖$Δ‖))))
    (Δa : Q(WfValTm $Δ $l $a (($A).toExpr ‖$Δ‖))) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l' $v (($B).toExpr ‖$Δ‖ |>.subst (($a).toExpr ‖$Δ‖).toSb)) ×
      Q($Δ ⊢[$l'] ($v).toExpr ‖$Δ‖ ≡
        .app $l $l' (($A).toExpr ‖$Δ‖) (($B).toExpr ‖$Δ‖) (($f).toExpr ‖$Δ‖) (($a).toExpr ‖$Δ‖) :
        (($B).toExpr ‖$Δ‖ |>.subst (($a).toExpr ‖$Δ‖).toSb))) :=
  match f with
  | .lam m m' A' (.mk_tm Γ k k' C D env b) => do
    let ⟨v, vwf, veq⟩ ←
      evalTm (t := b) (Δ := Δ) (Γ := (C, l) :: Γ) (env := a :: env) (T := D) (l := l')
        q(by have := extracted_5 $Δf; grind)
        q(by apply extracted_7 <;> assumption)
    return ⟨v,
      q(by apply extracted_3 <;> assumption),
      q(by apply extracted_9 <;> assumption)⟩
  | .neut n => do
    let n : Val := .neut <| .app l l' A B n a
    return ⟨n,
      q(WfValTm.neut_tm <| WfNeutTm.app $ΔB ($Δf).inv_neut $Δa),
      q(by
        unfold $n
        rw [Val.toExpr, Neut.toExpr, Val.toExpr]
        exact EqTm.refl_tm <| WfTm.app ($Δf).inv_neut.wf_toExpr ($Δa).wf_toExpr
      )⟩
  | _ => throw s!"unexpected normal form {repr f} at type Π"

partial def evalFst {Δ : Ctx} {p : Val} {A B : Expr} {l l' : Nat}
    (Δp : Q(WfValTm $Δ (max $l $l') $p (.sigma $l $l' $A $B))) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l $v $A) ×
      Q($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ .fst $l $l' $A $B (($p).toExpr ‖$Δ‖) : $A)) :=
  match p with
  | .pair _ _ _ t _ =>
    return ⟨t,
      q(by apply extracted_17; assumption),
      q(by apply extracted_18; assumption)⟩
  | .neut n =>
    return ⟨.neut (.fst l l' A B n),
      q(WfValTm.neut_tm <| WfNeutTm.fst ($Δp).wf_toExpr.wf_tp.inv_sigma.2 ($Δp).inv_neut),
      q(by
        convert EqTm.refl_tm <| WfTm.fst ($Δp).wf_toExpr using 1
        simp [Val.toExpr, Neut.toExpr])⟩
  | _ => throw s!"unexpected normal form {repr p} at type Σ"

partial def evalSnd {Δ : Ctx} {p : Val} {A B : Expr} {l l' : Nat}
    (Δp : Q(WfValTm $Δ (max $l $l') $p (.sigma $l $l' $A $B))) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l' $v (($B).subst (Expr.fst $l $l' $A $B (($p).toExpr ‖$Δ‖)).toSb)) ×
      Q($Δ ⊢[$l'] ($v).toExpr ‖$Δ‖ ≡ .snd $l $l' $A $B (($p).toExpr ‖$Δ‖) :
        ($B).subst (Expr.fst $l $l' $A $B (($p).toExpr ‖$Δ‖)).toSb)) :=
  match p with
  | .pair _ _ _ _ u =>
    return ⟨u,
      q(by apply extracted_15; assumption),
      q(by apply extracted_16; assumption)⟩
  | .neut n =>
    return ⟨.neut (.snd l l' A B n),
      q(by
        convert WfValTm.neut_tm <| WfNeutTm.snd ($Δp).wf_toExpr.wf_tp.inv_sigma.2 ($Δp).inv_neut using 1
        simp [Val.toExpr, Neut.toExpr]),
      q(by
        convert EqTm.refl_tm <| WfTm.snd ($Δp).wf_toExpr using 1
        simp [Val.toExpr, Neut.toExpr])⟩
  | _ => throw s!"unexpected normal form {repr p} at type Σ"

end
