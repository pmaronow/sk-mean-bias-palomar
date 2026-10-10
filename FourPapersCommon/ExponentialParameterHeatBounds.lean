module
public import FourPapersCommon.ExponentialSmoothBounds
public import FourPapersCommon.ExponentialAffineChange

@[expose] public section

/-! Actual exponential jets on a bounded parameter cylinder give the
uniform value and derivative envelopes needed for Gaussian heat differentiation. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_of_exponentialSmoothOn {F : E→ℝ} {s : Set E}
    (hF : ExponentialSmoothOn F s) : ContDiffOn ℝ ∞ F s :=
  fun x hx=>(hF.smooth x hx).contDiffWithinAt

theorem ExponentialSmoothOn.parameter_heat_bounds (F : ℝ×E→ℝ) (l u : ℝ)
    (hF : ExponentialSmoothOn F ((Ioo l u)×ˢ(univ : Set E))) :
    ∃B K : ℝ,0≤B ∧ 0≤K ∧
      (∀q∈Ioo l u,∀y,‖F (q,y)‖≤B*Real.exp (K*‖y‖)) ∧
      (∀q∈Ioo l u,∀y,‖_root_.fderiv ℝ F (q,y)‖≤B*Real.exp (K*‖y‖)) ∧
      (∀q∈Ioo l u,∀y,‖_root_.fderiv ℝ (_root_.fderiv ℝ (fun z=>F (q,z))) y‖≤B*Real.exp (K*‖y‖)) := by
  obtain ⟨C,R,hC,hR,hb⟩:=hF.common_bound 2
  let M : ℝ:=max |l| |u|
  let B : ℝ:=C*Real.exp (R*M)
  have hM : 0≤M:=(abs_nonneg l).trans (le_max_left _ _)
  have hC0 : 0≤C:=zero_le_one.trans hC
  have hqM (q : ℝ) (hq : q∈Ioo l u) : |q|≤M := by
    apply abs_le.mpr
    constructor
    · have hml : |l|≤M:=le_max_left _ _
      linarith [neg_abs_le l,hq.1]
    · exact hq.2.le.trans ((le_abs_self u).trans (le_max_right _ _))
  have hnorm (q : ℝ) (hq : q∈Ioo l u) (y : E) : ‖(q,y)‖≤M+‖y‖ := by
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le ((hqM q hq).trans (le_add_of_nonneg_right (norm_nonneg y)))
      (le_add_of_nonneg_left hM)
  have hjet (r : ℕ) (hr : r≤2) (q : ℝ) (hq : q∈Ioo l u) (y : E) :
      ‖iteratedFDeriv ℝ r F (q,y)‖≤B*Real.exp (R*‖y‖) := by
    calc
      _≤C*Real.exp (R*‖(q,y)‖):=hb r hr (q,y) ⟨hq,mem_univ y⟩
      _≤C*Real.exp (R*(M+‖y‖)):=mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hnorm q hq y) hR)) hC0
      _=B*Real.exp (R*‖y‖):=by rw [mul_add,Real.exp_add];dsimp [B];ring
  refine ⟨B,R,by dsimp [B];positivity,hR,?_,?_,?_⟩
  · intro q hq y
    simpa only [norm_iteratedFDeriv_zero] using hjet 0 (by omega) q hq y
  · intro q hq y
    simpa only [norm_iteratedFDeriv_one] using hjet 1 (by omega) q hq y
  · intro q hq y
    let L:=ContinuousLinearMap.inr ℝ ℝ E
    have hL : ‖L‖≤1:=by
      apply L.opNorm_le_bound zero_le_one
      intro v
      simp [L]
    have hL2 : ‖L‖^2≤1:=by nlinarith [norm_nonneg L]
    have hs:=norm_iteratedFDeriv_precomp_affine_le_at L (q,0) F y
      (by simpa only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using
        hF.smooth (q,y) ⟨hq,mem_univ y⟩) 2
    have hs': ‖iteratedFDeriv ℝ 2 (fun z=>F (q,z)) y‖≤‖iteratedFDeriv ℝ 2 F (q,y)‖:=by
      simpa only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add,mul_one] using
        hs.trans (mul_le_mul_of_nonneg_left hL2 (norm_nonneg _))
    have hh:=hs'.trans (hjet 2 le_rfl q hq y)
    simpa only [←norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] using hh

end FourPapersCommon
