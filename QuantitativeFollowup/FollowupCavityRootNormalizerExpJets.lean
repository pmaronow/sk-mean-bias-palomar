module
public import QuantitativeFollowup.FollowupCavityRootNormalizerHeat
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceJets
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! Honest global Gaussian envelopes for the first two spatial jets of the
actual root exponential density. Only its proved C² and Lipschitz bounds are
used, including singular disorder couplings. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem exponential_C2_gaussian_jets {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E→ℝ) (hF : ContDiff ℝ 2 F) (C H : ℝ) (hC : 0≤C) (hH : 0≤H)
    (hLip : LipschitzWith ⟨C,hC⟩ F) (hHess : ∀x,‖fderiv ℝ (fderiv ℝ F) x‖≤H)
    (a : ℝ) : ∃ B K : ℝ,0≤B ∧ 0≤K ∧
      (∀x,‖fderiv ℝ (fun y=>Real.exp (a*F y)) x‖≤B*Real.exp (K*‖x‖)) ∧
      (∀x,‖fderiv ℝ (fderiv ℝ (fun y=>Real.exp (a*F y))) x‖≤B*Real.exp (K*‖x‖)) := by
  let V:=fun x=>a*F x
  have hV : ContDiff ℝ 2 V:=contDiff_const.mul hF
  have hd (x : E) : ‖fderiv ℝ F x‖≤C:=norm_fderiv_le_of_lipschitz ℝ hLip
  have hVd (x : E) : ‖fderiv ℝ V x‖≤|a| *C := by
    have he : V=a • F:=rfl
    rw [he,fderiv_const_smul_field,Pi.smul_apply,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hd x) (abs_nonneg a)
  have hVH (x : E) : ‖fderiv ℝ (fderiv ℝ V) x‖≤|a| *H := by
    have he : V=a • F:=rfl
    rw [he,fderiv_const_smul_field,fderiv_const_smul_field,Pi.smul_apply,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hHess x) (abs_nonneg a)
  let B0:=Real.exp (|a| *|F 0|)
  let K:=|a| *C
  let Q:=|a| *H+(|a| *C)^2
  let B:=B0*(1+|a| *C+Q)
  have hQ : 0≤Q:=by dsimp [Q];positivity
  have hB0 : 0≤B0:=by dsimp [B0];positivity
  have hB : 0≤B:=by dsimp [B];positivity
  have hK : 0≤K:=by dsimp [K];positivity
  have he (x : E) : Real.exp (V x)≤B0*Real.exp (K*‖x‖) := by
    dsimp only [B0,K,V]
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl : |F x-F 0|≤C*‖x‖ := by
      convert hLip.dist_le_mul x 0 using 1 <;> simp only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,sub_zero] <;> rfl
    have hh: |F x|≤|F x-F 0|+|F 0| := by
      convert abs_add_le (F x-F 0) (F 0) using 1 <;> ring_nf
    have ha:=le_abs_self (a*F x)
    rw [abs_mul] at ha
    have hm:=mul_le_mul_of_nonneg_left (hh.trans (add_le_add hl le_rfl)) (abs_nonneg a)
    nlinarith only [ha,hm]
  have hEH (x : E) : ‖fderiv ℝ (fderiv ℝ (fun y=>Real.exp (V y))) x‖≤Real.exp (V x)*Q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have hHv : ‖fderiv ℝ (fderiv ℝ V) x v w‖≤(|a| *H)*‖v‖*‖w‖ :=
      ((fderiv ℝ (fderiv ℝ V) x v).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ V) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hVH x) (norm_nonneg v))) (norm_nonneg w))
    have hv : ‖fderiv ℝ V x v‖≤(|a| *C)*‖v‖:=
      ((fderiv ℝ V x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hVd x) (norm_nonneg v))
    have hw : ‖fderiv ℝ V x w‖≤(|a| *C)*‖w‖:=
      ((fderiv ℝ V x).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hVd x) (norm_nonneg w))
    change ‖exponentialDensityHessian (fun y=>Real.exp (V y)) x v w‖≤_
    rw [exponentialDensityHessian_exp_potential V hV,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _≤Real.exp (V x)*(‖exponentialDensityHessian V x v w‖+
          ‖fderiv ℝ V x v*fderiv ℝ V x w‖):=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _≤Real.exp (V x)*((|a| *H)*‖v‖*‖w‖+((|a| *C)*‖v‖)*((|a| *C)*‖w‖)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (add_le_add hHv (mul_le_mul hv hw (norm_nonneg _) (by positivity)))
          (Real.exp_pos _).le
      _=(Real.exp (V x)*Q)*‖v‖*‖w‖:=by dsimp [Q];ring
  refine ⟨B,K,hB,hK,?_,?_⟩
  · intro x
    have hD:=((hV.differentiable (by norm_num) x).hasFDerivAt.exp).fderiv
    rw [hD,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _≤(B0*Real.exp (K*‖x‖))*(|a| *C):=mul_le_mul (he x) (hVd x) (norm_nonneg _) (by positivity)
      _≤B*Real.exp (K*‖x‖) := by
        have hm:=mul_le_mul_of_nonneg_left (show |a| *C≤1+|a| *C+Q by linarith)
          (mul_nonneg hB0 (Real.exp_pos (K*‖x‖)).le)
        convert hm using 1 <;> dsimp only [B] <;> ring
  · intro x
    calc
      _≤Real.exp (V x)*Q:=hEH x
      _≤(B0*Real.exp (K*‖x‖))*Q:=mul_le_mul_of_nonneg_right (he x) hQ
      _≤B*Real.exp (K*‖x‖) := by
        have haC : 0≤|a| *C:=mul_nonneg (abs_nonneg a) hC
        have hm:=mul_le_mul_of_nonneg_left (show Q≤1+|a| *C+Q by linarith)
          (mul_nonneg hB0 (Real.exp_pos (K*‖x‖)).le)
        convert hm using 1 <;> dsimp only [B] <;> ring

end QuantitativeFollowup
