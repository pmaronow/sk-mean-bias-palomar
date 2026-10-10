module
public import QuantitativeFollowup.ScalarStateParameterBound
public import QuantitativeFollowup.ScalarKernelBasics

@[expose] public section

/-! Literal scalar-multiplier continuity on the paper's temperature window.
Every field and state is the actual constructed Parisi solution/diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB FourPapersCommon
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def scalarMultiplierContinuityConstant (B : ℝ) : ℝ :=
  1+2*B^2*(parisiHessianL1Constant B+scalarHessianTemperatureConstant B B+
    14*scalarStateParameterConstant B+14*scalarStateNoiseConstant B*parisiBrownianPathMoment)

theorem scalarMultiplierContinuityConstant_pos (B : ℝ) (hB : 0< B) :
    0< scalarMultiplierContinuityConstant B := by
  have hH : 0≤ parisiHessianL1Constant B := by unfold parisiHessianL1Constant FourPapersCommon.parisiGradientL1Constant;positivity
  have hT : 0≤ scalarHessianTemperatureConstant B B := by
    unfold scalarHessianTemperatureConstant
    have hp := scalarHessianTemperatureSourceConstant_pos B B
    positivity
  have hS := scalarStateParameterConstant_nonneg B
  have hN : 0≤ scalarStateNoiseConstant B := by unfold scalarStateNoiseConstant;positivity
  have hW := parisiBrownianPathMoment_nonneg
  unfold scalarMultiplierContinuityConstant
  positivity

theorem GammaPrime_parameter_window_bound (B b e : ℝ)
    (hB : 0< B) (hb : 0< b) (he : 0< e)
    (hbB : b^2∈Icc (B^2/2) (B^2)) (heB : e^2∈Icc (B^2/2) (B^2))
    (μ ν : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1) :
    ‖GammaPrime b μ q-GammaPrime e ν q‖≤
      scalarMultiplierContinuityConstant B*(Paper.parisiCDFDistance μ ν+|b^2-e^2|) := by
  let X := fun ω=> selectedParisiStateReal b 0 hb.ne' μ ω q
  let Y := fun ω=> selectedParisiStateReal e 0 he.ne' ν ω q
  let F := fun ω=> parisiHessian b μ (q,X ω)
  let G := fun ω=> parisiHessian e ν (q,Y ω)
  let Δ := Paper.parisiCDFDistance μ ν+|b^2-e^2|
  let A := parisiHessianL1Constant B+scalarHessianTemperatureConstant B B+14*scalarStateParameterConstant B
  let D := 14*scalarStateNoiseConstant B
  have hδ := Paper.parisiCDFDistance_nonneg μ ν
  have hΔ : 0≤Δ := by dsimp only [Δ];positivity
  have hA : 0≤ A := by
    have hH : 0≤ parisiHessianL1Constant B := by unfold parisiHessianL1Constant FourPapersCommon.parisiGradientL1Constant;positivity
    have hT : 0≤ scalarHessianTemperatureConstant B B := by
      unfold scalarHessianTemperatureConstant
      have hp := scalarHessianTemperatureSourceConstant_pos B B
      positivity
    have hS := scalarStateParameterConstant_nonneg B
    dsimp only [A];positivity
  have hD : 0≤ D := by dsimp only [D,scalarStateNoiseConstant];positivity
  have hpoint (ω : Paper.BrownianSample) : ‖F ω-G ω‖≤(A+D*‖canonicalBrownianPath ω‖)*Δ := by
    have hH := parisiHessian_parameter_window_bound B b e hb.ne' he.ne' hbB.2 heB.2 μ ν q hq (X ω)
    have hL : ‖parisiHessian e ν (q,X ω)-parisiHessian e ν (q,Y ω)‖≤14*‖X ω-Y ω‖ := by
      simpa only [dist_eq_norm,NNReal.coe_ofNat] using
        (lipschitzWith_parisiHessian e he.ne' ν q).dist_le_mul (X ω) (Y ω)
    have hS := selectedParisiState_parameter_window_bound B b e hB hb he hbB heB μ ν 0 q hq ω
    have ht := (norm_sub_le_norm_sub_add_norm_sub (F ω) (parisiHessian e ν (q,X ω)) (G ω)).trans
      (add_le_add hH (hL.trans (mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ)≤14))))
    apply ht.trans
    have hN := norm_nonneg (canonicalBrownianPath ω)
    dsimp only [A,D,Δ,X,Y,F,G] at *
    nlinarith [mul_nonneg (mul_nonneg hD hN) hδ]
  have hpointSq (ω : Paper.BrownianSample) : ‖F ω^2-G ω^2‖≤2*(A+D*‖canonicalBrownianPath ω‖)*Δ := by
    rw [show F ω^2-G ω^2=(F ω-G ω)*(F ω+G ω) by ring,norm_mul]
    have hsum : ‖F ω+G ω‖≤2 := (norm_add_le _ _).trans (by
      linarith [norm_parisiHessian_le_one_all b μ (q,X ω),norm_parisiHessian_le_one_all e ν (q,Y ω)])
    exact (mul_le_mul (hpoint ω) hsum (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hi (z : ℝ) (hz : 0< z) (ρ : Paper.ParisiMeasure) :
      Integrable (fun ω=> parisiHessian z ρ (q,selectedParisiStateReal z 0 hz.ne' ρ ω q)^2) canonicalBrownianMeasure := by
    simpa only [C_eq_hessian,optimalStateReal_eq_selected z hz.ne' ρ] using integrable_C_sq z hz.ne' ρ hq
  have hFi : Integrable (fun ω=> F ω^2) canonicalBrownianMeasure := hi b hb μ
  have hGi : Integrable (fun ω=> G ω^2) canonicalBrownianMeasure := hi e he ν
  have hboundi : Integrable (fun ω=>2*(A+D*‖canonicalBrownianPath ω‖)*Δ) canonicalBrownianMeasure :=
    ((integrable_const A).add (integrable_norm_canonicalBrownianPath.const_mul D)).const_mul 2 |>.mul_const Δ
  have hint := norm_integral_le_of_norm_le hboundi (.of_forall hpointSq)
  rw [integral_mul_const,integral_const_mul,integral_add (integrable_const A)
    (integrable_norm_canonicalBrownianPath.const_mul D),integral_const_mul] at hint
  simp only [integral_const,probReal_univ,one_smul] at hint
  have hintG : ‖∫ω,G ω^2 ∂canonicalBrownianMeasure‖≤1 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure)
      (.of_forall fun ω=> by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (norm_parisiHessian_le_one_all e ν (q,Y ω)))
  have hg (z : ℝ) (hz : 0< z) (ρ : Paper.ParisiMeasure) :
      GammaPrime z ρ q=z^2*∫ω,parisiHessian z ρ (q,selectedParisiStateReal z 0 hz.ne' ρ ω q)^2 ∂canonicalBrownianMeasure := by
    simp only [GammaPrime,curvatureMoment2,C_eq_hessian,optimalStateReal_eq_selected z hz.ne' ρ]
  rw [hg b hb μ,hg e he ν]
  change ‖b^2*(∫ω,F ω^2 ∂canonicalBrownianMeasure)-e^2*(∫ω,G ω^2 ∂canonicalBrownianMeasure)‖≤_
  rw [show b^2*(∫ω,F ω^2 ∂canonicalBrownianMeasure)-e^2*(∫ω,G ω^2 ∂canonicalBrownianMeasure)=
      b^2*((∫ω,F ω^2 ∂canonicalBrownianMeasure)-(∫ω,G ω^2 ∂canonicalBrownianMeasure))+
      (b^2-e^2)*(∫ω,G ω^2 ∂canonicalBrownianMeasure) by ring,←integral_sub hFi hGi]
  have hmain := mul_le_mul hbB.2 hint (norm_nonneg _) (sq_nonneg B)
  have hextra := mul_le_mul_of_nonneg_left hintG (abs_nonneg (b^2-e^2))
  apply ((norm_add_le _ _).trans (by
    simpa only [norm_mul,Real.norm_of_nonneg (sq_nonneg b),Real.norm_eq_abs] using add_le_add hmain hextra)).trans
  dsimp only [scalarMultiplierContinuityConstant,A,D,Δ,parisiBrownianPathMoment]
  nlinarith

theorem scalar_multiplier_continuity (B : ℝ) (hB : 0< B) :
    ∃C : ℝ,0< C ∧ ∀(μ ν : Paper.ParisiMeasure)(d e : ℝ),
      d∈Icc (B^2/2) (B^2)→e∈Icc (B^2/2) (B^2)→
      ∀q∈Icc (0 : ℝ) 1,‖GammaPrime (Real.sqrt d) μ q-GammaPrime (Real.sqrt e) ν q‖≤
        C*(Paper.parisiCDFDistance μ ν+|d-e|) := by
  refine ⟨scalarMultiplierContinuityConstant B,scalarMultiplierContinuityConstant_pos B hB,?_⟩
  intro μ ν d e hd he q hq
  have hd0 : 0< d := by nlinarith [hd.1,sq_pos_of_pos hB]
  have he0 : 0< e := by nlinarith [he.1,sq_pos_of_pos hB]
  have hh := GammaPrime_parameter_window_bound B (Real.sqrt d) (Real.sqrt e) hB
    (Real.sqrt_pos.mpr hd0) (Real.sqrt_pos.mpr he0)
    (by simpa only [Real.sq_sqrt hd0.le] using hd)
    (by simpa only [Real.sq_sqrt he0.le] using he) μ ν q hq
  simpa only [Real.sq_sqrt hd0.le,Real.sq_sqrt he0.le] using hh

end QuantitativeFollowup
