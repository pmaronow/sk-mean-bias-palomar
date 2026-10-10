module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquareUniform

@[expose] public section

/-! Honest affine field pullbacks preserve the depth-independent derivative
modulus of actual finite posterior expectations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

 theorem fderiv_affine_pullback_lipschitz
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F→G) (hf : Differentiable ℝ f) (C : ℝ≥0)
    (hC : LipschitzWith C (fderiv ℝ f)) (A : E→L[ℝ]F) (c : F) :
    LipschitzWith (C*‖A‖₊^2) (fderiv ℝ (fun x=>f (c+A x))) := by
  have hd (x) : fderiv ℝ (fun x=>f (c+A x)) x=(fderiv ℝ f (c+A x)).comp A := by
    exact ((hf _).hasFDerivAt.comp x (A.hasFDerivAt.const_add c)).fderiv
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,hd,hd,←ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hh := hC.norm_sub_le (c+A x) (c+A y)
  simp only [add_sub_add_left_eq_sub,←map_sub] at hh
  have hb:=hh.trans (mul_le_mul_of_nonneg_left (A.le_opNorm (x-y)) C.coe_nonneg)
  simpa only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,dist_eq_norm,pow_two,mul_assoc,
    mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right hb (norm_nonneg A)

variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

theorem cascadePosterior_retained_square_differential_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S) :
    ‖fderiv ℝ (fun Q=>∫z,cascadePosteriorRetainedSquare V a L j i K Q z
      ∂cascadePosteriorGaussianLaw V a L j Q) H‖≤4*‖K‖^2 := by
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L j H
  rw [(hasFDerivAt_cascadePosterior_retained_square V a ha ha1 hdec L j i K H).fderiv]
  have hb (z : (Fin j→Field n)×S) :
      ‖fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H+
        cascadePosteriorRetainedSquare V a L j i K H z •
          fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤4*‖K‖^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    have hsq : |cascadePosteriorRetainedSquare V a L j i K H z|≤‖K‖^2 := by
      simpa only [cascadePosteriorRetainedSquare,abs_pow] using
        pow_le_pow_left₀ (abs_nonneg _) (cascadePosteriorRetainedMean_bound V a ha L j i K H z) 2
    have hd : ‖fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤2 := by
      rw [←norm_iteratedFDeriv_one]
      exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z
    have hh:=add_le_add (cascadePosteriorRetainedSquare_differential_bound V a ha ha1 hdec L j i K H z)
      (mul_le_mul hsq hd (norm_nonneg _) (by positivity))
    convert hh using 1 <;> ring
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=cascadePosteriorGaussianLaw V a L j H) (.of_forall hb)

theorem cascadePosterior_retained_square_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S) :
    LipschitzWith (4*‖K‖₊^2) (fun H=>∫z,cascadePosteriorRetainedSquare V a L j i K H z
      ∂cascadePosteriorGaussianLaw V a L j H) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun H=>(hasFDerivAt_cascadePosterior_retained_square V a ha ha1 hdec L j i K H).differentiableAt)
  intro H
  rw [←NNReal.coe_le_coe,coe_nnnorm]
  simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,coe_nnnorm] using
    cascadePosterior_retained_square_differential_bound V a ha ha1 hdec L j i K H

end QuantitativeFollowup
