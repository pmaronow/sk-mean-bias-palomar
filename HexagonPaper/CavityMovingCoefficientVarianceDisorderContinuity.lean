module
public import HexagonPaper.CavityMovingCoefficientTailMixedDerivative

@[expose] public section

/-! Uniform disorder/field moduli of actual native future spin squares
and variance responses. The finite posterior bound is transferred through
the genuine dyadic physical-law limit, with no finite-profile restriction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
open scoped Topology ContDiff NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

theorem cavityFiniteRestartPosteriorSquare_parameter_difference_bound
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap) (v : ℕ) (i : Fin n)
    (g h : AnisotropicDisorder n) (x y : Field n) :
    ‖anisotropicFiniteRestartPosteriorSquare D s g q v i x-
      anisotropicFiniteRestartPosteriorSquare D s h q v i y‖≤
      (4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D‖)*
        ‖(anisotropicDisorderInjection n g+anisotropicFieldInjection n x)-
          (anisotropicDisorderInjection n h+anisotropicFieldInjection n y)‖ := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let G:=fun H=>∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) L (k+2) v (cavityCoordinateFeature i) H z
    ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) L (k+2) H
  let P:=anisotropicDisorderInjection n g+anisotropicFieldInjection n x
  let Q:=anisotropicDisorderInjection n h+anisotropicFieldInjection n y
  have hL:=cascadePosterior_retained_square_lipschitz (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs) (anisotropicSchemeMass_le_one cs 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs)) L (k+2) v (cavityCoordinateFeature i)
  have hd:=hL.dist_le_mul (anisotropicEnergyMap D P) (anisotropicEnergyMap D Q)
  rw [dist_eq_norm,dist_eq_norm,←map_sub] at hd
  change ‖G (anisotropicEnergyMap D P)-G (anisotropicEnergyMap D Q)‖≤_
  apply hd.trans
  have hn:=(anisotropicEnergyMap D).le_opNorm (P-Q)
  simpa [P,Q,mul_assoc] using mul_le_mul_of_nonneg_left hn
    (by positivity : 0≤((4*‖cavityCoordinateFeature i‖₊^2 : ℝ≥0) : ℝ))

theorem cavityNativeRestartSpinSquare_parameter_difference_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q r : Paper.Overlap)
    (hqr : q≤r) (i : Fin n) (g h : AnisotropicDisorder n) (x y : Field n) :
    ‖anisotropicRestartSpinSquare D μ g q x i r-anisotropicRestartSpinSquare D μ h q y i r‖≤
      (4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D‖)*
        ‖(anisotropicDisorderInjection n g+anisotropicFieldInjection n x)-
          (anisotropicDisorderInjection n h+anisotropicFieldInjection n y)‖ := by
  apply le_of_tendsto (((tendsto_anisotropicDyadicRestartPosteriorSquare D μ g q r hqr i x).sub
    (tendsto_anisotropicDyadicRestartPosteriorSquare D μ h q r hqr i y)).norm)
  exact .of_forall fun j=>cavityFiniteRestartPosteriorSquare_parameter_difference_bound D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q (vectorDyadicTimeIndex r j) i g h x y

theorem cavityNativeVarianceResponse_parameter_difference_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (i : Fin n) (g h : AnisotropicDisorder n) (x y : Field n) :
    ‖anisotropicRestartVarianceResponse D μ g q x i-anisotropicRestartVarianceResponse D μ h q y i‖≤
      (1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D‖)*
        ‖(anisotropicDisorderInjection n g+anisotropicFieldInjection n x)-
          (anisotropicDisorderInjection n h+anisotropicFieldInjection n y)‖ := by
  let F:=fun (g : AnisotropicDisorder n) (x : Field n) (r : Paper.Overlap)=>
    max 0 ((r : ℝ)-(q : ℝ))*anisotropicRestartSpinSquare D μ g q x i r
  let K:=(4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D‖)*
    ‖(anisotropicDisorderInjection n g+anisotropicFieldInjection n x)-
      (anisotropicDisorderInjection n h+anisotropicFieldInjection n y)‖
  have hK : 0≤K := by dsimp only [K]; positivity
  have hm (g : AnisotropicDisorder n) (x : Field n) : Measurable (F g x) :=
    (measurable_const.max (measurable_subtype_coe.sub_const _)).mul
      (measurable_anisotropicRestartSpinSquare D μ g q x i)
  have hi (g : AnisotropicDisorder n) (x : Field n) : Integrable (F g x) (μ : Measure Paper.Overlap) :=
    Integrable.of_bound (hm g x).aestronglyMeasurable 1 (.of_forall fun r=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (le_max_left _ _)
        (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1)]
      exact (mul_le_of_le_one_right (le_max_left _ _)
        (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2).trans
          (max_le (by norm_num) (by linarith [r.property.2,q.property.1])))
  have hB (r : Paper.Overlap) : ‖F g x r-F h y r‖≤K := by
    by_cases hqr : q≤r
    · have hd:=cavityNativeRestartSpinSquare_parameter_difference_bound D μ q r hqr i g h x y
      rw [←mul_sub,norm_mul,Real.norm_of_nonneg (le_max_left _ _)]
      exact (mul_le_mul_of_nonneg_left hd (le_max_left _ _)).trans
        ((mul_le_mul_of_nonneg_right
          (max_le (by norm_num) (by linarith [r.property.2,q.property.1])) hK).trans_eq (one_mul _))
    · have hz : max 0 ((r : ℝ)-(q : ℝ))=0 :=
        max_eq_left (sub_nonpos.mpr (show (r : ℝ)≤(q : ℝ) from le_of_not_ge hqr))
      simpa only [F,hz,zero_mul,sub_self,norm_zero] using hK
  have hI : ‖∫r,F g x r-F h y r∂(μ : Measure Paper.Overlap)‖≤K := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=(μ : Measure Paper.Overlap)) (.of_forall hB)
  have he : anisotropicRestartVarianceResponse D μ g q x i-anisotropicRestartVarianceResponse D μ h q y i=
      -(1/2 : ℝ)*(∫r,F g x r-F h y r∂(μ : Measure Paper.Overlap)) := by
    rw [integral_sub (hi g x) (hi h y)]
    unfold anisotropicRestartVarianceResponse F
    ring
  rw [he,norm_mul]
  norm_num only [norm_neg,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ)≤1/2)).trans_eq (by ring)

end HexagonPaper
