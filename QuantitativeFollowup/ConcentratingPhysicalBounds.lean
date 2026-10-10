module
public import QuantitativeFollowup.ConcentratingMeasurePairing
public import QuantitativeFollowup.ConcentratingResponseTest
public import QuantitativeFollowup.ConcentratingMeasure
public import QuantitativeFollowup.VectorConcentratingDelta
public import QuantitativePaper.ResponseC1Functionals
public import QuantitativePaper.ResponseC1PhysicalIntegrals

@[expose] public section

/-! Actual signal and density bounds for concentrating tests, with the
physical S′ normalization and the ordinary energy Stieltjes measure. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000
variable {n : ℕ}

theorem responseMeanHessian_le_beta (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (beta t lam : ℝ) (hbeta : 0 < beta) (ht : t < 1) (q : Paper.Overlap) :
    responseMeanHessian (n:=n) μ beta t lam ht.le q ≤ beta := by
  let := vectorMeasureDisorderTilt_probability (n:=n) μ beta t (lam/beta) ht.le
  have hi := (memLp_responseHessianTrace (n:=n) μ beta t lam ht.le q).integrable (by norm_num)
  have he : ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ beta t (lam/beta),
      responseHessianTrace μ beta t ht.le q sample ≤ beta*(n : ℝ) := by
    filter_upwards [vectorMeasure_matrix_order (n:=n) μ beta t (lam/beta) hbeta.ne' ht q] with sample hs
    have htrace := hs.2.2.trace_nonneg
    rw [Matrix.trace_sub,vectorMeasureSpinCovariance_trace] at htrace
    unfold responseHessianTrace
    exact mul_le_mul_of_nonneg_left (by nlinarith [(sq_nonneg ‖vectorMeasureSpinMean μ beta t ht.le q sample‖)]) hbeta.le
  have hh := integral_mono_ae hi (integrable_const (beta*(n : ℝ))) he
  rw [integral_const,probReal_univ,one_smul] at hh
  unfold responseMeanHessian
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/(n : ℝ))
  convert hh' using 1
  field_simp

theorem concentrating_physical_density_bound (μ : Paper.ParisiMeasure)
    (beta t lam a ell d : ℝ) (hbeta : 0 < beta) (ht : t < 1)
    (hell : 0 < ell) (hd : 0 ≤ d)
    (hdensity : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo a (a+ell))) :
    beta*(∫q : Paper.Overlap, vectorMeanOverlapDerivative (n:=n) μ beta t (lam/beta) ht.le q*
        (concentratingIntervalBump a ell q)^2 ∂(μ : Measure Paper.Overlap)) ≤
      d*vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell := by
  let D := fun x : ℝ => vectorMeanOverlapDerivative (n:=n) μ beta t (lam/beta) ht.le
    (projIcc 0 1 zero_le_one x)
  have hD : Continuous D := continuous_vectorMeanOverlapDerivativeReal μ beta t (lam/beta) ht.le
  have hh := concentrating_density_square_bound D hD
    (fun x => vectorMeanOverlapDerivative_nonneg μ beta t (lam/beta) ht.le _)
    a ell hell (ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure) d hd
    (by simpa only [Measure.restrict_smul] using hdensity)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hbeta.le,parisiCDFPrimitive_measure,
    smul_eq_mul] at hh
  have hmap : (∫x : ℝ, D x*(concentratingIntervalBump a ell x)^2
      ∂((μ : Measure Paper.Overlap).map Subtype.val)) =
      ∫q : Paper.Overlap, D q*(concentratingIntervalBump a ell q)^2 ∂(μ : Measure Paper.Overlap) :=
    integral_map_of_stronglyMeasurable measurable_subtype_coe
      (hD.mul ((contDiff_concentratingIntervalBump a ell).continuous.pow 2)).stronglyMeasurable
  rw [hmap] at hh
  simpa only [D,vectorConcentratingDelta,projIcc_of_mem zero_le_one (Subtype.property _)] using hh

theorem concentrating_physical_signal_lower (μ ν ρ : Paper.ParisiMeasure)
    (beta t lam a ell A : ℝ) (ht : t < 1) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1)
    (hsignal : ∀x∈Ioo a (a+ell), A ≤ beta*(parisiCDF ν x-parisiCDF μ x)) :
    A*vectorConcentratingDelta (n:=n) ρ beta t (lam/beta) ht.le a ell ≤
      (1-t)*(∫x in (0 : ℝ)..1, beta*(parisiCDF ν x-parisiCDF μ x)*
        concentratingIntervalBump a ell x*
        responseAveragedCurvatureReal (n:=n) ρ beta t lam ht.le x) := by
  let D := fun x : ℝ => vectorMeanOverlapDerivative (n:=n) ρ beta t (lam/beta) ht.le
    (projIcc 0 1 zero_le_one x)
  let psi := fun x : ℝ => beta*(parisiCDF ν x-parisiCDF μ x)
  have hpsi : Measurable psi :=
    (parisiCDF_measurable ν).sub (parisiCDF_measurable μ) |>.const_mul beta
  have hbound : ∀x, ‖psi x‖ ≤ 2*|beta| := by
    intro x
    dsimp only [psi]
    rw [norm_mul,Real.norm_eq_abs]
    have hbν : |parisiCDF ν x| ≤ 1 := abs_le.mpr ⟨by linarith [parisiCDF_nonneg ν x],parisiCDF_le_one ν x⟩
    have hbμ : |parisiCDF μ x| ≤ 1 := abs_le.mpr ⟨by linarith [parisiCDF_nonneg μ x],parisiCDF_le_one μ x⟩
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |beta| *(|parisiCDF ν x|+|parisiCDF μ x|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg beta)
      _ ≤ _ := by nlinarith [abs_nonneg beta]
  have hh := concentrating_signal_lower D psi
    (continuous_vectorMeanOverlapDerivativeReal ρ beta t (lam/beta) ht.le)
    (fun x => vectorMeanOverlapDerivative_nonneg ρ beta t (lam/beta) ht.le _)
    hpsi (2*|beta|) hbound a ell A hell ha he hsignal
  change A*concentratingDelta a ell D ≤ _
  refine hh.trans_eq ?_
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [D,psi,responseAveragedCurvatureReal]
  rw [vectorMeanOverlapDerivative_eq_responseCurvature]
  ring

theorem concentrating_response_denominator_bound (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta t lam theta a ell d : ℝ) (hbeta : 0 < beta) (ht : t < 1)
    (hell : 0 < ell) (ha : 0 ≤ a) (he : a+ell ≤ 1) (hd : 0 ≤ d)
    (hdensity : ENNReal.ofReal beta •
      (parisiCDFPrimitive (parisiMix μ ν theta)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo a (a+ell))) :
    responseC1EnergyDenominator (n:=n) μ ν beta t lam theta ht.le
      (concentratingResponseTest a ell hell ha he) ≤
      beta*512/(105*ell)+2*d*vectorConcentratingDelta (n:=n)
        (parisiMix μ ν theta) beta t (lam/beta) ht.le a ell := by
  let ρ := parisiMix μ ν theta
  let w := concentratingResponseTest a ell hell ha he
  have hY : (∫x in (0 : ℝ)..1, (w.slope x)^2*
      responseMeanHessianReal (n:=n) ρ beta t lam ht.le x) ≤ beta*512/(105*ell) := by
    have hh : (∫x in (0 : ℝ)..1, (w.slope x)^2*
        responseMeanHessianReal (n:=n) ρ beta t lam ht.le x) ≤
        ∫x in (0 : ℝ)..1, beta*(w.slope x)^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_response_C1_mean ρ beta t lam w 0 1 ht.le)
        ((w.continuous_slope.pow 2).intervalIntegrable 0 1 |>.const_mul beta)
      intro x _
      have hh := mul_le_mul_of_nonneg_left
        (responseMeanHessian_le_beta hn ρ beta t lam hbeta ht (projIcc 0 1 zero_le_one x)) (sq_nonneg (w.slope x))
      simpa only [responseMeanHessianReal,Pi.pow_apply,mul_comm beta] using hh
    rw [intervalIntegral.integral_const_mul,concentratingResponseTest_energy] at hh
    convert hh using 1 <;> ring
  have hZ := concentrating_physical_density_bound (n:=n) ρ beta t lam a ell d
    hbeta ht hell hd hdensity
  have hZeq : (1-t)*beta*(∫q : Paper.Overlap, (w.value q)^2*
      responseAveragedCurvature (n:=n) ρ beta t lam ht.le q ∂(ρ : Measure Paper.Overlap)) =
      beta*(∫q : Paper.Overlap, vectorMeanOverlapDerivative (n:=n) ρ beta t (lam/beta) ht.le q*
        (concentratingIntervalBump a ell q)^2 ∂(ρ : Measure Paper.Overlap)) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    dsimp only [w,concentratingResponseTest]
    rw [vectorMeanOverlapDerivative_eq_responseCurvature]
    ring
  have hZ' : 2*(1-t)*beta*(∫q : Paper.Overlap, (w.value q)^2*
      responseAveragedCurvature (n:=n) ρ beta t lam ht.le q ∂(ρ : Measure Paper.Overlap)) ≤
      2*d*vectorConcentratingDelta (n:=n) ρ beta t (lam/beta) ht.le a ell := by
    have hh := mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 2)
    rw [←hZeq] at hh
    nlinarith only [hh]
  unfold responseC1EnergyDenominator
  change _ ≤ _
  exact add_le_add hY hZ'

end QuantitativeFollowup
