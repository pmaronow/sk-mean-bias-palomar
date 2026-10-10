module
public import QuantitativeFollowup.ConcentratingPhysicalBounds
public import QuantitativePaper.ResponseCurvatureLower
public import QuantitativePaper.ResponseMeanUpper

@[expose] public section

/-! Actual response estimates on the middle half of a small cutoff. The
Gaussian Hessian upper bound and the genuine all-profile curvature lower
bound produce the sharper powers without a beta-dependent denominator. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem p2_response_mean_upper (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (β lam r q : ℝ) (hβ : 0 < β) (hr : 0 < r) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    {x : ℝ} (hx : x ∈ Icc (q/4) (3*q/4)) :
    responseMeanHessianReal (n := n) μ β (1-r) lam (by linarith) x ≤
      2/(Real.sqrt r*Real.sqrt q) := by
  have hxp : 0 < x := lt_of_lt_of_le (by linarith [hq.1]) hx.1
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hxp.le,by linarith [hx.2,hq.2]⟩
  have hh := responseMeanHessian_upper hn μ β (1-r) lam hβ (by linarith)
    (⟨x,hx01⟩ : Paper.Overlap) hxp
  have hroot : Real.sqrt r*Real.sqrt q/2 ≤ Real.sqrt (r*x) := by
    have he : (Real.sqrt r*Real.sqrt q/2)^2 = r*q/4 := by
      rw [div_pow,mul_pow,Real.sq_sqrt hr.le,Real.sq_sqrt hq.1.le]
      norm_num
    apply Real.le_sqrt_of_sq_le
    rw [he]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hx.1 hr.le
  have hpos : 0 < Real.sqrt r*Real.sqrt q/2 := by positivity [hq.1]
  have hi := one_div_le_one_div_of_le hpos hroot
  have he : 1/(Real.sqrt r*Real.sqrt q/2) = 2/(Real.sqrt r*Real.sqrt q) := by ring
  rw [he] at hi
  have heq : (1-(1-r))*x = r*x := by ring
  simp only [Subtype.coe_mk,heq] at hh
  simpa only [responseMeanHessianReal,projIcc_of_mem zero_le_one hx01] using hh.trans hi

theorem p2_concentrating_delta_lower (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (β lam r q : ℝ) (hβ : 1 ≤ β) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (hlam : 0 ≤ lam)
    (hfloor : lam ≤ β*parisiCDF μ 0)
    (hprofile : ∀x ∈ Icc (q/4) (3*q/4), β*parisiCDF μ x ≤ 2) :
    r*(responseCurvatureConstant 2)^2*(4*q/15) ≤
      vectorConcentratingDelta (n := n) μ β (1-r) (lam/β) (by linarith [hr.1]) (q/4) (q/2) := by
  let D := fun x : ℝ => vectorMeanOverlapDerivative (n := n) μ β (1-r) (lam/β)
    (by linarith [hr.1]) (projIcc 0 1 zero_le_one x)
  have hD : Continuous D := continuous_vectorMeanOverlapDerivativeReal μ β (1-r) (lam/β) (by linarith [hr.1])
  have hell : 0 < q/2 := half_pos hq.1
  have hE : q/4+q/2 = 3*q/4 := by ring
  have ht : (1-r) ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have hc := (contDiff_concentratingIntervalBump (q/4) (q/2)).continuous
  have hi₀ : IntervalIntegrable (fun x => r*(responseCurvatureConstant 2)^2*
      concentratingIntervalBump (q/4) (q/2) x) volume (q/4) (q/4+q/2) :=
    (hc.const_mul _).intervalIntegrable _ _
  have hi₁ : IntervalIntegrable (fun x => D x*concentratingIntervalBump (q/4) (q/2) x)
      volume (q/4) (q/4+q/2) := (hD.mul hc).intervalIntegrable _ _
  have hh := intervalIntegral.integral_mono_on (show q/4 ≤ q/4+q/2 by linarith [hq.1])
    hi₀ hi₁ (fun x hx => by
      have hx' : x ∈ Icc (q/4) (3*q/4) := by simpa only [hE] using hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx'.1,hq.1],by linarith [hx'.2,hq.2]⟩
      have hlow := responseAveragedCurvature_lower hn μ β (1-r) lam 2 hβ ht hlam hfloor
        (⟨x,hx01⟩ : Paper.Overlap) (hprofile x hx')
      have hDr : r*(responseCurvatureConstant 2)^2 ≤ D x := by
        have he := vectorMeanOverlapDerivative_eq_responseCurvature (n := n) μ β (1-r) lam ht.2.le (⟨x,hx01⟩ : Paper.Overlap)
        dsimp only [D]
        rw [projIcc_of_mem zero_le_one hx01,he,show 1-(1-r) = r by ring]
        exact mul_le_mul_of_nonneg_left hlow hr.1.le
      exact mul_le_mul_of_nonneg_right hDr (concentratingIntervalBump_bounds (q/4) (q/2) x).1)
  rw [intervalIntegral.integral_const_mul,concentratingIntervalBump_interval_integral (q/4) (q/2) hell] at hh
  convert hh using 1 <;> first | rfl | ring

theorem p2_concentrating_denominator_local_bound (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β t lam θ a ell B d : ℝ) (hβ : 0 < β) (ht : t < 1)
    (hell : 0 < ell) (ha : 0 ≤ a) (he : a+ell ≤ 1) (hd : 0 ≤ d)
    (hb : ∀x ∈ Icc a (a+ell), responseMeanHessianReal (n := n) (parisiMix μ ν θ) β t lam ht.le x ≤ B)
    (hdensity : ENNReal.ofReal β •
      (parisiCDFPrimitive (parisiMix μ ν θ)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo a (a+ell))) :
    responseC1EnergyDenominator (n := n) μ ν β t lam θ ht.le (concentratingResponseTest a ell hell ha he) ≤
      B*512/(105*ell)+2*d*vectorConcentratingDelta (n := n) (parisiMix μ ν θ) β t (lam/β) ht.le a ell := by
  let ρ := parisiMix μ ν θ
  let w := concentratingResponseTest a ell hell ha he
  have hY : (∫x in (0 : ℝ)..1,(w.slope x)^2*responseMeanHessianReal (n := n) ρ β t lam ht.le x) ≤
      B*512/(105*ell) := by
    have hh := intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_response_C1_mean ρ β t lam w 0 1 ht.le)
      ((w.continuous_slope.pow 2).intervalIntegrable 0 1 |>.const_mul B) (fun x _ => by
        by_cases hx : x ∈ Icc a (a+ell)
        · simpa only [ρ,Pi.pow_apply,mul_comm] using mul_le_mul_of_nonneg_left (hb x hx) (sq_nonneg (w.slope x))
        · have hout : x ∉ Ioo a (a+ell) := fun hi => hx ⟨hi.1.le,hi.2.le⟩
          change (concentratingIntervalIncrement a ell x)^2*_ ≤ B*(concentratingIntervalIncrement a ell x)^2
          rw [concentratingIntervalIncrement_zero_outside a ell x hell hout]
          simp)
    simp only [Pi.pow_apply] at hh
    have hew : (∫x in (0 : ℝ)..1,(w.slope x)^2) = 512/(105*ell) :=
      concentratingResponseTest_energy a ell hell ha he
    rw [intervalIntegral.integral_const_mul,hew] at hh
    convert hh using 1 <;> ring
  have hZ := concentrating_physical_density_bound (n := n) ρ β t lam a ell d hβ ht hell hd hdensity
  have hZeq : (1-t)*β*(∫q : Paper.Overlap,(w.value q)^2*
      responseAveragedCurvature (n := n) ρ β t lam ht.le q ∂(ρ : Measure Paper.Overlap)) =
      β*(∫q : Paper.Overlap,vectorMeanOverlapDerivative (n := n) ρ β t (lam/β) ht.le q*
        (concentratingIntervalBump a ell q)^2 ∂(ρ : Measure Paper.Overlap)) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      dsimp only [w,concentratingResponseTest]
      rw [vectorMeanOverlapDerivative_eq_responseCurvature]
      ring
  have hZ' := mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 2)
  rw [←hZeq] at hZ'
  unfold responseC1EnergyDenominator
  change _ ≤ _
  have hh := add_le_add hY hZ'
  convert hh using 1 <;> ring

end QuantitativePaper
