module
public import QuantitativePaper.ResponseMidpointConstants

@[expose] public section

/-! Public exact tent and midpoint scalar calculus for the response argument.
Actual model second variation and localized Dynkin inputs are separate. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
set_option maxHeartbeats 1500000

 theorem responseTent_bounds (ell q : ℝ) (hell : 0<ell) :
    0≤responseTent ell q ∧ responseTent ell q≤1 := by
  refine ⟨le_max_left _ _,max_le (by norm_num) ?_⟩
  have h : 0≤4*|q-ell/2|/ell:=div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hell.le
  linarith

 theorem tsupport_responseTent {ell : ℝ} (hell : 0<ell) :
    tsupport (responseTent ell)=Icc (ell/4) (3*ell/4) := by
  rw [tsupport,support_responseTent hell,closure_Ioo (by linarith : ell/4≠3*ell/4)]

 theorem responseTent_interval_integral {ell : ℝ} (hell : ell∈Ioc (0:ℝ) 1) :
    (∫q in (0:ℝ)..1,responseTent ell q)=ell/4 := by
  have hs : (∫q in Ioc (0:ℝ) 1,responseTent ell q)=∫q,responseTent ell q := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    by_cases hq₀ : q≤0
    · exact responseTent_zero_left hell.1 (by linarith [hell.1])
    · have hq₁ : 1<q := by
        have hh : ¬(0<q ∧ q≤1):=hq
        have hqpos : 0<q:=lt_of_not_ge hq₀
        exact lt_of_not_ge (fun h=>hh ⟨hqpos,h⟩)
      exact responseTent_zero_right hell.1 (by linarith [hell.2])
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),hs,responseTent_integral hell.1]

 theorem responseTent_deriv_interval_energy {ell : ℝ} (hell : ell∈Ioc (0:ℝ) 1) :
    (∫q in (0:ℝ)..1,|deriv (responseTent ell) q|^2)=8/ell := by
  have hs : (∫q in Ioc (0:ℝ) 1,|deriv (responseTent ell) q|^2)=
      ∫q,|deriv (responseTent ell) q|^2 := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_deriv_responseTent hell.1] with q hq hnot
    rw [hq,sq_abs,congrFun (responseTentSlope_sq hell.1) q]
    apply Set.indicator_of_notMem
    intro hmem
    apply hnot
    exact ⟨by linarith [hmem.1,hell.1],by linarith [hmem.2,hell.2]⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),hs,responseTent_deriv_sq_integral hell.1]

 theorem response_tent_calculus {ell : ℝ} (hell : ell∈Ioc (0:ℝ) 1) :
    Continuous (responseTent ell) ∧ (∀q,0≤responseTent ell q ∧ responseTent ell q≤1) ∧
    tsupport (responseTent ell)=Icc (ell/4) (3*ell/4) ∧
    (∫q in (0:ℝ)..1,responseTent ell q)=ell/4 ∧
    (∫q in (0:ℝ)..1,|deriv (responseTent ell) q|^2)=8/ell :=
  ⟨continuous_responseTent ell,fun q=>responseTent_bounds ell q hell.1,
    tsupport_responseTent hell.1,responseTent_interval_integral hell,responseTent_deriv_interval_energy hell⟩

end QuantitativePaper
