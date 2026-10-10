module
public import QuantitativeFollowup.FollowupCavityThirdRestMomentThermalEndpoint
public import QuantitativeFollowup.FollowupCavityCubicComparison
public import QuantitativeFollowup.FollowupCavityCubicSupremum

@[expose] public section

/-! Literal thermal third-moment budget, integrated over the actual free
measure and uniform over the genuine cavity interpolation family. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem integrable_vectorSelfOverlap_cubic_curve (hn:0<n)
    (μ:Paper.ParisiMeasure) (β t a:ℝ) (ht:t≤1)
    (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>∫z,|vectorSelfOverlap (n:=n) μ β t ht q z-(q:ℝ)|^3
      ∂vectorMeasureSpinPathLaw μ β t a ht) ν := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hm : Measurable (fun q:Paper.Overlap=>∫z,
      |vectorSelfOverlap (n:=n) μ β t ht q z-(q:ℝ)|^3
        ∂vectorMeasureSpinPathLaw μ β t a ht) :=
    ((measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht).abs.pow_const 3).stronglyMeasurable.integral_prod_right.measurable
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact .of_forall fun q=>by
    have hb (z:VectorMarkedSample n) : ‖|vectorSelfOverlap μ β t ht q z-(q:ℝ)|^3‖≤1 := by
      rw [Real.norm_of_nonneg (by positivity)]
      have hb:=norm_vectorCenteredSelfOverlap_le_one hn μ β t ht q z
      rw [Real.norm_eq_abs] at hb
      exact (pow_le_pow_left₀ (abs_nonneg _) hb 3).trans_eq (by norm_num)
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht) (.of_forall hb)

theorem followup_cavity_one_third_rest_moment_thermal_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) :
    cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a≤
      64*((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q
        ∂parisiFreeMeasure μ a)+
        followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]))+
      16*followupSourceCubicIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
      32/((n+1:ℕ):ℝ)^3 := by
  let ht:1-ρ<1:=by linarith[hρ.1]
  let ν:=parisiFreeMeasure μ a
  let A:=foundationThermalTrace (n:=n+1) μ β (1-ρ) a ht.le
  let J:=foundationMeanCovariance (n:=n+1) μ β (1-ρ) a ht.le
  let H:=fun q:Paper.Overlap=>∫z,|vectorSelfOverlap (n:=n+1) μ β (1-ρ) ht.le q z-(q:ℝ)|^3
    ∂vectorMeasureSpinPathLaw μ β (1-ρ) a ht.le
  let C:=32/((n+1:ℕ):ℝ)^3
  have hi:=integrable_foundationThermalTrace_and_meanCovariance (n:=n+1)
    μ β (1-ρ) a hβ.ne' ht ν
  have hiH:=integrable_vectorSelfOverlap_cubic_curve (n:=n+1) (by omega) μ β (1-ρ) a ht.le ν
  have hh:=integral_mono (integrable_cavityCubicPairMoment
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a)
    ((((hi.1.add hi.2).const_mul 64).add (hiH.const_mul 16)).add (integrable_const C))
    (fun q=>followup_cavity_one_cubic_pair_thermal_le hn μ β ρ a hβ hρ q)
  simp only [Pi.add_apply] at hh
  have hadd:=integral_add (((hi.1.add hi.2).const_mul 64).add (hiH.const_mul 16)) (integrable_const C)
  have hfirst:=integral_add ((hi.1.add hi.2).const_mul 64) (hiH.const_mul 16)
  have hAJ:=integral_add hi.1 hi.2
  simp only [Pi.add_apply] at hadd hfirst hAJ
  rw [hadd,hfirst,integral_const_mul,integral_const_mul,hAJ,integral_const] at hh
  have hm : ν.real univ=1-a := by
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  rw [hm,smul_eq_mul] at hh
  have hc : 0≤C:=by dsimp only [C];positivity
  change (∫q,cavityCubicPairMoment _ μ a q∂ν)≤_ at hh
  change (∫q,cavityCubicPairMoment _ μ a q∂ν)≤
    64*((∫q,A q∂ν)+(∫q,J q∂ν))+16*(∫q,H q∂ν)+C
  exact hh.trans (by nlinarith[mul_nonneg ha.1 hc])

theorem followup_cavity_third_rest_moment_thermal (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hfloor:a≤Paper.parisiCDF μ 0) :
    cavityPhysicalCubicSupremum n μ β ρ a hβ hρ≤Real.exp (21*β^2)*
      (64*((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q
        ∂parisiFreeMeasure μ a)+
        followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]))+
        16*followupSourceCubicIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
        32/((n+1:ℕ):ℝ)^3) := by
  have h1:=followup_cavity_one_third_rest_moment_thermal_le hn μ β ρ a hβ hρ ha
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u,rfl⟩
  exact (cavityThirdMoment_comparison hn β ρ hβ hρ μ a ha hfloor u 1 u.property
    ⟨zero_le_one,le_rfl⟩).trans
    (mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _))

end QuantitativeFollowup
