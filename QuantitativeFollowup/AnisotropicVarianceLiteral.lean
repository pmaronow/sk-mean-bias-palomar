module
public import QuantitativeFollowup.AnisotropicVarianceCovarianceL2
public import QuantitativeFollowup.AnisotropicSpinPathCovariance

@[expose] public section

/-! The two literal 4/|J|² integrated variance estimates for the actual
marked anisotropic full-profile law and every signed L² representative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

private theorem averaged_energy_fubini (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (E : Paper.Overlap→AnisotropicDisorderBrownianSample n→ℝ)
    (hE : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>E z.1 z.2))
    (C : ℝ) (hb : ∀q sample,‖E q sample‖ ≤ C) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    (∫sample,(∫q,(κ q)^2*E q sample ∂parisiFreeMeasure μ a)/((J.card:ℝ)/2)^2
      ∂anisotropicMeasureSampleLaw D μ a)=
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,E q sample ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a) := by
  have hm := ((hκ.comp measurable_fst).pow_const 2).mul hE
  have hp : Integrable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (κ z.1)^2*E z.1 z.2) ((parisiFreeMeasure μ a).prod (anisotropicMeasureSampleLaw D μ a)) := by
    apply ((hL.integrable_sq.mul_const C).comp_fst (anisotropicMeasureSampleLaw D μ a)).mono'
      hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖(κ z.1)^2*E z.1 z.2‖ ≤ (κ z.1)^2*C
      rw [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_left (hb z.1 z.2) (sq_nonneg _)
  have he := integral_integral_swap (f:=fun q sample=>(κ q)^2*E q sample) hp
  rw [integral_div,←he]
  simp_rw [integral_const_mul]
  have hc : (J.card:ℝ)≠0:=by exact_mod_cast hJ.card_pos.ne'
  field_simp
  <;> ring

theorem anisotropic_weighted_selfOverlap_variance_literal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,anisotropicProcessHessianEnergy D μ J q sample
        ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,anisotropicProcessHessianEnergy D μ J q sample
        ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,anisotropicProcessCovarianceEnergy D μ J q sample
        ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a) := by
  let η:=hL.aestronglyMeasurable.mk κ
  have hm : Measurable η:=hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : κ=ᵐ[parisiFreeMeasure μ a]η:=hL.aestronglyMeasurable.ae_eq_mk
  have hη : MemLp η 2 (parisiFreeMeasure μ a):=(memLp_congr_ae he).mp hL
  have h := anisotropic_weighted_selfOverlap_variance_bounds_signedL2 D μ a ha hμ η hη J hJ
  have hH := averaged_energy_fubini D μ a η hm hη (anisotropicProcessHessianEnergy D μ J)
    (measurable_uncurry_anisotropicProcessHessianEnergy D μ J) (anisotropicProcessEnergyBound D J)
    (norm_anisotropicProcessHessianEnergy_le D μ J) J hJ
  have hC := averaged_energy_fubini D μ a η hm hη (anisotropicProcessCovarianceEnergy D μ J)
    (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J) (anisotropicProcessCovarianceEnergyBound J)
    (norm_anisotropicProcessCovarianceEnergy_le D μ J) J hJ
  have hr (E : Paper.Overlap→AnisotropicDisorderBrownianSample n→ℝ) :
      (∫q,(κ q)^2*(∫sample,E q sample ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a)=
        ∫q,(η q)^2*(∫sample,E q sample ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a := by
    apply integral_congr_ae
    exact he.mono fun q hq=>by dsimp only;rw [hq]
  rw [anisotropicWeightedSelfOverlap_kernel_congr D μ a κ η J he,hr,hr]
  simp only [anisotropicWeightedProcessHessianEnergy,anisotropicWeightedProcessCovarianceEnergy] at h
  rw [hH,hC] at h
  exact h

theorem anisotropic_marked_selfOverlap_variance_literal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>anisotropicWeightedSelfOverlap D μ a κ J p.1)
      (anisotropicMeasureSpinPathLaw D μ a) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessHessianEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessHessianEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessCovarianceEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a) := by
  have hmeas : Measurable (anisotropicWeightedSelfOverlap D μ a κ J) := by
    let η:=hL.aestronglyMeasurable.mk κ
    have he : κ=ᵐ[parisiFreeMeasure μ a]η:=hL.aestronglyMeasurable.ae_eq_mk
    rw [anisotropicWeightedSelfOverlap_kernel_congr D μ a κ η J he]
    exact measurable_anisotropicWeightedSelfOverlap D μ a η
      hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable J
  rw [(measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).variance_fun_comp
    (f:=anisotropicWeightedSelfOverlap D μ a κ J) hmeas.aemeasurable]
  have hHm (q : Paper.Overlap) : Measurable (anisotropicProcessHessianEnergy D μ J q) := by
    have h := (measurable_uncurry_anisotropicProcessHessianEnergy D μ J).comp
      ((measurable_const (a:=q)).prodMk measurable_id)
    change Measurable (fun sample=>anisotropicProcessHessianEnergy D μ J q sample)
    simpa only [Function.comp_def,id_eq] using h
  have hCm (q : Paper.Overlap) : Measurable (anisotropicProcessCovarianceEnergy D μ J q) := by
    have h := (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J).comp
      ((measurable_const (a:=q)).prodMk measurable_id)
    change Measurable (fun sample=>anisotropicProcessCovarianceEnergy D μ J q sample)
    simpa only [Function.comp_def,id_eq] using h
  have hH (q : Paper.Overlap) := integral_anisotropicMeasureSpinPathLaw_sample D μ a
    (anisotropicProcessHessianEnergy D μ J q) (hHm q)
  have hC (q : Paper.Overlap) := integral_anisotropicMeasureSpinPathLaw_sample D μ a
    (anisotropicProcessCovarianceEnergy D μ J q) (hCm q)
  simp_rw [hH,hC]
  exact anisotropic_weighted_selfOverlap_variance_literal D μ a ha hμ κ hL J hJ

end QuantitativeFollowup
