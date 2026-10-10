module
public import QuantitativeFollowup.AnisotropicFreeEnergyLimits
public import FourPapersCommon.BoundedVarianceConvergence

@[expose] public section

/-! Signed kernel passage for the actual anisotropic process. Domination
is by a fixed integrable kernel, so truncation constants never enter the limit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropicWeightedSelfOverlap_integrable_kernel_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ A : Paper.Overlap→ℝ)
    (hiA : Integrable A (parisiFreeMeasure μ a)) (hb : ∀q,|κ q|≤A q)
    (sample : AnisotropicDisorderBrownianSample n) (J : Finset (Fin n)) :
    ‖anisotropicWeightedSelfOverlap D μ a κ J sample‖≤∫q,A q ∂parisiFreeMeasure μ a := by
  apply norm_integral_le_of_norm_le hiA
  exact .of_forall fun q=>by
    rw [norm_mul,Real.norm_eq_abs]
    have hs:=anisotropicSelectedMeanSquare_bound J (anisotropicProcessMagnetization D μ q sample)
      (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)
    exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans (by simpa only [mul_one] using hb q)

theorem tendsto_anisotropicWeightedSelfOverlap_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κj : ℕ→Paper.Overlap→ℝ) (κ A : Paper.Overlap→ℝ)
    (hκj : ∀j,Measurable (κj j)) (hiA : Integrable A (parisiFreeMeasure μ a))
    (hb : ∀j q,|κj j q|≤A q)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ a,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)))
    (sample : AnisotropicDisorderBrownianSample n) (J : Finset (Fin n)) :
    Tendsto (fun j=>anisotropicWeightedSelfOverlap D μ a (κj j) J sample) atTop
      (𝓝 (anisotropicWeightedSelfOverlap D μ a κ J sample)) := by
  apply tendsto_integral_of_dominated_convergence A
  · intro j
    have hs := (continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : Paper.Overlap=>sample))))
    exact ((hκj j).mul hs).aestronglyMeasurable
  · exact hiA
  · intro j
    exact .of_forall fun q=>by
      rw [norm_mul,Real.norm_eq_abs]
      have hs:=anisotropicSelectedMeanSquare_bound J (anisotropicProcessMagnetization D μ q sample)
        (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)
      exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans (by simpa only [mul_one] using hb j q)
  · exact hlim.mono fun q hq=>hq.mul tendsto_const_nhds

theorem tendsto_variance_anisotropicWeightedSelfOverlap_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κj : ℕ→Paper.Overlap→ℝ) (κ A : Paper.Overlap→ℝ)
    (hκj : ∀j,Measurable (κj j)) (hκ : Measurable κ)
    (hiA : Integrable A (parisiFreeMeasure μ a)) (hA : ∀q,0≤A q)
    (hb : ∀j q,|κj j q|≤A q) (hb0 : ∀q,|κ q|≤A q)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ a,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)))
    (J : Finset (Fin n)) :
    Tendsto (fun j=>variance (anisotropicWeightedSelfOverlap D μ a (κj j) J)
      (anisotropicMeasureSampleLaw D μ a)) atTop
      (𝓝 (variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a))) :=
  tendsto_variance_of_uniform_bound (anisotropicMeasureSampleLaw D μ a) _ _
    (fun j=>measurable_anisotropicWeightedSelfOverlap D μ a (κj j) (hκj j) J)
    (measurable_anisotropicWeightedSelfOverlap D μ a κ hκ J)
    (∫q,A q ∂parisiFreeMeasure μ a) (integral_nonneg hA)
    (fun j sample=>anisotropicWeightedSelfOverlap_integrable_kernel_bound D μ a _ A hiA (hb j) sample J)
    (fun sample=>anisotropicWeightedSelfOverlap_integrable_kernel_bound D μ a κ A hiA hb0 sample J)
    (.of_forall fun sample=>tendsto_anisotropicWeightedSelfOverlap_kernel D μ a κj κ A hκj hiA hb hlim sample J)

theorem anisotropicWeightedProcessHessianEnergy_integrable_kernel_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ A : Paper.Overlap→ℝ)
    (hiA : Integrable (fun q=>(A q)^2) (parisiFreeMeasure μ a)) (hb : ∀q,|κ q|≤A q)
    (sample : AnisotropicDisorderBrownianSample n) (J : Finset (Fin n)) :
    ‖anisotropicWeightedProcessHessianEnergy D μ a κ J sample‖≤
      (∫q,(A q)^2 ∂parisiFreeMeasure μ a)*anisotropicProcessEnergyBound D J/((J.card:ℝ)/2)^2 := by
  unfold anisotropicWeightedProcessHessianEnergy
  rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hh:=norm_integral_le_of_norm_le
    (f:=fun q=>(κ q)^2*anisotropicProcessHessianEnergy D μ J q sample)
    (hiA.mul_const (anisotropicProcessEnergyBound D J))
    (.of_forall fun q=>by
      rw [norm_mul,norm_pow,Real.norm_eq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb q) 2)
        (norm_anisotropicProcessHessianEnergy_le D μ J q sample) (norm_nonneg _) (sq_nonneg _))
  simpa only [integral_mul_const] using hh

theorem tendsto_anisotropicWeightedProcessHessianEnergy_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κj : ℕ→Paper.Overlap→ℝ) (κ A : Paper.Overlap→ℝ)
    (hκj : ∀j,Measurable (κj j)) (hiA : Integrable (fun q=>(A q)^2) (parisiFreeMeasure μ a))
    (hb : ∀j q,|κj j q|≤A q)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ a,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)))
    (sample : AnisotropicDisorderBrownianSample n) (J : Finset (Fin n)) :
    Tendsto (fun j=>anisotropicWeightedProcessHessianEnergy D μ a (κj j) J sample) atTop
      (𝓝 (anisotropicWeightedProcessHessianEnergy D μ a κ J sample)) := by
  apply Tendsto.div_const
  apply tendsto_integral_of_dominated_convergence (fun q=>(A q)^2*anisotropicProcessEnergyBound D J)
  · intro j
    have hs := (measurable_uncurry_anisotropicProcessHessianEnergy D μ J).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : Paper.Overlap=>sample)))
    exact (((hκj j).pow_const 2).mul hs).aestronglyMeasurable
  · exact hiA.mul_const _
  · intro j
    exact .of_forall fun q=>by
      rw [norm_mul,norm_pow,Real.norm_eq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb j q) 2)
        (norm_anisotropicProcessHessianEnergy_le D μ J q sample) (norm_nonneg _) (sq_nonneg _)
  · exact hlim.mono fun q hq=>(hq.pow 2).mul tendsto_const_nhds

theorem tendsto_integral_anisotropicWeightedProcessHessianEnergy_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κj : ℕ→Paper.Overlap→ℝ) (κ A : Paper.Overlap→ℝ)
    (hκj : ∀j,Measurable (κj j)) (hiA : Integrable (fun q=>(A q)^2) (parisiFreeMeasure μ a))
    (hb : ∀j q,|κj j q|≤A q)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ a,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)))
    (J : Finset (Fin n)) :
    Tendsto (fun j=>∫sample,anisotropicWeightedProcessHessianEnergy D μ a (κj j) J sample
      ∂anisotropicMeasureSampleLaw D μ a) atTop
      (𝓝 (∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _=>(∫q,(A q)^2 ∂parisiFreeMeasure μ a)*anisotropicProcessEnergyBound D J/((J.card:ℝ)/2)^2)
  · exact fun j=>(measurable_anisotropicWeightedProcessHessianEnergy D μ a (κj j) (hκj j) J).aestronglyMeasurable
  · exact integrable_const _
  · exact fun j=>.of_forall fun sample=>
      anisotropicWeightedProcessHessianEnergy_integrable_kernel_bound D μ a _ A hiA (hb j) sample J
  · exact .of_forall fun sample=>tendsto_anisotropicWeightedProcessHessianEnergy_kernel D μ a κj κ A hκj hiA hb hlim sample J

end QuantitativeFollowup
