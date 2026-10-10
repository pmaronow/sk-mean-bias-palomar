module
public import QuantitativeFollowup.AnisotropicFreeObservables

@[expose] public section

/-! Genuine weighted selected-Hessian energy limits under the native
anisotropic tilted diffusion laws and the actual free Stieltjes measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem measurable_anisotropicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (J : Finset (Fin n)) : Measurable (anisotropicWeightedProcessHessianEnergy D μ a κ J) := by
  have hm := ((hκ.comp measurable_fst).pow_const 2).mul
    (measurable_uncurry_anisotropicProcessHessianEnergy D μ J)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable.div_const _

theorem measurable_anisotropicDyadicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (J : Finset (Fin n)) (j : ℕ) : Measurable (anisotropicDyadicWeightedProcessHessianEnergy D μ a κ J j) := by
  have hmap : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      Paper.parisiGridRound (vectorDyadicIndex j) z.1) :=
    (Paper.measurable_parisiGridRound (vectorDyadicIndex j)).comp measurable_fst
  have hm := ((hκ.comp hmap).pow_const 2).mul
    ((measurable_uncurry_anisotropicFiniteProcessHessianEnergy D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) J).comp (hmap.prodMk measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable.div_const _

theorem norm_anisotropicWeightedProcessHessianEnergy_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ)
    (J : Finset (Fin n)) (K : ℝ) (hb : ∀q,|κ q|≤K)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicWeightedProcessHessianEnergy D μ a κ J sample‖≤
      K^2*anisotropicProcessEnergyBound D J/((J.card:ℝ)/2)^2 := by
  unfold anisotropicWeightedProcessHessianEnergy
  rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply anisotropic_freeIntegral_bound μ a ha _ _ (mul_nonneg (sq_nonneg _) (anisotropicProcessEnergyBound_nonneg D J))
  intro q
  rw [norm_mul,norm_pow,Real.norm_eq_abs]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb q) 2)
    (norm_anisotropicProcessHessianEnergy_le D μ J q sample) (norm_nonneg _ ) (sq_nonneg _)

theorem norm_anisotropicDyadicWeightedProcessHessianEnergy_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ)
    (J : Finset (Fin n)) (K : ℝ) (hb : ∀q,|κ q|≤K) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicDyadicWeightedProcessHessianEnergy D μ a κ J j sample‖≤
      K^2*anisotropicProcessEnergyBound D J/((J.card:ℝ)/2)^2 := by
  unfold anisotropicDyadicWeightedProcessHessianEnergy
  rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply anisotropic_freeIntegral_bound μ a ha _ _ (mul_nonneg (sq_nonneg _) (anisotropicProcessEnergyBound_nonneg D J))
  intro q
  rw [norm_mul,norm_pow,Real.norm_eq_abs]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb _) 2)
    (norm_anisotropicFiniteProcessHessianEnergy_le D _ J _ sample) (norm_nonneg _) (sq_nonneg _)

theorem tendsto_anisotropicDyadicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Continuous κ)
    (J : Finset (Fin n)) (K : ℝ) (hb : ∀q,|κ q|≤K)
    (sample : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j=>anisotropicDyadicWeightedProcessHessianEnergy D μ a κ J j sample) atTop
      (𝓝 (anisotropicWeightedProcessHessianEnergy D μ a κ J sample)) := by
  apply Tendsto.div_const
  apply tendsto_integral_of_dominated_convergence (fun _=>K^2*anisotropicProcessEnergyBound D J)
  · intro j
    have hmap:=(Paper.measurable_parisiGridRound (vectorDyadicIndex j)).prodMk
      (measurable_const : Measurable (fun _ : Paper.Overlap => sample))
    have hm := (measurable_uncurry_anisotropicFiniteProcessHessianEnergy D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) J).comp hmap
    exact (((hκ.measurable.comp (Paper.measurable_parisiGridRound _)).pow_const 2).mul hm).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun q=>by
      rw [norm_mul,norm_pow,Real.norm_eq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb _) 2)
        (norm_anisotropicFiniteProcessHessianEnergy_le D _ J _ sample) (norm_nonneg _) (sq_nonneg _)
  · exact .of_forall fun q=>
      (((hκ.tendsto q).comp ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)).pow 2).mul
        (tendsto_anisotropicFiniteProcessHessianEnergy_moving_time D μ J sample
          ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex))

theorem tendsto_integral_anisotropicDyadicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ) (hκ : Continuous κ)
    (J : Finset (Fin n)) (K : ℝ) (hb : ∀q,|κ q|≤K) :
    Tendsto (fun j=>∫sample,anisotropicDyadicWeightedProcessHessianEnergy D μ a κ J j sample
      ∂anisotropicFiniteWienerSampleLaw D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a) atTop
      (𝓝 (∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a)) :=
  tendsto_integral_anisotropicDyadicTilt_bounded D μ a _ _
    (K^2*anisotropicProcessEnergyBound D J/((J.card:ℝ)/2)^2) (by
      exact div_nonneg (mul_nonneg (sq_nonneg _) (anisotropicProcessEnergyBound_nonneg D J)) (sq_nonneg _))
    (measurable_anisotropicDyadicWeightedProcessHessianEnergy D μ a κ hκ.measurable J)
    (norm_anisotropicDyadicWeightedProcessHessianEnergy_le D μ a ha κ J K hb)
    (.of_forall (tendsto_anisotropicDyadicWeightedProcessHessianEnergy D μ a κ hκ J K hb))

end QuantitativeFollowup
