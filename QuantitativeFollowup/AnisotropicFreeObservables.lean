module
public import QuantitativeFollowup.AnisotropicProcessEnergy
public import QuantitativeFollowup.AnisotropicTiltedObservableLimits
public import QuantitativeFollowup.ParisiFreeGrid

@[expose] public section

/-! Actual free-measure self-overlap and Hessian-energy observables. Their
moving-grid limits use the honest native diffusion and normalized outer tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicWeightedSelfOverlap (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫q,κ q*anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)
    ∂parisiFreeMeasure μ a

def anisotropicDyadicWeightedSelfOverlap (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫q,κ (Paper.parisiGridRound (vectorDyadicIndex j) q)*anisotropicSelectedMeanSquare J
    (anisotropicFiniteProcessMagnetization D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRound (vectorDyadicIndex j) q) sample) ∂parisiFreeMeasure μ a

def anisotropicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∫q,(κ q)^2*anisotropicProcessHessianEnergy D μ J q sample ∂parisiFreeMeasure μ a)/((J.card:ℝ)/2)^2

def anisotropicDyadicWeightedProcessHessianEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∫q,(κ (Paper.parisiGridRound (vectorDyadicIndex j) q))^2*
    anisotropicFiniteProcessHessianEnergy D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) J
      (Paper.parisiGridRound (vectorDyadicIndex j) q) sample ∂parisiFreeMeasure μ a)/((J.card:ℝ)/2)^2

theorem anisotropic_freeIntegral_bound (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (f : Paper.Overlap→ℝ) (C : ℝ) (hC : 0≤C) (hf : ∀q,‖f q‖≤C) :
    ‖∫q,f q ∂parisiFreeMeasure μ a‖≤C := by
  have h:=norm_integral_le_of_norm_le (integrable_const C : Integrable _ (parisiFreeMeasure μ a))
    (.of_forall hf)
  have he : (∫_q : Paper.Overlap,C ∂parisiFreeMeasure μ a)=(1-a)*C := by
    simp only [integral_const,Measure.real,parisiFreeMeasure_univ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2),smul_eq_mul]
  rw [he] at h
  exact h.trans (by nlinarith [mul_nonneg ha.1 hC])

theorem measurable_anisotropicWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (J : Finset (Fin n)) :
    Measurable (anisotropicWeightedSelfOverlap D μ a κ J) := by
  have hm := (hκ.comp measurable_fst).mul
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
      (measurable_uncurry_anisotropicProcessMagnetization D μ))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable

theorem measurable_anisotropicDyadicWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (J : Finset (Fin n)) (j : ℕ) : Measurable (anisotropicDyadicWeightedSelfOverlap D μ a κ J j) := by
  have hmap : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      Paper.parisiGridRound (vectorDyadicIndex j) z.1) :=
    (Paper.measurable_parisiGridRound (vectorDyadicIndex j)).comp measurable_fst
  have hm := (hκ.comp hmap).mul ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
    ((measurable_uncurry_anisotropicFiniteProcessMagnetization D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))).comp (hmap.prodMk measurable_snd)))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable

theorem norm_anisotropicWeightedSelfOverlap_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ)
    (J : Finset (Fin n)) (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K)
    (sample : AnisotropicDisorderBrownianSample n) : ‖anisotropicWeightedSelfOverlap D μ a κ J sample‖≤K := by
  apply anisotropic_freeIntegral_bound μ a ha _ K hK
  intro q
  rw [norm_mul,Real.norm_eq_abs]
  exact (mul_le_mul (hb q) (anisotropicSelectedMeanSquare_bound J _
    (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)) (norm_nonneg _) hK).trans_eq (mul_one K)

theorem norm_anisotropicDyadicWeightedSelfOverlap_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ)
    (J : Finset (Fin n)) (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) : ‖anisotropicDyadicWeightedSelfOverlap D μ a κ J j sample‖≤K := by
  apply anisotropic_freeIntegral_bound μ a ha _ K hK
  intro q
  rw [norm_mul,Real.norm_eq_abs]
  exact (mul_le_mul (hb _) (anisotropicSelectedMeanSquare_bound J _
    (fun i=>anisotropicFiniteTailMagnetization_component_bound D _ _ _ i)) (norm_nonneg _) hK).trans_eq (mul_one K)

theorem tendsto_anisotropicDyadicWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Continuous κ)
    (J : Finset (Fin n)) (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K)
    (sample : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j=>anisotropicDyadicWeightedSelfOverlap D μ a κ J j sample) atTop
      (𝓝 (anisotropicWeightedSelfOverlap D μ a κ J sample)) := by
  apply tendsto_integral_of_dominated_convergence (fun _=>K)
  · intro j
    have hmap:=(Paper.measurable_parisiGridRound (vectorDyadicIndex j)).prodMk
      (measurable_const : Measurable (fun _ : Paper.Overlap => sample))
    have hm := (continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicFiniteProcessMagnetization D
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))).comp hmap)
    exact ((hκ.measurable.comp (Paper.measurable_parisiGridRound _)).mul hm).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun q=>by
      rw [norm_mul,Real.norm_eq_abs]
      exact (mul_le_mul (hb _) (anisotropicSelectedMeanSquare_bound J _
        (fun i=>anisotropicFiniteTailMagnetization_component_bound D _ _ _ i)) (norm_nonneg _) hK).trans_eq (mul_one K)
  · exact .of_forall fun q=>
      ((hκ.tendsto q).comp ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)).mul
        ((continuous_anisotropicSelectedMeanSquare J).tendsto _ |>.comp
          (tendsto_anisotropicFiniteProcessMagnetization_moving_time D μ sample
            ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)))

theorem tendsto_variance_anisotropicDyadicWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ) (hκ : Continuous κ)
    (J : Finset (Fin n)) (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K) :
    Tendsto (fun j=>variance (anisotropicDyadicWeightedSelfOverlap D μ a κ J j)
      (anisotropicFiniteWienerSampleLaw D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a)) atTop
      (𝓝 (variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a))) :=
  tendsto_variance_anisotropicDyadicTilt_bounded D μ a _ _ K hK
    (measurable_anisotropicDyadicWeightedSelfOverlap D μ a κ hκ.measurable J)
    (measurable_anisotropicWeightedSelfOverlap D μ a κ hκ.measurable J)
    (norm_anisotropicDyadicWeightedSelfOverlap_le D μ a ha κ J K hK hb)
    (norm_anisotropicWeightedSelfOverlap_le D μ a ha κ J K hK hb)
    (.of_forall (tendsto_anisotropicDyadicWeightedSelfOverlap D μ a κ hκ J K hK hb))

end QuantitativeFollowup
