module
public import QuantitativeFollowup.AnisotropicFreeObservables
public import QuantitativeFollowup.AnisotropicFiniteDiffusionVariance

@[expose] public section

/-! The genuine free-measure integrals at finite profiles are exactly the
posterior history observables of the actual native anisotropic diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropicFiniteProcessHessianEnergy_node (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n) (i : ℕ) (hi : i≤k+2) :
    anisotropicFiniteProcessHessianEnergy D s J (anisotropicSchemeNode s i hi) sample=
      anisotropicHistoryHessianEnergy D s J i (anisotropicFiniteWienerHistory D s (k+2) sample) := by
  unfold anisotropicFiniteProcessHessianEnergy
  rw [anisotropicFiniteProcessMagnetization_node,anisotropicFiniteTailPotential_node]
  rw [anisotropicHistoryHessianEnergy,anisotropicFieldHessian_quadratic_eq_parameter,
    anisotropicFiniteWienerHistory_node D s sample i hi]
  rfl

theorem anisotropicHistoryWeightedSelfOverlap_eq_freeIntegral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha0 : 0≤a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicHistoryWeightedSelfOverlap D s a (fun q=>κ (projIcc 0 1 zero_le_one q)) J
      (anisotropicFiniteWienerHistory D s (k+2) sample)=
      ∫q,κ q*anisotropicSelectedMeanSquare J (anisotropicFiniteProcessMagnetization D s q sample)
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha0 ha hq,integral_vectorProfileFreeMeasure s a ha]
  unfold anisotropicHistoryWeightedSelfOverlap
  apply Finset.sum_congr rfl
  intro i _
  have hi : anisotropicPosteriorFeatureTime i≤k+2 := by
    cases i <;> dsimp [anisotropicPosteriorFeatureTime] <;> omega
  have hatom : vectorProfileAtom s i=anisotropicSchemeNode s (anisotropicPosteriorFeatureTime i) hi := rfl
  rw [hatom,anisotropicFiniteProcessMagnetization_node]
  simp only [anisotropicPosteriorFeatureKernel,projIcc_of_mem zero_le_one
    ⟨s.q_nonneg hi,s.q_le_one hi⟩]
  exact mul_assoc _ _ _

theorem anisotropicHistoryWeightedHessianEnergy_eq_freeIntegral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha0 : 0≤a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicHistoryWeightedHessianEnergy D s a (fun q=>κ (projIcc 0 1 zero_le_one q)) J
      (anisotropicFiniteWienerHistory D s (k+2) sample)=
      (∫q,(κ q)^2*anisotropicFiniteProcessHessianEnergy D s J q sample
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)/((J.card:ℝ)/2)^2 := by
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha0 ha hq,integral_vectorProfileFreeMeasure s a ha]
  unfold anisotropicHistoryWeightedHessianEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : anisotropicPosteriorFeatureTime i≤k+2 := by
    cases i <;> dsimp [anisotropicPosteriorFeatureTime] <;> omega
  have hatom : vectorProfileAtom s i=anisotropicSchemeNode s (anisotropicPosteriorFeatureTime i) hi := rfl
  rw [hatom,anisotropicFiniteProcessHessianEnergy_node]
  simp only [anisotropicPosteriorFeatureKernel,projIcc_of_mem zero_le_one
    ⟨s.q_nonneg hi,s.q_le_one hi⟩]
  exact mul_assoc _ _ _

theorem anisotropicDyadicWeightedSelfOverlap_eq_history (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (J : Finset (Fin n)) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicDyadicWeightedSelfOverlap D μ a κ J j sample=
      anisotropicHistoryWeightedSelfOverlap D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a
        (fun q=>κ (projIcc 0 1 zero_le_one q)) J
        (anisotropicFiniteWienerHistory D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
          (vectorDyadicIndex j+3) sample) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hs : a ≤ s.m 1:=parisiGridRSBScheme_floor μ a hμ _
  have hq : s.q 1=0:=Paper.parisiGridSchemeOverlap_one _
  rw [anisotropicHistoryWeightedSelfOverlap_eq_freeIntegral D s a ha.1 hs hq,
    FRSB.parisiSchemeMeasure_grid_eq]
  have hm := hκ.mul ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
    ((measurable_uncurry_anisotropicFiniteProcessMagnetization D s).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : Paper.Overlap=>sample)))))
  have hm' : Measurable (fun q : Paper.Overlap=>κ q*anisotropicSelectedMeanSquare J
      (anisotropicFiniteProcessMagnetization D s q sample)) := by
    convert hm using 1
    funext q
    rfl
  rw [integral_parisiFreeMeasure_grid μ a ha hμ (vectorDyadicIndex j) _ hm']
  rfl

theorem anisotropicDyadicWeightedHessianEnergy_eq_history (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (J : Finset (Fin n)) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicDyadicWeightedProcessHessianEnergy D μ a κ J j sample=
      anisotropicHistoryWeightedHessianEnergy D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a
        (fun q=>κ (projIcc 0 1 zero_le_one q)) J
        (anisotropicFiniteWienerHistory D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
          (vectorDyadicIndex j+3) sample) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hs : a ≤ s.m 1:=parisiGridRSBScheme_floor μ a hμ _
  have hq : s.q 1=0:=Paper.parisiGridSchemeOverlap_one _
  rw [anisotropicHistoryWeightedHessianEnergy_eq_freeIntegral D s a ha.1 hs hq,
    FRSB.parisiSchemeMeasure_grid_eq]
  have hm := (hκ.pow_const 2).mul
    ((measurable_uncurry_anisotropicFiniteProcessHessianEnergy D s J).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : Paper.Overlap=>sample))))
  have hm' : Measurable (fun q : Paper.Overlap=>(κ q)^2*
      anisotropicFiniteProcessHessianEnergy D s J q sample) := by
    convert hm using 1
    funext q
    rfl
  rw [integral_parisiFreeMeasure_grid μ a ha hμ (vectorDyadicIndex j) _ hm']
  rfl

end QuantitativeFollowup
