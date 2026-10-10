module
public import QuantitativeFollowup.FollowupCavityRootNormalizerFreshMarks
public import FourPapersCommon.BoundedAffineConditionalVariance
public import QuantitativeFollowup.AnisotropicCovarianceMoments

@[expose] public section

/-! Four genuine independent terminal draws given the entire native past.
The centered two-overlap product is exactly the squared deviation of the
rest self-overlap. No contact condition is imposed on the rest system. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

abbrev CavityFourTerminalSpins (n : ℕ) :=
  (Configuration n×Configuration n)×(Configuration n×Configuration n)

def cavitySelectedSpinOverlap (J : Finset (Fin n)) (σ τ : Configuration n) : ℝ :=
  (∑i∈J,Paper.spinSign (σ i)*Paper.spinSign (τ i))/(J.card:ℝ)

def cavityFourDescendantLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) :
    Measure ((AnisotropicDisorderBrownianSample n×Configuration n)×CavityFourTerminalSpins n) :=
  (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
    (((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ (anisotropicFreshTerminalSpinKernel D μ a q)) ×ₖ
      ((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ (anisotropicFreshTerminalSpinKernel D μ a q)))

instance cavityFourDescendantLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    IsProbabilityMeasure (cavityFourDescendantLaw D μ a q) := by
  unfold cavityFourDescendantLaw
  infer_instance

theorem integral_cavitySelectedSpinOverlap_product (J : Finset (Fin n))
    (K : Measure (Configuration n)) [IsProbabilityMeasure K] :
    (∫z : Configuration n×Configuration n,cavitySelectedSpinOverlap J z.1 z.2 ∂K.prod K) =
      (∑i∈J,(∫σ,Paper.spinSign (σ i) ∂K)^2)/(J.card:ℝ) := by
  unfold cavitySelectedSpinOverlap
  rw [integral_div,integral_finset_sum _ (fun i _ =>
    (integrable_configuration_function K (fun σ => Paper.spinSign (σ i))).mul_prod
      (integrable_configuration_function K (fun σ => Paper.spinSign (σ i))))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two]
  exact integral_prod_mul (f := fun σ : Configuration n => Paper.spinSign (σ i))
    (g := fun σ : Configuration n => Paper.spinSign (σ i))

theorem cavityFourDescendantLaw_centered_overlap_product (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (J : Finset (Fin n)) :
    (∫z,(cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ)) ∂cavityFourDescendantLaw D μ a q) =
      ∫sample,(anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)-(q:ℝ))^2
        ∂anisotropicMeasureSampleLaw D μ a := by
  let F := fun z : CavityFourTerminalSpins n =>
    (cavitySelectedSpinOverlap J z.1.1 z.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.1 z.2.2-(q:ℝ))
  let B : ℝ := ∑z : CavityFourTerminalSpins n,‖F z‖
  have hFB (z : CavityFourTerminalSpins n) : ‖F z‖ ≤ B :=
    Finset.single_le_sum (fun x _ => norm_nonneg (F x)) (Finset.mem_univ z)
  have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
      CavityFourTerminalSpins n => F z.2) (cavityFourDescendantLaw D μ a q) :=
    bounded_real_integrable _ ((measurable_of_finite F).comp measurable_snd) B
      (fun z => hFB z.2)
  change (∫z,F z.2 ∂cavityFourDescendantLaw D μ a q)=_
  rw [cavityFourDescendantLaw,Measure.integral_compProd hi]
  have he (p : AnisotropicDisorderBrownianSample n×Configuration n) :
      (∫z,F z ∂(((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ
        (anisotropicFreshTerminalSpinKernel D μ a q)) ×ₖ
        ((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ
          (anisotropicFreshTerminalSpinKernel D μ a q))) p) =
      ((∑i∈J,(∫σ,Paper.spinSign (σ i) ∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)/
        (J.card:ℝ)-(q:ℝ))^2 := by
    simp only [Kernel.prod_apply]
    change (∫z,(cavitySelectedSpinOverlap J z.1.1 z.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.1 z.2.2-(q:ℝ))
        ∂((anisotropicFreshTerminalSpinKernel D μ a q p).prod
          (anisotropicFreshTerminalSpinKernel D μ a q p)).prod
          ((anisotropicFreshTerminalSpinKernel D μ a q p).prod
            (anisotropicFreshTerminalSpinKernel D μ a q p))) = _
    rw [integral_prod_mul (f := fun z : Configuration n×Configuration n =>
      cavitySelectedSpinOverlap J z.1 z.2-(q:ℝ))
      (g := fun z : Configuration n×Configuration n =>
        cavitySelectedSpinOverlap J z.1 z.2-(q:ℝ))]
    have hr : Integrable (fun z : Configuration n×Configuration n => cavitySelectedSpinOverlap J z.1 z.2)
        ((anisotropicFreshTerminalSpinKernel D μ a q p).prod
          (anisotropicFreshTerminalSpinKernel D μ a q p)) := by
      apply bounded_real_integrable _ (measurable_of_finite _) (∑z : Configuration n×Configuration n,
        ‖cavitySelectedSpinOverlap J z.1 z.2‖)
      intro z
      exact Finset.single_le_sum (fun x _ => norm_nonneg (cavitySelectedSpinOverlap J x.1 x.2))
        (Finset.mem_univ z)
    rw [integral_sub hr (integrable_const _),integral_const,probReal_univ,one_smul,
      integral_cavitySelectedSpinOverlap_product]
    exact (pow_two _).symm
  simp_rw [he]
  have hk (i : Fin n) :=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q (fun σ => Paper.spinSign (σ i))).symm.trans
      (anisotropicMeasureSpinPathLaw_spin_condExp D μ a q i)
  have hs : (fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
      ((∑i∈J,(∫σ,Paper.spinSign (σ i) ∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)/
        (J.card:ℝ)-(q:ℝ))^2) =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p => (anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q p.1)-(q:ℝ))^2 := by
    filter_upwards [ae_all_iff.2 hk] with p hp
    simp only [anisotropicSelectedMeanSquare]
    congr 3
    exact Finset.sum_congr rfl fun i _ => congrArg (fun x : ℝ => x^2) (hp i)
  rw [integral_congr_ae hs]
  have hA : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)) := by
    have hm := (continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp
        ((measurable_const (a:=q)).prodMk measurable_id))
    simpa only [Function.comp_def,id_eq] using hm
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _ ((hA.sub measurable_const).pow_const 2)

end QuantitativeFollowup
