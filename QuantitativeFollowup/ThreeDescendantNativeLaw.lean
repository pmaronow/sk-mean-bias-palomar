module
public import QuantitativeFollowup.ThreeDescendantKernelMoments
public import QuantitativeFollowup.FollowupCavitySignedResponseTraceMoments

@[expose] public section

/-! Three genuine independent terminal continuations of the full native past.
The difference-square moment is identified with actual posterior pair moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

abbrev CavityThreeTerminalSpins (n : ℕ) :=
  (Configuration n×Configuration n)×Configuration n

def cavityThreeDescendantLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) :
    Measure ((AnisotropicDisorderBrownianSample n×Configuration n)×CavityThreeTerminalSpins n) :=
  (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
    (((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ (anisotropicFreshTerminalSpinKernel D μ a q)) ×ₖ
      (anisotropicFreshTerminalSpinKernel D μ a q))

instance cavityThreeDescendantLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    IsProbabilityMeasure (cavityThreeDescendantLaw D μ a q) := by
  unfold cavityThreeDescendantLaw
  infer_instance

theorem cavityThreeDescendantLaw_difference_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (J : Finset (Fin n)) :
    (∫z,(cavitySpinDifferencePairing J z.2)^2 ∂cavityThreeDescendantLaw D μ a q)=
      2*(∫sample,∑i∈J,∑j∈J,anisotropicProcessSpinCovariance D μ q sample i j*
        anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample
        ∂anisotropicMeasureSampleLaw D μ a) := by
  let F := fun z : CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing J z)^2
  let B : ℝ := ∑z : CavityThreeTerminalSpins n,‖F z‖
  have hFB (z : CavityThreeTerminalSpins n) : ‖F z‖≤B :=
    Finset.single_le_sum (fun x _=>norm_nonneg (F x)) (Finset.mem_univ z)
  have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
      CavityThreeTerminalSpins n=>F z.2) (cavityThreeDescendantLaw D μ a q) :=
    bounded_real_integrable _ ((measurable_of_finite F).comp measurable_snd) B (fun z=>hFB z.2)
  change (∫z,F z.2 ∂cavityThreeDescendantLaw D μ a q)=_
  rw [cavityThreeDescendantLaw,Measure.integral_compProd hi]
  simp only [Kernel.prod_apply]
  simp_rw [show F=fun z : CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing J z)^2 from rfl,
    cavitySpinKernel_three_difference_square]
  have hM (i : Fin n) :=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q
      (fun σ=>Paper.spinSign (σ i))).symm.trans (anisotropicMeasureSpinPathLaw_spin_condExp D μ a q i)
  have hQ (i j : Fin n) :=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q
      (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))).symm.trans
        (anisotropicMeasureSpinPathLaw_orderedPair_condExp D μ a q i j)
  have he : (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      2*(∑i∈J,∑j∈J,cavitySpinKernelCovariance (anisotropicFreshTerminalSpinKernel D μ a q p) i j*
        cavitySpinKernelSecond (anisotropicFreshTerminalSpinKernel D μ a q p) i j))=ᵐ[
      anisotropicMeasureSpinPathLaw D μ a]
      fun p=>2*(∑i∈J,∑j∈J,anisotropicProcessSpinCovariance D μ q p.1 i j*
        anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) p.1) := by
    filter_upwards [ae_all_iff.2 hM,ae_all_iff.2 (fun i=>ae_all_iff.2 (hQ i))] with p hp hpp
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold cavitySpinKernelCovariance cavitySpinKernelSecond cavitySpinKernelMean
    rw [hpp i j,hp i,hp j]
    rfl
  rw [integral_congr_ae he,integral_const_mul]
  congr 1
  have hC (i j : Fin n) : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      anisotropicProcessSpinCovariance D μ q sample i j) := by
    have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(q,sample)) :=
      measurable_const.prodMk measurable_id
    have h := (measurable_uncurry_cavityCovarianceEntry D μ i j).comp hmap
    dsimp only [Function.comp_def] at h
    exact h
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    (Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (hC i j).mul (measurable_anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j)))

end QuantitativeFollowup
