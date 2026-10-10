module
public import FourPapersCommon.BoundedKernelAverageFubini
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarKernels

@[expose] public section

/-! The original native T1 term, its actual whole-past reduction, and
the genuine bounded product-measure Fubini identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponse_terminal_kernel_average_fubini
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (K : Paper.Overlap→Paper.Overlap→ℝ) (hK : Measurable (Function.uncurry K))
    (hb : ∀r p,‖K r p‖≤1) :
    (∫p,∫r,K r p*(∫z,cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseSelfOverlap D μ p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
    ∫r,∫z,cavitySignedResponseTerminalResidual D μ r z*
      anisotropicWeightedSelfOverlap D μ a (K r) Finset.univ z.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a := by
  have hx := measurable_joint_cavitySignedResponseTerminalResidual D μ
  have hmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hA := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hmap
  dsimp only [Function.comp_def] at hA
  have hh := bounded_kernel_average_fubini (parisiFreeMeasure μ a) (parisiFreeMeasure μ a)
    (anisotropicMeasureSpinPathLaw D μ a) K (cavitySignedResponseTerminalResidual D μ)
    (fun p z=>cavitySignedResponseSelfOverlap D μ p z.1) hK hx hA 1 2 1 hb
    (norm_cavitySignedResponseTerminalResidual_le D μ)
    (fun p z=>norm_cavitySignedResponseSelfOverlap_le D μ p z.1)
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [anisotropicWeightedSelfOverlap,cavitySignedResponseSelfOverlap] using hh

def cavitySignedResponseT1 (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (hβ0 : β0≠0) (p : Paper.Overlap) : ℝ :=
  2*(∫z,M β0 μ p z.1*C β0 μ p z.1*Paper.spinSign z.2 ∂scalarMarkedSpinLaw β0 hβ0 μ)*
    (∫z,cavitySignedResponseTerminalResidual D μ p z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)-
  2*(∫r,cavitySignedScalarKernelOne β0 μ r p*
    (∫sample,cavitySignedResponseSymmetricMeanResidual D μ p r sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a)
    ∂parisiFreeMeasure μ a)

theorem cavitySignedResponse_T1_original_eq_terminal_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    (∫p,cavitySignedResponseT1 D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)=
      (-2:ℝ)*(∫r,∫z,cavitySignedResponseTerminalResidual D μ r z*
        anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelOneFuture β0 μ r)
          Finset.univ z.1 ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a) := by
  have hb (r p : Paper.Overlap) : ‖cavitySignedScalarKernelOneFuture β0 μ r p‖≤1 := by
    have hprod : Gamma β0 μ r*Gamma β0 μ p≤1 :=
      (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ p p.property)
        (scalarGamma_nonneg β0 μ p) zero_le_one).trans_eq (one_mul (1:ℝ))
    have hs := (cavitySignedScalarKernelOneFuture_square_le β0 hβ0 μ r p).trans hprod
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (cavitySignedScalarKernelOneFuture β0 μ r p),
      abs_nonneg (cavitySignedScalarKernelOneFuture β0 μ r p)]
  have hp (p : Paper.Overlap) : cavitySignedResponseT1 D μ a β0 hβ0 p=
      (-2:ℝ)*(∫r,cavitySignedScalarKernelOneFuture β0 μ r p*
        (∫z,cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseSelfOverlap D μ p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a) := by
    simp only [cavitySignedResponseT1,cavitySignedResponse_original_T1_diagonal_zero,mul_zero,zero_sub]
    have he : (∫r,cavitySignedScalarKernelOne β0 μ r p*
        (∫sample,cavitySignedResponseSymmetricMeanResidual D μ p r sample*
          cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a)
          ∂parisiFreeMeasure μ a)=
      ∫r,cavitySignedScalarKernelOneFuture β0 μ r p*
        (∫z,cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseSelfOverlap D μ p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a := by
      apply integral_congr_ae
      exact .of_forall fun r=>by
        dsimp only
        rw [cavitySignedResponse_original_T1_two_time_pairing]
        by_cases hrp : r<p <;> simp [cavitySignedScalarKernelOneFuture,hrp]
    rw [he]
    ring
  simp_rw [hp]
  rw [integral_const_mul,cavitySignedResponse_terminal_kernel_average_fubini D μ a _
    (measurable_cavitySignedScalarKernelOneFuture β0 hβ0 μ) hb]

theorem cavitySignedResponse_T1_original_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫p,cavitySignedResponseT1 D μ a β0 hβ0 p ∂parisiFreeMeasure μ a|≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  rw [cavitySignedResponse_T1_original_eq_terminal_integral]
  exact cavitySignedResponse_T1_terminal_integral_bound D μ a β0 hβ0 ha hμ hn

end QuantitativeFollowup
