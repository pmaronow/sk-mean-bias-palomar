module
public import FourPapersCommon.IntegrableBoundedFamilies
public import QuantitativeFollowup.FollowupCavitySignedResponseT2Original
public import QuantitativeFollowup.FollowupCavitySignedResponseT3LastHessian
public import QuantitativeFollowup.FollowupCavitySignedResponseT3ScoreFubini
public import QuantitativeFollowup.FollowupCavitySignedResponseDiagonalIntegral

@[expose] public section

/-! Genuine free-measure integrability of the original native response
terms. Every bound here is derived from the actual spin and scalar laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

private theorem kernel_norm (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (x : ℝ) (hx : x^2≤Gamma β0 μ r*Gamma β0 μ p) : ‖x‖≤1 := by
  have hp : Gamma β0 μ r*Gamma β0 μ p≤1 :=
    (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ p p.property)
      (scalarGamma_nonneg β0 μ p) zero_le_one).trans_eq (one_mul (1:ℝ))
  have hs := hx.trans hp
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs x,abs_nonneg x]

theorem integrable_cavitySignedResponseT1 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT1 D μ a β0 hβ0) (parisiFreeMeasure μ a) := by
  let F := fun (p r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n)=>
    cavitySignedScalarKernelOne β0 μ r p*
      (cavitySignedResponseSymmetricMeanResidual D μ p r sample*
        cavitySignedResponseCenteredSelfOverlap D μ a p sample)
  have hKmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n=>
      (z.1.2,z.1.1)) := measurable_fst.snd.prodMk measurable_fst.fst
  have hRmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n=>
      ((z.1.1,z.1.2),z.2)) := measurable_fst.prodMk measurable_snd
  have hAmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n=>
      (z.1.1,z.2)) := measurable_fst.fst.prodMk measurable_snd
  have hF := ((continuous_cavitySignedScalarKernelOne β0 hβ0 μ).measurable.comp hKmap).mul
    (((measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).comp hRmap).mul
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hAmap))
  dsimp only [Function.comp_def] at hF
  have hb (p r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ‖F p r sample‖≤4 := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (kernel_norm β0 μ r p _ (cavitySignedScalarKernelOne_square_le β0 hβ0 μ r p))
      (mul_le_mul (norm_cavitySignedResponseMeanResidual_le D μ (min p r) (max p r) sample)
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p sample) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
  have hi := integrable_bounded_double_integral_family (parisiFreeMeasure μ a) (parisiFreeMeasure μ a)
    (anisotropicMeasureSampleLaw D μ a) F hF 4 hb
  apply (hi.const_mul (-2)).congr
  exact .of_forall fun p=>by
    dsimp only [F]
    simp only [integral_const_mul,cavitySignedResponseT1,cavitySignedResponse_original_T1_diagonal_zero,
      mul_zero,zero_sub]
    ring

theorem integrable_cavitySignedResponseT2First (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT2First D μ a β0 hβ0) (parisiFreeMeasure μ a) := by
  let F := fun (p r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavitySignedScalarKernelMarked β0 hβ0 μ r p*
      (cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
  have hKmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>(z.1.2,z.1.1)) :=
    measurable_fst.snd.prodMk measurable_fst.fst
  have hRmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>(z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hAmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>(z.1.1,z.2.1)) :=
    measurable_fst.fst.prodMk measurable_snd.fst
  have hF := ((continuous_cavitySignedScalarKernelMarked β0 hβ0 μ).measurable.comp hKmap).mul
    (((measurable_joint_cavitySignedResponseTerminalResidual D μ).comp hRmap).mul
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hAmap))
  dsimp only [Function.comp_def] at hF
  have hb (p r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n) : ‖F p r z‖≤4 := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (kernel_norm β0 μ r p _ (cavitySignedScalarKernelMarked_square_le β0 hβ0 μ r p))
      (mul_le_mul (norm_cavitySignedResponseTerminalResidual_le D μ r z)
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
  have hi := integrable_bounded_double_integral_family (parisiFreeMeasure μ a) (parisiFreeMeasure μ a)
    (anisotropicMeasureSpinPathLaw D μ a) F hF 4 hb
  apply hi.neg.congr
  exact .of_forall fun p=>by
    dsimp only [F]
    simp only [integral_const_mul,cavitySignedResponseT2First]
    rfl

theorem integrable_cavitySignedResponseT2Double (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT2Double D μ a β0) (parisiFreeMeasure μ a) := by
  let F := fun (p : Paper.Overlap) (rl : Paper.Overlap×Paper.Overlap)
      (sample : AnisotropicDisorderBrownianSample n)=>
    cavitySignedScalarKernelTriple β0 μ rl p*
      (cavitySignedResponseSymmetricMeanResidual D μ rl.1 rl.2 sample*
        cavitySignedResponseCenteredSelfOverlap D μ a p sample)
  have hKmap : Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×AnisotropicDisorderBrownianSample n=>
      (z.1.2,z.1.1)) := measurable_fst.snd.prodMk measurable_fst.fst
  have hRmap : Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×AnisotropicDisorderBrownianSample n=>
      (z.1.2,z.2)) := measurable_fst.snd.prodMk measurable_snd
  have hAmap : Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×AnisotropicDisorderBrownianSample n=>
      (z.1.1,z.2)) := measurable_fst.fst.prodMk measurable_snd
  have hF := ((continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).measurable.comp hKmap).mul
    (((measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).comp hRmap).mul
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hAmap))
  dsimp only [Function.comp_def] at hF
  have hb (p : Paper.Overlap) (rl : Paper.Overlap×Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ‖F p rl sample‖≤4 := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (kernel_norm β0 μ (min rl.1 rl.2) p _ (cavitySignedScalarKernelTriple_square_le β0 μ rl.1 rl.2 p))
      (mul_le_mul (norm_cavitySignedResponseMeanResidual_le D μ (min rl.1 rl.2) (max rl.1 rl.2) sample)
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p sample) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
  have hi := integrable_bounded_double_integral_family (parisiFreeMeasure μ a)
    ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) (anisotropicMeasureSampleLaw D μ a) F hF 4 hb
  apply (hi.const_mul (1/2)).congr
  exact .of_forall fun p=>by
    dsimp only [F]
    simp only [integral_const_mul,cavitySignedResponseT2Double]

end QuantitativeFollowup
