module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileResiduals
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileScalarKernels
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! The literal first two signed terms pass under the atom-preserving
finite approximation. Integrals are pulled back to the fixed genuine
free measure, including its atoms and two-variable diagonal. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 950000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private def symmMoment (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (r s p : Paper.Overlap) : ℝ :=
  ∫ω,cavitySignedResponseSymmetricMeanResidual D μ r s ω*
    cavitySignedResponseCenteredSelfOverlap D μ a p ω ∂anisotropicMeasureSampleLaw D μ a

private theorem symmMoment_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×Paper.Overlap=>symmMoment D μ a z.1 z.2 p) := by
  have hAmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n=>(p,z.2)) :=
    measurable_const.prodMk measurable_snd
  have hA := (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hAmap
  have hm := ((measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).mul hA)
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν:=anisotropicMeasureSampleLaw D μ a)
  change Measurable (fun z : Paper.Overlap×Paper.Overlap=>∫ω,
    cavitySignedResponseSymmetricMeanResidual D μ z.1 z.2 ω*
      cavitySignedResponseCenteredSelfOverlap D μ a p ω ∂anisotropicMeasureSampleLaw D μ a)
  dsimp only [Function.comp_def] at hi
  exact hi.measurable

private theorem symmMoment_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r s p : Paper.Overlap) :
    ‖symmMoment D μ a r s p‖≤4 := by
  have hb (ω : AnisotropicDisorderBrownianSample n) :
      ‖cavitySignedResponseSymmetricMeanResidual D μ r s ω*
        cavitySignedResponseCenteredSelfOverlap D μ a p ω‖≤4 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_cavitySignedResponseMeanResidual_le D μ (min r s) (max r s) ω)
      (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p ω)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  unfold symmMoment
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=anisotropicMeasureSampleLaw D μ a) (.of_forall hb)

private theorem kernel_norm (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (x : ℝ) (h : x^2≤Gamma β μ r*Gamma β μ p) : ‖x‖≤1 := by
  have hb : Gamma β μ r*Gamma β μ p≤1 :=
    (mul_le_mul (scalarGamma_le_one β μ r r.property)
      (scalarGamma_le_one β μ p p.property) (scalarGamma_nonneg β μ p) zero_le_one).trans_eq
        (one_mul (1:ℝ))
  rw [Real.norm_eq_abs]
  nlinarith [h.trans hb,sq_abs x,abs_nonneg x]

theorem tendsto_cavitySignedResponseT1_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a β : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) (hβ : β≠0)
    (p : Paper.Overlap) :
    Tendsto (fun N=>cavitySignedResponseT1 D (FRSB.preservingMeasure μ S N) a β hβ p)
      atTop (𝓝 (cavitySignedResponseT1 D μ a β hβ p)) := by
  simp only [cavitySignedResponseT1,cavitySignedResponse_original_T1_diagonal_zero,
    mul_zero,zero_sub]
  apply Tendsto.neg
  apply Tendsto.const_mul
  change Tendsto (fun N=>∫r,cavitySignedScalarKernelOne β (FRSB.preservingMeasure μ S N) r p*
    symmMoment D (FRSB.preservingMeasure μ S N) a p r p
      ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
    (𝓝 (∫r,cavitySignedScalarKernelOne β μ r p*symmMoment D μ a p r p ∂parisiFreeMeasure μ a))
  refine nativeStreaming_free_integral_tendsto μ S hzero a ha hfloor
    (fun N r=>cavitySignedScalarKernelOne β (FRSB.preservingMeasure μ S N) r p*
      symmMoment D (FRSB.preservingMeasure μ S N) a p r p)
    (fun r=>cavitySignedScalarKernelOne β μ r p*symmMoment D μ a p r p)
    ?_ 4 (by norm_num) ?_ ?_
  · intro N
    have hKmap : Measurable (fun r : Paper.Overlap=>(r,p)) := measurable_id.prodMk measurable_const
    have hRmap : Measurable (fun r : Paper.Overlap=>(p,r)) := measurable_const.prodMk measurable_id
    have hK := (continuous_cavitySignedScalarKernelOne β hβ
      (FRSB.preservingMeasure μ S N)).measurable.comp hKmap
    have hR := (symmMoment_measurable D (FRSB.preservingMeasure μ S N) a p).comp hRmap
    dsimp only [Function.comp_def] at hK hR
    exact hK.mul hR
  · intro N r
    rw [←Real.norm_eq_abs,norm_mul]
    exact (mul_le_mul (kernel_norm β _ r p _ (cavitySignedScalarKernelOne_square_le β hβ _ r p))
      (symmMoment_norm_le D _ a p r p) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro r
    have hK := ((continuous_cavitySignedScalarKernelOne_profile β hβ).tendsto (μ,(r,p))).comp
      ((FRSB.tendsto_preservingMeasure μ S).prodMk_nhds
        ((FRSB.tendsto_preservingRound S r).prodMk_nhds (tendsto_const_nhds (x:=p))))
    have hR := tendsto_cavitySignedResponseSymmetricSelfMoment_profile D
        (r:=fun _ : ℕ=>p) (p:=fun _ : ℕ=>p)
        (FRSB.tendsto_preservingMeasure μ S) a tendsto_const_nhds
        (FRSB.tendsto_preservingRound S r) tendsto_const_nhds
    dsimp only [Function.comp_def] at hK
    change Tendsto (fun N=>symmMoment D (FRSB.preservingMeasure μ S N) a p
      (FRSB.preservingRound S N r) p) atTop (𝓝 (symmMoment D μ a p r p)) at hR
    exact hK.mul hR

private theorem terminalMoment_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (fun r=>∫z,cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseSelfOverlap D μ p z.1 ∂anisotropicMeasureSpinPathLaw D μ a) := by
  have hAmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>(p,z.2.1)) :=
    measurable_const.prodMk measurable_snd.fst
  have hA := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap
  have hm := (measurable_joint_cavitySignedResponseTerminalResidual D μ).mul hA
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν:=anisotropicMeasureSpinPathLaw D μ a)
  dsimp only [Function.comp_def] at hi
  exact hi.measurable

theorem tendsto_cavitySignedResponseT2First_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a β : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) (hβ : β≠0)
    (p : Paper.Overlap) :
    Tendsto (fun N=>cavitySignedResponseT2First D (FRSB.preservingMeasure μ S N) a β hβ p)
      atTop (𝓝 (cavitySignedResponseT2First D μ a β hβ p)) := by
  simp only [cavitySignedResponseT2First]
  simp_rw [cavitySignedResponse_terminal_centered_self_pairing_eq]
  apply Tendsto.neg
  refine nativeStreaming_free_integral_tendsto μ S hzero a ha hfloor _ _ ?_ 2 (by norm_num) ?_ ?_
  · intro N
    exact ((continuous_cavitySignedScalarKernelMarked β hβ _).measurable.comp
      (measurable_id.prodMk (measurable_const (a:=p)))).mul (terminalMoment_measurable D _ a p)
  · intro N r
    have hb : ‖∫z,cavitySignedResponseTerminalResidual D (FRSB.preservingMeasure μ S N) r z*
        cavitySignedResponseSelfOverlap D (FRSB.preservingMeasure μ S N) p z.1
          ∂anisotropicMeasureSpinPathLaw D (FRSB.preservingMeasure μ S N) a‖≤2 := by
      have hz (z : AnisotropicDisorderBrownianSample n×Configuration n) :
          ‖cavitySignedResponseTerminalResidual D (FRSB.preservingMeasure μ S N) r z*
            cavitySignedResponseSelfOverlap D (FRSB.preservingMeasure μ S N) p z.1‖≤2 := by
        rw [norm_mul]
        exact (mul_le_mul (norm_cavitySignedResponseTerminalResidual_le D _ r z)
          (norm_cavitySignedResponseSelfOverlap_le D _ p z.1)
          (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
        (μ:=anisotropicMeasureSpinPathLaw D (FRSB.preservingMeasure μ S N) a) (.of_forall hz)
    rw [←Real.norm_eq_abs,norm_mul]
    exact (mul_le_mul (kernel_norm β _ r p _ (cavitySignedScalarKernelMarked_square_le β hβ _ r p))
      hb (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro r
    exact ((continuous_cavitySignedScalarKernelMarked_profile β hβ).tendsto _ |>.comp
      ((FRSB.tendsto_preservingMeasure μ S).prodMk_nhds
        ((FRSB.tendsto_preservingRound S r).prodMk_nhds tendsto_const_nhds))).mul
      (tendsto_cavitySignedResponseTerminalSelfMoment_profile D
        (FRSB.tendsto_preservingMeasure μ S) a (FRSB.tendsto_preservingRound S r) tendsto_const_nhds)

theorem tendsto_cavitySignedResponseT2Double_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a β : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) (hβ : β≠0)
    (p : Paper.Overlap) :
    Tendsto (fun N=>cavitySignedResponseT2Double D (FRSB.preservingMeasure μ S N) a β p)
      atTop (𝓝 (cavitySignedResponseT2Double D μ a β p)) := by
  simp only [cavitySignedResponseT2Double]
  apply Tendsto.const_mul
  refine nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hfloor _ _ ?_ 4 (by norm_num) ?_ ?_
  · intro N
    exact ((continuous_cavitySignedScalarKernelTriple β hβ _).measurable.comp
      (measurable_id.prodMk measurable_const)).mul (symmMoment_measurable D _ a p)
  · intro N rl
    rw [←Real.norm_eq_abs,norm_mul]
    exact (mul_le_mul (kernel_norm β _ (min rl.1 rl.2) p _
      (cavitySignedScalarKernelTriple_square_le β _ rl.1 rl.2 p))
      (symmMoment_norm_le D _ a rl.1 rl.2 p) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro r s
    exact ((continuous_cavitySignedScalarKernelTriple_profile β hβ).tendsto _ |>.comp
      ((FRSB.tendsto_preservingMeasure μ S).prodMk_nhds
        (((FRSB.tendsto_preservingRound S r).prodMk_nhds
          (FRSB.tendsto_preservingRound S s)).prodMk_nhds tendsto_const_nhds))).mul
      (tendsto_cavitySignedResponseSymmetricSelfMoment_profile D
        (FRSB.tendsto_preservingMeasure μ S) a (FRSB.tendsto_preservingRound S r)
        (FRSB.tendsto_preservingRound S s) tendsto_const_nhds)

end QuantitativeFollowup
