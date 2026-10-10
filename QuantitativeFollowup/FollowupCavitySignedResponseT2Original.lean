module
public import QuantitativeFollowup.FollowupCavitySignedResponseT1Fubini
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarDoubleKernels

@[expose] public section

/-! Both original T2 terms under the actual rest law, with their bounded
Fubini/centering transport to the proved signed residual estimates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

private theorem scalar_kernel_norm_le_one (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (x : ℝ) (hs : x^2≤Gamma β0 μ r*Gamma β0 μ p) : ‖x‖≤1 := by
  have hprod : Gamma β0 μ r*Gamma β0 μ p≤1 :=
    (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ p p.property)
      (scalarGamma_nonneg β0 μ p) zero_le_one).trans_eq (one_mul (1:ℝ))
  have h := hs.trans hprod
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs x,abs_nonneg x]

def cavitySignedResponseT2First (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (hβ0 : β0≠0) (p : Paper.Overlap) : ℝ :=
  -(∫r,cavitySignedScalarKernelMarked β0 hβ0 μ r p*
    (∫z,cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)
    ∂parisiFreeMeasure μ a)

theorem cavitySignedResponse_T2_first_original_eq_terminal_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    (∫p,cavitySignedResponseT2First D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)=
    -(∫r,∫z,cavitySignedResponseTerminalResidual D μ r z*
      anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelMarked β0 hβ0 μ r)
        Finset.univ z.1 ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a) := by
  simp only [cavitySignedResponseT2First]
  simp_rw [cavitySignedResponse_terminal_centered_self_pairing_eq]
  rw [integral_neg,cavitySignedResponse_terminal_kernel_average_fubini D μ a _
    (continuous_cavitySignedScalarKernelMarked β0 hβ0 μ).measurable
    (fun r p=>scalar_kernel_norm_le_one β0 μ r p _
      (cavitySignedScalarKernelMarked_square_le β0 hβ0 μ r p))]

theorem cavitySignedResponse_T2_first_original_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫p,cavitySignedResponseT2First D μ a β0 hβ0 p ∂parisiFreeMeasure μ a|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  rw [cavitySignedResponse_T2_first_original_eq_terminal_integral,abs_neg]
  exact cavitySignedResponse_T2_terminal_integral_bound D μ a β0 hβ0 ha hμ hn

theorem cavitySignedResponse_symmetric_centered_self_pairing_eq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l p : Paper.Overlap) :
    (∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
        cavitySignedResponseSelfOverlap D μ p sample ∂anisotropicMeasureSampleLaw D μ a := by
  let Y := cavitySignedResponseSymmetricMeanResidual D μ r l
  have hYmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>((r,l),sample)) :=
    measurable_const.prodMk measurable_id
  have hYm := (measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).comp hYmap
  dsimp only [Function.comp_def] at hYm
  have hYb (sample) : ‖Y sample‖≤2 :=
    norm_cavitySignedResponseMeanResidual_le D μ (min r l) (max r l) sample
  have hy : Integrable Y (anisotropicMeasureSampleLaw D μ a) :=
    bounded_real_integrable _ hYm 2 hYb
  have hAmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(p,sample)) :=
    measurable_const.prodMk measurable_id
  have hAm := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap
  dsimp only [Function.comp_def] at hAm
  have hi : Integrable (fun sample=>Y sample*cavitySignedResponseSelfOverlap D μ p sample)
      (anisotropicMeasureSampleLaw D μ a) := by
    apply bounded_real_integrable _ (hYm.mul hAm) 2
    intro sample
    change ‖Y sample*cavitySignedResponseSelfOverlap D μ p sample‖≤2
    rw [norm_mul]
    exact (mul_le_mul (hYb sample) (norm_cavitySignedResponseSelfOverlap_le D μ p sample)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hzero : (∫sample,Y sample ∂anisotropicMeasureSampleLaw D μ a)=0 :=
    cavitySignedResponseMeanResidual_centered D μ a (min r l) (max r l) min_le_max
  change (∫sample,Y sample*(cavitySignedResponseSelfOverlap D μ p sample-_) ∂anisotropicMeasureSampleLaw D μ a)=_
  simp_rw [mul_sub]
  rw [integral_sub hi (hy.mul_const _),integral_mul_const,hzero,zero_mul,sub_zero]

def cavitySignedResponseT2Double (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  (1/2:ℝ)*(∫rl : Paper.Overlap×Paper.Overlap,cavitySignedScalarKernelTriple β0 μ rl p*
    (∫sample,cavitySignedResponseSymmetricMeanResidual D μ rl.1 rl.2 sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a)
    ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))

theorem cavitySignedResponse_T2_double_original_eq_mean_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    (∫p,cavitySignedResponseT2Double D μ a β0 p ∂parisiFreeMeasure μ a)=
      (1/2:ℝ)*(∫r,∫l,∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
        anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelTriple β0 μ (r,l))
          Finset.univ sample ∂anisotropicMeasureSampleLaw D μ a ∂parisiFreeMeasure μ a
          ∂parisiFreeMeasure μ a) := by
  let ν := parisiFreeMeasure μ a
  let P := anisotropicMeasureSampleLaw D μ a
  let K := cavitySignedScalarKernelTriple β0 μ
  let R := fun rl : Paper.Overlap×Paper.Overlap=>cavitySignedResponseSymmetricMeanResidual D μ rl.1 rl.2
  have hK := (continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).measurable
  have hKb (rl : Paper.Overlap×Paper.Overlap) (p : Paper.Overlap) : ‖K rl p‖≤1 :=
    scalar_kernel_norm_le_one β0 μ (min rl.1 rl.2) p _
      (cavitySignedScalarKernelTriple_square_le β0 μ rl.1 rl.2 p)
  have hR := measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ
  have hRb (rl : Paper.Overlap×Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
      ‖R rl sample‖≤2 := norm_cavitySignedResponseMeanResidual_le D μ (min rl.1 rl.2) (max rl.1 rl.2) sample
  have hA := measurable_joint_cavitySignedResponseSelfOverlap D μ
  have h := bounded_kernel_average_fubini (ν.prod ν) ν P K R (cavitySignedResponseSelfOverlap D μ)
    hK hR hA 1 2 1 hKb hRb (norm_cavitySignedResponseSelfOverlap_le D μ)
    (by norm_num) (by norm_num) (by norm_num)
  let Q := fun rl : Paper.Overlap×Paper.Overlap=>∫sample,R rl sample*
    anisotropicWeightedSelfOverlap D μ a (K rl) Finset.univ sample ∂P
  have hQm : Measurable Q :=
    ((hR.mul (measurable_joint_anisotropicWeightedSelfOverlap_two D μ a Finset.univ K hK)).stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have hQi : Integrable Q (ν.prod ν) := by
    apply (integrable_const 2).mono' hQm.aestronglyMeasurable
    exact .of_forall fun rl=>by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
        norm_integral_le_of_norm_le (integrable_const (μ:=P) (2:ℝ)) (.of_forall fun sample=>by
          change ‖R rl sample*anisotropicWeightedSelfOverlap D μ a (K rl) Finset.univ sample‖≤2
          rw [norm_mul]
          exact (mul_le_mul (hRb rl sample)
            (norm_anisotropicWeightedSelfOverlap_le D μ a ha (K rl) Finset.univ 1 zero_le_one
              (fun p=>by simpa only [Real.norm_eq_abs] using hKb rl p) sample)
            (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  change (∫p,(1/2:ℝ)*(∫rl,K rl p*(∫sample,R rl sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂P) ∂ν.prod ν) ∂ν)=_
  have hc (rl : Paper.Overlap×Paper.Overlap) (p : Paper.Overlap) :
      (∫sample,R rl sample*cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂P)=
      ∫sample,R rl sample*cavitySignedResponseSelfOverlap D μ p sample ∂P :=
    cavitySignedResponse_symmetric_centered_self_pairing_eq D μ a rl.1 rl.2 p
  simp_rw [hc]
  rw [integral_const_mul]
  change (1/2:ℝ)*(∫p,∫rl,K rl p*(∫sample,R rl sample*cavitySignedResponseSelfOverlap D μ p sample ∂P)
    ∂ν.prod ν ∂ν)=_
  rw [h]
  change (1/2:ℝ)*(∫rl,Q rl ∂ν.prod ν)=_
  rw [integral_prod _ hQi]

theorem cavitySignedResponse_T2_double_original_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫p,cavitySignedResponseT2Double D μ a β0 p ∂parisiFreeMeasure μ a|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  rw [cavitySignedResponse_T2_double_original_eq_mean_integral D μ a β0 hβ0 ha]
  exact cavitySignedResponse_T2_double_integral_bound D μ a β0 hβ0 ha hμ hn

end QuantitativeFollowup
