module
public import QuantitativeFollowup.FollowupCavitySignedResponseIntegratedPairing

@[expose] public section

/-! The literal symmetric two-time residual and its integrated pairing.
The minimum-time variance controls the double integral under the actual
free measure, including atoms and repeated observation times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def cavitySignedResponseSymmetricMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  cavitySignedResponseMeanResidual D μ (min r l) (max r l) sample

theorem measurable_joint_cavitySignedResponseSymmetricMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseSymmetricMeanResidual D μ z.1.1 z.1.2 z.2) := by
  have hm : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n =>
      (min z.1.1 z.1.2,(max z.1.1 z.1.2,z.2))) :=
    (measurable_fst.fst.min measurable_fst.snd).prodMk
      ((measurable_fst.fst.max measurable_fst.snd).prodMk measurable_snd)
  have h := (measurable_joint_cavitySignedResponseMeanResidual D μ).comp hm
  dsimp only [Function.comp_def] at h
  exact h

theorem measurable_joint_anisotropicWeightedSelfOverlap_two (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n))
    (K : (Paper.Overlap×Paper.Overlap)→Paper.Overlap→ℝ)
    (hK : Measurable (Function.uncurry K)) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n =>
      anisotropicWeightedSelfOverlap D μ a (K z.1) J z.2) := by
  have hKmap : Measurable (fun z : Paper.Overlap×((Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n) =>
      (z.2.1,z.1)) := measurable_snd.fst.prodMk measurable_fst
  have hMmap : Measurable (fun z : Paper.Overlap×((Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n) =>
      (z.1,z.2.2)) := measurable_fst.prodMk measurable_snd.snd
  have hm := (hK.comp hKmap).mul
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hMmap))
  have h := (hm.stronglyMeasurable.integral_prod_left' (μ := parisiFreeMeasure μ a)).measurable
  exact h

theorem cavitySignedResponse_symmetric_mean_residual_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n)
    (r l : Paper.Overlap) (ψ : Paper.Overlap→ℝ) (hψ : Measurable ψ)
    (hb : ∀q,(ψ q)^2≤Gamma β0 μ (min r l)*Gamma β0 μ q) :
    |∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
      anisotropicWeightedSelfOverlap D μ a ψ Finset.univ sample
      ∂anisotropicMeasureSampleLaw D μ a|≤
      2*Real.sqrt (cavitySignedResponseWeightedJ D μ a β0 Finset.univ)*
        cavitySignedResponseSqrtMoment D μ a β0 Finset.univ (min r l) := by
  have h := cavitySignedResponse_mean_residual_pairing D μ a β0 hβ0 ha hμ hn
    (min r l) (max r l) min_le_max ψ hψ hb
  apply h.trans_eq
  unfold cavitySignedResponseSqrtMoment
  have he : Gamma β0 μ ((min r l : Paper.Overlap):ℝ)*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
      cavitySignedResponseCovarianceMoment D μ a Finset.univ (min r l)=
      cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        (Gamma β0 μ ((min r l : Paper.Overlap):ℝ)*cavitySignedResponseCovarianceMoment D μ a Finset.univ (min r l)) := by ring
  rw [he,Real.sqrt_mul (cavitySignedResponseWeightedJ_nonneg D μ a β0 _)]
  ring

theorem cavitySignedResponse_double_mean_residual_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n)
    (K : (Paper.Overlap×Paper.Overlap)→Paper.Overlap→ℝ)
    (hK : Measurable (Function.uncurry K))
    (hb : ∀r l q,(K (r,l) q)^2≤Gamma β0 μ (min r l)*Gamma β0 μ q) :
    |∫r,∫l,∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
      anisotropicWeightedSelfOverlap D μ a (K (r,l)) Finset.univ sample
      ∂anisotropicMeasureSampleLaw D μ a ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a|≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let P := anisotropicMeasureSampleLaw D μ a
  let j := cavitySignedResponseWeightedJ D μ a β0 Finset.univ
  let χ := cavitySignedResponseSqrtMoment D μ a β0 Finset.univ
  let f := fun z : Paper.Overlap×Paper.Overlap => ∫sample,
    cavitySignedResponseSymmetricMeanResidual D μ z.1 z.2 sample*
      anisotropicWeightedSelfOverlap D μ a (K z) Finset.univ sample ∂P
  have hkernel (r l q : Paper.Overlap) : |K (r,l) q|≤1 := by
    have h := (hb r l q).trans ((mul_le_mul (scalarGamma_le_one β0 μ (min r l) (min r l).property)
      (scalarGamma_le_one β0 μ q q.property) (scalarGamma_nonneg β0 μ q) zero_le_one).trans_eq
        (one_mul (1:ℝ)))
    nlinarith [sq_abs (K (r,l) q),abs_nonneg (K (r,l) q)]
  have hm := (measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).mul
    (measurable_joint_anisotropicWeightedSelfOverlap_two D μ a Finset.univ K hK)
  have hf : Measurable f := (hm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hfB (z : Paper.Overlap×Paper.Overlap) : ‖f z‖≤2 := by
    change ‖∫sample,cavitySignedResponseMeanResidual D μ (min z.1 z.2) (max z.1 z.2) sample*
      anisotropicWeightedSelfOverlap D μ a (K z) Finset.univ sample ∂P‖≤2
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      norm_integral_le_of_norm_le (integrable_const (μ := P) (2:ℝ)) (.of_forall fun sample =>
        (norm_mul _ _).trans_le ((mul_le_mul
          (norm_cavitySignedResponseMeanResidual_le D μ (min z.1 z.2) (max z.1 z.2) sample)
          (norm_anisotropicWeightedSelfOverlap_le D μ a ha (K z) Finset.univ 1 zero_le_one
            (hkernel z.1 z.2) sample) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)))
  have hχm : Measurable χ := measurable_cavitySignedResponseSqrtMoment D μ a β0 hβ0 _
  have hχB := norm_cavitySignedResponseSqrtMoment_le D μ a β0 Finset.univ
  have hgB := fun r l => hχB (min r l)
  have hfI : Integrable f (ν.prod ν) := (integrable_const (2:ℝ)).mono' hf.aestronglyMeasurable (.of_forall hfB)
  have hgI : Integrable (fun z : Paper.Overlap×Paper.Overlap=>χ (min z.1 z.2)) (ν.prod ν) :=
    (integrable_const _).mono' (hχm.comp (measurable_fst.min measurable_snd)).aestronglyMeasurable
      (.of_forall fun z=>hχB (min z.1 z.2))
  have hpoint (z : Paper.Overlap×Paper.Overlap) : ‖f z‖≤(2*Real.sqrt j)*χ (min z.1 z.2) := by
    have hzm : Measurable (fun q : Paper.Overlap => (z,q)) := measurable_const.prodMk measurable_id
    simpa only [Real.norm_eq_abs,mul_assoc] using
      cavitySignedResponse_symmetric_mean_residual_pairing D μ a β0 hβ0 ha hμ hn z.1 z.2
        (K z) (hK.comp hzm) (hb z.1 z.2)
  have h := norm_integral_le_of_norm_le (hgI.const_mul (2*Real.sqrt j)) (.of_forall hpoint)
  rw [integral_const_mul,integral_prod _ hfI,integral_prod _ hgI,Real.norm_eq_abs] at h
  have hmin := cavitySignedResponse_minimum_free_integral_le μ a ha χ hχm _ (Real.sqrt_nonneg _)
    (fun q=>Real.sqrt_nonneg _) hχB
  have hs := cavitySignedResponse_sqrt_free_integral_le D μ a β0 ha hβ0 Finset.univ
  exact h.trans ((mul_le_mul_of_nonneg_left
    (hmin.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by positivity)).trans_eq
      (by dsimp only [j]
          calc
            _=4*(Real.sqrt (cavitySignedResponseWeightedJ D μ a β0 Finset.univ))^2 := by ring
            _=_ := by rw [Real.sq_sqrt (cavitySignedResponseWeightedJ_nonneg D μ a β0 _)]))

end QuantitativeFollowup
