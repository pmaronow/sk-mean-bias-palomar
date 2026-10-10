module
public import QuantitativeFollowup.FollowupCavitySignedResponseJointMeasurability
public import QuantitativeFollowup.FollowupCavitySignedResponseIntegration

@[expose] public section

/-! Genuine integrated signed residual estimates. Joint measurability and
integrability are proved for every bounded admissible deterministic kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

private theorem kernel_norm_le_one (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (K : Paper.Overlap→Paper.Overlap→ℝ)
    (hb : ∀r q,(K r q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q) (r q : Paper.Overlap) :
    |K r q| ≤ 1 := by
  have h := (hb r q).trans ((mul_le_mul (scalarGamma_le_one β0 μ r r.property)
    (scalarGamma_le_one β0 μ q q.property) (scalarGamma_nonneg β0 μ q) zero_le_one).trans_eq
      (one_mul (1:ℝ)))
  nlinarith [sq_abs (K r q),abs_nonneg (K r q)]

private theorem integrated_sharp_sqrt_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (ha : a∈Icc (0:ℝ) 1) (hβ0 : β0≠0)
    (f : Paper.Overlap→ℝ) (hf : Measurable f) (B : ℝ) (hfB : ∀r,‖f r‖≤B)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀r,|f r|≤C*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
      cavitySignedResponseCovarianceMoment D μ a Finset.univ r)) :
    |∫r,f r ∂parisiFreeMeasure μ a|≤C*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let j := cavitySignedResponseWeightedJ D μ a β0 Finset.univ
  let χ := cavitySignedResponseSqrtMoment D μ a β0 Finset.univ
  have hj : 0≤j := cavitySignedResponseWeightedJ_nonneg D μ a β0 _
  have hi : Integrable f ν := (integrable_const B).mono' hf.aestronglyMeasurable (.of_forall hfB)
  have hχi : Integrable χ ν := (integrable_const _).mono'
    (measurable_cavitySignedResponseSqrtMoment D μ a β0 hβ0 _).aestronglyMeasurable
    (.of_forall (norm_cavitySignedResponseSqrtMoment_le D μ a β0 _))
  have hs (r : Paper.Overlap) : Real.sqrt (Gamma β0 μ r*j*
      cavitySignedResponseCovarianceMoment D μ a Finset.univ r)=Real.sqrt j*χ r := by
    have he : Gamma β0 μ r*j*cavitySignedResponseCovarianceMoment D μ a Finset.univ r=
      j*(Gamma β0 μ r*cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by ring
    rw [he,Real.sqrt_mul hj]
    rfl
  have hp (r : Paper.Overlap) : ‖f r‖≤(C*Real.sqrt j)*χ r := by
    have hh := hb r
    change |f r|≤C*Real.sqrt (Gamma β0 μ r*j*cavitySignedResponseCovarianceMoment D μ a Finset.univ r) at hh
    rw [hs] at hh
    simpa only [Real.norm_eq_abs,mul_assoc] using hh
  have h := norm_integral_le_of_norm_le (hχi.const_mul (C*Real.sqrt j)) (.of_forall hp)
  rw [integral_const_mul,Real.norm_eq_abs] at h
  have hχ := cavitySignedResponse_sqrt_free_integral_le D μ a β0 ha hβ0 Finset.univ
  exact h.trans ((mul_le_mul_of_nonneg_left hχ (mul_nonneg hC (Real.sqrt_nonneg j))).trans_eq
    (by rw [mul_assoc,←pow_two,Real.sq_sqrt hj]))

theorem cavitySignedResponse_integrated_terminal_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n)
    (K : Paper.Overlap→Paper.Overlap→ℝ) (hK : Measurable (Function.uncurry K))
    (hb : ∀r q,(K r q)^2≤Gamma β0 μ r*Gamma β0 μ q) :
    |∫r,∫p,cavitySignedResponseTerminalResidual D μ r p*
      anisotropicWeightedSelfOverlap D μ a (K r) Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a| ≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let f := fun r : Paper.Overlap => ∫p,cavitySignedResponseTerminalResidual D μ r p*
    anisotropicWeightedSelfOverlap D μ a (K r) Finset.univ p.1 ∂anisotropicMeasureSpinPathLaw D μ a
  have hmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hm := (measurable_joint_cavitySignedResponseTerminalResidual D μ).mul
    ((measurable_joint_anisotropicWeightedSelfOverlap D μ a Finset.univ K hK).comp hmap)
  have hf : Measurable f := (hm.stronglyMeasurable.integral_prod_right'
    (ν := anisotropicMeasureSpinPathLaw D μ a)).measurable
  have hB (r : Paper.Overlap) : ‖f r‖≤2 := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      norm_integral_le_of_norm_le (integrable_const (μ := anisotropicMeasureSpinPathLaw D μ a) (2:ℝ))
        (.of_forall fun p => (norm_mul _ _).trans_le ((mul_le_mul
          (norm_cavitySignedResponseTerminalResidual_le D μ r p)
          (norm_anisotropicWeightedSelfOverlap_le D μ a ha (K r) Finset.univ 1 zero_le_one
            (kernel_norm_le_one β0 μ K hb r) p.1) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)))
  apply integrated_sharp_sqrt_bound D μ a β0 ha hβ0 f hf 2 hB 2 (by norm_num)
  intro r
  have hrmap : Measurable (fun q : Paper.Overlap => (r,q)) := measurable_const.prodMk measurable_id
  exact cavitySignedResponse_terminal_pairing D μ a β0 hβ0 ha hμ hn r (K r) (hK.comp hrmap) (hb r)

theorem cavitySignedResponse_integrated_score_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n)
    (K : Paper.Overlap→Paper.Overlap→ℝ) (hK : Measurable (Function.uncurry K))
    (hb : ∀r q,(K r q)^2≤Gamma β0 μ r*Gamma β0 μ q) :
    |∫r,∫p,cavitySignedResponseScore D μ a r p*
      anisotropicWeightedSelfOverlap D μ a (K r) Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a| ≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let f := fun r : Paper.Overlap => ∫p,cavitySignedResponseScore D μ a r p*
    anisotropicWeightedSelfOverlap D μ a (K r) Finset.univ p.1 ∂anisotropicMeasureSpinPathLaw D μ a
  have hmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hm := (measurable_joint_cavitySignedResponseScore D μ a).mul
    ((measurable_joint_anisotropicWeightedSelfOverlap D μ a Finset.univ K hK).comp hmap)
  have hf : Measurable f := (hm.stronglyMeasurable.integral_prod_right'
    (ν := anisotropicMeasureSpinPathLaw D μ a)).measurable
  have hB (r : Paper.Overlap) : ‖f r‖≤4 := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      norm_integral_le_of_norm_le (integrable_const (μ := anisotropicMeasureSpinPathLaw D μ a) (4:ℝ))
        (.of_forall fun p => (norm_mul _ _).trans_le ((mul_le_mul
          (norm_cavitySignedResponseScore_le D μ a ha r p)
          (norm_anisotropicWeightedSelfOverlap_le D μ a ha (K r) Finset.univ 1 zero_le_one
            (kernel_norm_le_one β0 μ K hb r) p.1) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)))
  apply integrated_sharp_sqrt_bound D μ a β0 ha hβ0 f hf 4 hB 4 (by norm_num)
  intro r
  have hrmap : Measurable (fun q : Paper.Overlap => (r,q)) := measurable_const.prodMk measurable_id
  exact cavitySignedResponse_score_pairing D μ a β0 hβ0 ha hμ hn r (K r) (hK.comp hrmap) (hb r)

end QuantitativeFollowup
