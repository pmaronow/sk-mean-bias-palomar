module
public import QuantitativePaper.VectorControlEnvelope
public import FourPapersCommon.IntegrableTruncation
public import FourPapersCommon.UniformSlopeLimit

@[expose] public section

/-! The control envelope under a genuinely integrable initial weight. Bounded
truncations converge uniformly at the level of increments divided by the mix
parameter, so the actual exponential disorder weight is permitted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasurePotentialMixIncrement (μ ν : Paper.ParisiMeasure) (β t lam : ℝ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0-
    vectorMeasurePotential μ β t sample.1 0

theorem measurable_vectorMeasurePotentialMixIncrement (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) :
    Measurable (vectorMeasurePotentialMixIncrement (n := n) μ ν β t lam) :=
  by
    have hm (ρ : Paper.ParisiMeasure) : Measurable (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0) := by
      have hp : Continuous (fun p : Couplings n × ℝ => ((p,(0 : Field n)) : VectorParameter n)) :=
        continuous_id.prodMk continuous_const
      have hh := (continuous_vectorMeasurePotential_joint (n := n) ρ β t ht).comp hp
      simpa only [Function.comp_def] using hh.measurable
    exact ((hm _).comp measurable_fst).sub ((hm μ).comp measurable_fst)

theorem norm_vectorMeasurePotentialMixIncrement_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasurePotentialMixIncrement μ ν β t lam sample‖ ≤
      ((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance ν μ)*‖lam‖ := by
  have hh := vectorMeasurePotential_CDFDistance_abs_sub_le (n := n)
    (Paper.parisiMix μ ν lam) μ β t ht sample.1 0
  rw [parisiCDFDistance_mix_left μ ν lam hlam] at hh
  rw [Real.norm_of_nonneg hlam.1]
  simpa only [vectorMeasurePotentialMixIncrement,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hh

theorem integrable_vectorMeasurePotentialMixIncrement_weighted (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (W : VectorDisorderBrownianSample n → ℝ) (hi : Integrable W (vectorDisorderBrownianMeasure n)) :
    Integrable (fun sample => W sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample)
      (vectorDisorderBrownianMeasure n) :=
  integrable_weight_mul_bounded W _ hi
    (measurable_vectorMeasurePotentialMixIncrement μ ν β t ht lam)
    (((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance ν μ)*‖lam‖)
    (norm_vectorMeasurePotentialMixIncrement_le μ ν β t ht lam hlam)

theorem hasDerivWithinAt_vectorMeasurePotential_mix_integrable_weight
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (W : VectorDisorderBrownianSample n → ℝ)
    (hW : Measurable[vectorBrownianFiltration n 0] W)
    (hn : ∀sample,0 ≤ W sample) (hi : Integrable W (vectorDisorderBrownianMeasure n)) :
    HasDerivWithinAt (fun lam => ∫sample,W sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample
      ∂vectorDisorderBrownianMeasure n)
      (vectorWeightedMeasureControlDerivative μ ν β t ht W) (Icc (0 : ℝ) 1) 0 := by
  let P := vectorDisorderBrownianMeasure n
  let A := vectorMeasureFeedbackControl (n := n) μ β t ht
  have hA : IsVectorParisiControl A := isVectorParisiControl_vectorMeasureFeedbackControl μ β t ht
  have hWg : Measurable W := hW.mono ((vectorBrownianFiltration n).le 0) le_rfl
  let R := (n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance ν μ
  let Wk := truncateWeight W
  let F := fun k lam => ∫sample,Wk k sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample ∂P
  let D := fun k => vectorWeightedMeasureControlDerivative μ ν β t ht (Wk k)
  let error := fun k => R*(∫sample,W sample-Wk k sample ∂P)
  have hFk (k : ℕ) : HasDerivWithinAt (F k) (D k) (Icc (0 : ℝ) 1) 0 := by
    have hkm : Measurable[vectorBrownianFiltration n 0] (Wk k) := measurable_const.min hW
    have hkb (sample) : ‖Wk k sample‖ ≤ (k : ℝ≥0) := norm_truncateWeight_le W hn k sample
    have hkn (sample) : 0 ≤ Wk k sample := truncateWeight_nonneg W hn k sample
    have hd := (hasDerivWithinAt_vectorMeasurePotential_mix_weighted_control μ ν β t ht
      (Wk k) hkm (k : ℝ≥0) hkb hkn).sub_const
        (∫sample,Wk k sample*vectorMeasurePotential μ β t sample.1 0 ∂P)
    apply hd.congr_of_mem
    · intro lam hlam
      dsimp only [F,vectorMeasurePotentialMixIncrement]
      have ik (ρ : Paper.ParisiMeasure) : Integrable
          (fun sample => Wk k sample*vectorMeasurePotential ρ β t sample.1 0) P :=
        ((integrable_vectorMeasurePotential ρ β t ht (0 : Field n)).comp_fst (vectorBrownianMeasure n)).bdd_mul
          (hkm.mono ((vectorBrownianFiltration n).le 0) le_rfl).aestronglyMeasurable (Eventually.of_forall hkb)
      rw [←integral_sub (ik _) (ik μ)]
      congr 1
      funext sample
      ring
    · exact ⟨le_rfl,zero_le_one⟩
  have hD : Tendsto D atTop (𝓝 (vectorWeightedMeasureControlDerivative μ ν β t ht W)) := by
    exact tendsto_integral_truncateWeight_mul W (vectorAffineControlDerivative μ ν β t A 0)
      hWg hn hi (measurable_vectorAffineControlDerivative μ ν β t A hA 0)
      (3*|(1-t)*β^2| *(n : ℝ)) (norm_vectorAffineControlDerivative_le μ ν β t A hA 0)
  have he : Tendsto error atTop (𝓝 0) := by
    simpa only [error,mul_zero] using (tendsto_integral_truncation_tail W hWg hn hi).const_mul R
  apply hasDerivWithinAt_zero_of_uniform_increment_approximation
    (F := F) (D := D) (error := error) (hF := hFk) (hD := hD) (he := he)
  intro k lam hlam
  have hzero : vectorMeasurePotentialMixIncrement (n := n) μ ν β t 0=fun _ => 0 := by
    funext sample
    simp [vectorMeasurePotentialMixIncrement,Paper.parisiMix_zero]
  have hiK := integrable_truncateWeight W hWg hn hi k
  have hip := integrable_vectorMeasurePotentialMixIncrement_weighted μ ν β t ht lam hlam W hi
  have hik := integrable_vectorMeasurePotentialMixIncrement_weighted μ ν β t ht lam hlam (Wk k) hiK
  dsimp only [F]
  rw [hzero]
  simp only [mul_zero,integral_zero,sub_zero]
  rw [←integral_sub hik hip]
  have htai : Integrable (fun sample => W sample-Wk k sample) P := hi.sub hiK
  have hnai (sample) : 0 ≤ W sample-Wk k sample := sub_nonneg.mpr (truncateWeight_le W k sample)
  have hinorm := norm_integral_le_of_norm_le
    (f := fun sample => Wk k sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample-
      W sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample)
    (g := fun sample => (R*‖lam‖)*(W sample-Wk k sample))
    (htai.const_mul (R*‖lam‖))
    (Eventually.of_forall (fun sample => by
      rw [show Wk k sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample-
        W sample*vectorMeasurePotentialMixIncrement μ ν β t lam sample=
        (Wk k sample-W sample)*vectorMeasurePotentialMixIncrement μ ν β t lam sample from by ring,
        norm_mul,Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg (hnai sample)]
      exact (mul_le_mul_of_nonneg_left
        (norm_vectorMeasurePotentialMixIncrement_le μ ν β t ht lam hlam sample) (hnai sample)).trans_eq (mul_comm _ _)))
  rw [integral_const_mul] at hinorm
  convert hinorm using 1
  dsimp only [error]
  ring

end QuantitativePaper
