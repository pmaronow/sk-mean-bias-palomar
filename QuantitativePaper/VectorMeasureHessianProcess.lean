module
public import QuantitativePaper.VectorTiltedBrownian
public import QuantitativePaper.VectorMeasureHessianEnergy
public import QuantitativeFollowup.VectorMeanMartingale

@[expose] public section

/-! The literal Hessian along the actual diffusion is a bounded continuous
adapted matrix process. These properties concern the constructed process,
not an assumed stochastic representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorMeasureHessianProcess (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Field n →L[ℝ] Field n :=
  vectorMeasureHessian μ β t q sample.1
    (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)

theorem adapted_vectorMeasureHessianProcess (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (vectorMeasureHessianProcess (n := n) μ β t ht q) := by
  let insert : VectorDisorderBrownianSample n → Paper.Overlap × VectorParameter n :=
    fun sample => (q, (sample.1, vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hJ := adapted_vectorMeasureJointState (n := n) μ β t ht (q : ℝ).toNNReal
  have hm : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] insert :=
    measurable_const.prodMk hJ
  have hc := (continuous_vectorMeasureHessian (n := n) μ β t ht).measurable.comp hm
  dsimp only [Function.comp_def, insert] at hc
  exact hc

theorem continuous_vectorMeasureHessianProcess_path (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q => vectorMeasureHessianProcess μ β t ht q sample) := by
  let insert : Paper.Overlap → Paper.Overlap × VectorParameter n := fun q =>
    (q, (sample.1, vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hX : Continuous (fun q : Paper.Overlap =>
      vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) :=
    (continuous_vectorMeasureState μ β t ht sample).comp
    (continuous_real_toNNReal.comp continuous_subtype_val)
  have hi : Continuous insert := continuous_id.prodMk (continuous_const.prodMk hX)
  have hc := (continuous_vectorMeasureHessian (n := n) μ β t ht).comp hi
  simpa only [vectorMeasureHessianProcess, insert, Function.comp_def] using hc

theorem norm_vectorMeasureHessianProcess_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureHessianProcess μ β t ht q sample‖ ≤ (n : ℝ) :=
  norm_vectorMeasureHessian_le μ β t ht q sample.1 _

def vectorMeasureHessianRow (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (l : Fin n) (sample : VectorDisorderBrownianSample n) : Field n →L[ℝ] ℝ :=
  (EuclideanSpace.proj l).comp (vectorMeasureHessianProcess μ β t ht q sample)

theorem adapted_vectorMeasureHessianRow (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (l : Fin n) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (vectorMeasureHessianRow μ β t ht q l) := by
  exact (ContinuousLinearMap.compL ℝ (Field n) (Field n) ℝ
    (EuclideanSpace.proj l)).continuous.measurable.comp
      (adapted_vectorMeasureHessianProcess μ β t ht q)

theorem norm_vectorMeasureHessianRow_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureHessianRow μ β t ht q l sample‖ ≤ (n : ℝ) := by
  apply (vectorMeasureHessianRow μ β t ht q l sample).opNorm_le_bound (Nat.cast_nonneg n)
  intro x
  exact (PiLp.norm_apply_le _ l).trans
    (((vectorMeasureHessianProcess μ β t ht q sample).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (norm_vectorMeasureHessianProcess_le μ β t ht q sample) (norm_nonneg x)))

theorem continuous_vectorMeasureHessianRow_path (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q => vectorMeasureHessianRow μ β t ht q l sample) :=
  (ContinuousLinearMap.compL ℝ (Field n) (Field n) ℝ (EuclideanSpace.proj l)).continuous.comp
    (continuous_vectorMeasureHessianProcess_path μ β t ht sample)

theorem memLp_vectorMeasureSpinMean_component (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (l : Fin n) :
    MemLp (fun sample => vectorMeasureSpinMean μ β t ht q sample l) 2
      (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  exact MemLp.of_bound ((adapted_vectorMeasureSpinMean_component μ β t ht q l).mono
    ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable 1
      (.of_forall fun sample => by simpa only [Real.norm_eq_abs] using
        vectorMeasureSpinMean_component_bound μ β t ht q sample l)

theorem martingale_vectorOverlapBrownian_coordinate (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (l : Fin n) :
    Martingale (fun q : Paper.Overlap => fun sample =>
      disorderVectorBrownian (q : ℝ).toNNReal sample l)
      (QuantitativeFollowup.vectorOverlapFiltration n) (vectorMeasureDisorderTilt μ β t a) := by
  have hJ := martingale_disorderVectorBrownian_coordinate_tilted μ β t a ht l
  refine ⟨fun q => hJ.stronglyMeasurable _, ?_⟩
  intro r q hrq
  exact hJ.condExp_ae_eq (Real.toNNReal_mono hrq)

theorem memLp_vectorOverlapBrownian_coordinate (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (l : Fin n) :
    MemLp (fun sample => disorderVectorBrownian (q : ℝ).toNNReal sample l) 2
      (vectorMeasureDisorderTilt μ β t a) := by
  have hG := (isBrownianReal_disorderVectorBrownian_coordinate_tilted μ β t a ht l).toIsPreBrownianReal.isGaussianProcess
  exact (hG.hasGaussianLaw_eval (q : ℝ).toNNReal).memLp_two

end QuantitativePaper
