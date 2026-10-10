module
public import QuantitativePaper.VectorMeasureKernelMean
public import QuantitativePaper.VectorMeasureHessianCovariance
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! A genuine regular conditional law of the whole continuous mean path.
Clipping coordinates only extends bounded tests off the actual path range. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

abbrev VectorContinuousMeanPath (n : ℕ) := C(Paper.Overlap, Field n)

def vectorMeasureContinuousMeanPath (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (p : VectorDisorderBrownianSample n) : VectorContinuousMeanPath n :=
  ⟨fun q => vectorMeasureSpinMean μ β t ht q p, continuous_vectorMeasureSpinMean_path μ β t ht p⟩

theorem measurable_vectorMeasureContinuousMeanPath (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) : Measurable (vectorMeasureContinuousMeanPath (n:=n) μ β t ht) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact (adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl

def vectorMeanPathDirection (w : Field n) (q : Paper.Overlap) (f : VectorContinuousMeanPath n) : ℝ :=
  ∑l : Fin n, w l*(projIcc (-1:ℝ) 1 (by norm_num) (f q l):ℝ)

theorem continuous_vectorMeanPathDirection (w : Field n) :
    Continuous (fun z : Paper.Overlap × VectorContinuousMeanPath n => vectorMeanPathDirection w z.1 z.2) := by
  unfold vectorMeanPathDirection
  apply continuous_finset_sum
  intro l _
  exact (continuous_subtype_val.comp (continuous_projIcc.comp
    ((EuclideanSpace.proj l).continuous.comp (continuous_snd.eval continuous_fst)))).const_mul (w l)

theorem vectorMeanPathDirection_bound (w : Field n) (q : Paper.Overlap)
    (f : VectorContinuousMeanPath n) : |vectorMeanPathDirection w q f| ≤ vectorDirectionBound w := by
  unfold vectorMeanPathDirection vectorDirectionBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  have hb : |(projIcc (-1:ℝ) 1 (by norm_num) (f q l):ℝ)| ≤ 1 :=
    abs_le.mpr (projIcc (-1:ℝ) 1 (by norm_num) (f q l)).property
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (abs_nonneg (w l))

theorem vectorMeanPathDirection_actual (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (w : Field n) (q : Paper.Overlap) (p : VectorDisorderBrownianSample n) :
    vectorMeanPathDirection w q (vectorMeasureContinuousMeanPath μ β t ht p) =
      vectorMeasureMeanInDirection μ β t ht q w p := by
  unfold vectorMeanPathDirection vectorMeasureMeanInDirection
  apply Finset.sum_congr rfl
  intro l _
  have hb := abs_le.mp (vectorMeasureSpinMean_component_bound μ β t ht q p l)
  have he : projIcc (-1:ℝ) 1 (by norm_num) (vectorMeasureSpinMean μ β t ht q p l) =
      (⟨vectorMeasureSpinMean μ β t ht q p l,hb⟩ : Icc (-1:ℝ) 1) :=
    projIcc_of_mem (by norm_num) hb
  change w l*(projIcc (-1:ℝ) 1 (by norm_num) (vectorMeasureSpinMean μ β t ht q p l):ℝ) = _
  rw [he]

def vectorPastMeanPathKernel (μ : Paper.ParisiMeasure) (β t a : ℝ) (q : Paper.Overlap)
    (ht : t ≤ 1) :
    @Kernel (VectorDisorderBrownianSample n) (VectorContinuousMeanPath n)
      (vectorBrownianFiltration n (q:ℝ).toNNReal) inferInstance := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n) := inferInstance
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let V := vectorBrownianFiltration n (q:ℝ).toNNReal
  exact @condDistrib (VectorDisorderBrownianSample n) (VectorDisorderBrownianSample n)
    (VectorContinuousMeanPath n) inferInstance inferInstance inferInstance ambient V
    (vectorMeasureContinuousMeanPath μ β t ht) id P inferInstance

instance vectorPastMeanPathKernel_markov (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) :
    IsMarkovKernel (vectorPastMeanPathKernel (n:=n) μ β t a q ht) := by
  unfold vectorPastMeanPathKernel
  infer_instance

theorem vectorPastMeanPathKernel_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (F : VectorContinuousMeanPath n → ℝ)
    (hF : Measurable F) (R : ℝ) (hR : ∀f, ‖F f‖ ≤ R) :
    (vectorMeasureDisorderTilt μ β t a)[
      (fun p => F (vectorMeasureContinuousMeanPath μ β t ht p)) |
        vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun p => ∫f, F f ∂vectorPastMeanPathKernel μ β t a q ht p := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n) := inferInstance
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let V := vectorBrownianFiltration n (q:ℝ).toNNReal
  have hi : Integrable (fun p => F (vectorMeasureContinuousMeanPath μ β t ht p)) P :=
    (integrable_const R).mono'
      (hF.comp (measurable_vectorMeasureContinuousMeanPath μ β t ht)).aestronglyMeasurable
      (.of_forall fun p => hR _)
  have he := @condExp_ae_eq_integral_condDistrib
    (VectorDisorderBrownianSample n) (VectorDisorderBrownianSample n) (VectorContinuousMeanPath n) ℝ
    inferInstance inferInstance inferInstance inferInstance ambient P inferInstance
    id (vectorMeasureContinuousMeanPath μ β t ht) V inferInstance inferInstance
    (@measurable_id'' (VectorDisorderBrownianSample n) V ambient ((vectorBrownianFiltration n).le _))
    (measurable_vectorMeasureContinuousMeanPath μ β t ht).aemeasurable F hF.stronglyMeasurable hi
  simpa only [MeasurableSpace.comap_id, id_eq, vectorPastMeanPathKernel, P, V] using he

end QuantitativePaper
