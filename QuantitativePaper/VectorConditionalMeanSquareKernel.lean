module
public import QuantitativePaper.VectorConditionalMeanPath
public import FourPapersCommon.ConditionalKernelWeight

@[expose] public section

/-! Jointly measurable genuine conditional mean-square expectations,
with exact bounded-past pairings and bounds discharged from the path law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorPastMeanSquareKernel (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (w : Field n)
    (p : VectorDisorderBrownianSample n) : ℝ :=
  ∫f, (vectorMeanPathDirection w u f)^2 ∂vectorPastMeanPathKernel μ β t a q ht p

theorem measurable_vectorMeanPathDirection_square (w : Field n) (u : Paper.Overlap) :
    Measurable (fun f : VectorContinuousMeanPath n => (vectorMeanPathDirection w u f)^2) :=
  ((continuous_vectorMeanPathDirection w).measurable.comp
    (measurable_const.prodMk measurable_id)).pow_const 2

theorem norm_vectorMeanPathDirection_square_le (w : Field n) (u : Paper.Overlap)
    (f : VectorContinuousMeanPath n) : ‖(vectorMeanPathDirection w u f)^2‖ ≤ (vectorDirectionBound w)^2 := by
  rw [Real.norm_eq_abs, abs_sq]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (vectorMeanPathDirection_bound w u f) 2

theorem norm_vectorPastMeanSquareKernel_le (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (w : Field n)
    (p : VectorDisorderBrownianSample n) :
    ‖vectorPastMeanSquareKernel μ β t a q ht u w p‖ ≤ (vectorDirectionBound w)^2 := by
  unfold vectorPastMeanSquareKernel
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ:=vectorPastMeanPathKernel μ β t a q ht p)
    (.of_forall fun f => norm_vectorMeanPathDirection_square_le w u f)

theorem measurable_uncurry_vectorPastMeanSquareKernel (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n) :
    @Measurable (Paper.Overlap × VectorDisorderBrownianSample n) ℝ
      ((inferInstance : MeasurableSpace Paper.Overlap).prod
        (vectorBrownianFiltration n (q:ℝ).toNNReal)) inferInstance
      (fun z => vectorPastMeanSquareKernel μ β t a q ht z.1 w z.2) := by
  let V := vectorBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := V
  let K : Kernel (VectorDisorderBrownianSample n) (VectorContinuousMeanPath n) :=
    vectorPastMeanPathKernel μ β t a q ht
  let Q : Kernel (Paper.Overlap × VectorDisorderBrownianSample n) (VectorContinuousMeanPath n) :=
    K.comap Prod.snd measurable_snd
  have hF : StronglyMeasurable (fun z : (Paper.Overlap × VectorDisorderBrownianSample n) ×
      VectorContinuousMeanPath n => (vectorMeanPathDirection w z.1.1 z.2)^2) :=
    (((continuous_vectorMeanPathDirection w).measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)).pow_const 2).stronglyMeasurable
  exact (hF.integral_kernel_prod_right' (κ:=Q)).measurable

theorem vectorPastMeanSquareKernel_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (w : Field n) :
    (vectorMeasureDisorderTilt μ β t a)[
      (fun p => (vectorMeasureMeanInDirection μ β t ht u w p)^2) |
        vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
      vectorPastMeanSquareKernel μ β t a q ht u w := by
  change (vectorMeasureDisorderTilt μ β t a)[
    (fun p => (vectorMeasureMeanInDirection μ β t ht u w p)^2) |
      vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
    fun p => ∫f, (vectorMeanPathDirection w u f)^2 ∂vectorPastMeanPathKernel μ β t a q ht p
  have he := vectorPastMeanPathKernel_condExp μ β t a q ht
    (fun f => (vectorMeanPathDirection w u f)^2)
    (measurable_vectorMeanPathDirection_square w u) ((vectorDirectionBound w)^2)
    (norm_vectorMeanPathDirection_square_le w u)
  simpa only [vectorMeanPathDirection_actual, vectorPastMeanSquareKernel] using he

theorem vectorPastMeanSquareKernel_weighted_pairing (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*vectorPastMeanSquareKernel μ β t a q ht u w p
      ∂vectorMeasureDisorderTilt μ β t a) =
      ∫p, Z p*(vectorMeasureMeanInDirection μ β t ht u w p)^2
        ∂vectorMeasureDisorderTilt μ β t a := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hi := integrable_vectorMeasureMeanInDirection_sq μ β t a ht u w
  have hp : Integrable (Z * (fun p => (vectorMeasureMeanInDirection μ β t ht u w p)^2)) P := by
    change Integrable (fun p => Z p*(vectorMeasureMeanInDirection μ β t ht u w p)^2)
      (vectorMeasureDisorderTilt μ β t a)
    simpa only [Pi.mul_apply, mul_comm] using hi.mul_bdd hZm.aestronglyMeasurable (.of_forall hC)
  exact (weighted_kernelObservable_of_condExp_integrable
    (vectorBrownianFiltration n (q:ℝ).toNNReal) P ((vectorBrownianFiltration n).le _)
    _ _ hi (vectorPastMeanSquareKernel_condExp μ β t a q ht u w) Z hZ.stronglyMeasurable hp).symm

end QuantitativePaper
