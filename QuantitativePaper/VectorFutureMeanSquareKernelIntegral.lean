module
public import QuantitativePaper.VectorConditionalMeanSquareKernel
public import QuantitativePaper.VectorProfileFutureMeanLoss

@[expose] public section

/-! Actual conditional future integrals, with joint measurability and
Fubini proved under the genuine physical disorder tilt and profile law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem parisi_future_mass (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    (μ:Measure Paper.Overlap).real {u | q < u} = 1-Paper.parisiCDF μ q := by
  have he := measureReal_add_measureReal_compl (μ:=(μ:Measure Paper.Overlap))
    (s:={u : Paper.Overlap | (u:ℝ) ≤ q})
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  have hc : {u : Paper.Overlap | (u:ℝ) ≤ q}ᶜ = {u | q < u} := by
    ext u
    simp only [mem_compl_iff, mem_setOf_eq, not_le]
    rfl
  rw [hc, probReal_univ] at he
  change _ = 1-(μ:Measure Paper.Overlap).real {u | (u:ℝ) ≤ q}
  linarith

def vectorFutureMeanSquareKernelIntegral (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n) (p : VectorDisorderBrownianSample n) : ℝ :=
  ∫u : Paper.Overlap, if q < u then vectorPastMeanSquareKernel μ β t a q ht u w p else 0
    ∂(μ:Measure Paper.Overlap)

theorem adapted_vectorFutureMeanSquareKernelIntegral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n) :
    StronglyMeasurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (vectorFutureMeanSquareKernelIntegral μ β t a q ht w) := by
  let V := vectorBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := V
  have hK := measurable_uncurry_vectorPastMeanSquareKernel μ β t a q ht w
  have hF : Measurable (fun z : Paper.Overlap × VectorDisorderBrownianSample n =>
      if q < z.1 then vectorPastMeanSquareKernel μ β t a q ht z.1 w z.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hK measurable_const
  exact hF.stronglyMeasurable.integral_prod_left' (μ:=(μ:Measure Paper.Overlap))

theorem norm_vectorFutureMeanSquareKernelIntegral_le (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n)
    (p : VectorDisorderBrownianSample n) :
    ‖vectorFutureMeanSquareKernelIntegral μ β t a q ht w p‖ ≤ (vectorDirectionBound w)^2 := by
  unfold vectorFutureMeanSquareKernelIntegral
  apply (norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (C:=(vectorDirectionBound w)^2) _).trans_eq (by simp only [probReal_univ, mul_one])
  exact .of_forall fun u => by
    split_ifs
    · exact norm_vectorPastMeanSquareKernel_le μ β t a q ht u w p
    · simp only [norm_zero]
      exact sq_nonneg _

theorem integrable_vectorFutureMeanSquareKernelIntegral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n) :
    Integrable (vectorFutureMeanSquareKernelIntegral μ β t a q ht w)
      (vectorMeasureDisorderTilt μ β t a) := by
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  exact (integrable_const ((vectorDirectionBound w)^2)).mono'
    ((adapted_vectorFutureMeanSquareKernelIntegral μ β t a q ht w).mono
      ((vectorBrownianFiltration n).le _)).aestronglyMeasurable
    (.of_forall (norm_vectorFutureMeanSquareKernelIntegral_le μ β t a q ht w))

theorem vectorFutureMeanSquareKernelIntegral_weighted_pairing (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*vectorFutureMeanSquareKernelIntegral μ β t a q ht w p
      ∂vectorMeasureDisorderTilt μ β t a) =
      vectorMeasureFutureMeanSquareTail μ β t a ht q w Z := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let F := fun z : Paper.Overlap × VectorDisorderBrownianSample n =>
    Z z.2*(if q < z.1 then vectorPastMeanSquareKernel μ β t a q ht z.1 w z.2 else 0)
  have hinc : @Measurable (VectorDisorderBrownianSample n) (VectorDisorderBrownianSample n)
      inferInstance (vectorBrownianFiltration n (q:ℝ).toNNReal) id :=
    measurable_id'' ((vectorBrownianFiltration n).le _)
  have hK : Measurable (fun z : Paper.Overlap × VectorDisorderBrownianSample n =>
      vectorPastMeanSquareKernel μ β t a q ht z.1 w z.2) :=
    (measurable_uncurry_vectorPastMeanSquareKernel μ β t a q ht w).comp
      (measurable_fst.prodMk (hinc.comp measurable_snd))
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hF : Measurable F := (hZm.comp measurable_snd).mul
    (Measurable.ite (measurableSet_lt measurable_const measurable_fst) hK measurable_const)
  have hB z : ‖F z‖ ≤ (C:ℝ)*(vectorDirectionBound w)^2 := by
    dsimp only [F]
    rw [norm_mul]
    apply mul_le_mul (hC z.2) _ (norm_nonneg _) C.coe_nonneg
    split_ifs
    · exact norm_vectorPastMeanSquareKernel_le μ β t a q ht z.1 w z.2
    · simp only [norm_zero]
      exact sq_nonneg _
  have hi : Integrable F ((μ:Measure Paper.Overlap).prod P) :=
    (integrable_const ((C:ℝ)*(vectorDirectionBound w)^2)).mono' hF.aestronglyMeasurable (.of_forall hB)
  calc
    _ = ∫p, (∫u : Paper.Overlap, F (u,p) ∂(μ:Measure Paper.Overlap)) ∂P := by
      apply integral_congr_ae
      exact .of_forall fun p => (integral_const_mul (Z p) _).symm
    _ = ∫u : Paper.Overlap, (∫p, F (u,p) ∂P) ∂(μ:Measure Paper.Overlap) :=
      (integral_integral_swap hi).symm
    _ = _ := by
      unfold vectorMeasureFutureMeanSquareTail
      apply integral_congr_ae
      exact .of_forall fun u => by
        by_cases hqu : q < u
        · simp only [F, ite_eq_left hqu]
          exact vectorPastMeanSquareKernel_weighted_pairing μ β t a q ht u w Z hZ C hC
        · simp only [F, ite_eq_right hqu, mul_zero, integral_zero]

end QuantitativePaper
