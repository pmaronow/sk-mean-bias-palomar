module
public import QuantitativePaper.VectorCovarianceEntrySquareMoment
public import QuantitativePaper.VectorSupportCovarianceSquare
public import QuantitativePaper.SpinMatrixDefectAlgebra
public import FourPapersCommon.SquaredConditionalExpectationMonotone
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! Time measurability of the actual expected conditional covariance-square
trace. Squared conditional moments form monotone scalar curves; the remaining
terms are integrals of jointly measurable continuous magnetization paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem measurable_vectorMeasureSpinMean_joint (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun p : Paper.Overlap×VectorMarkedSample n=>
      vectorMeasureSpinMean μ β t ht p.1 p.2.1) := by
  change Measurable (Function.uncurry (fun (q : Paper.Overlap) (z : VectorMarkedSample n)=>
    vectorMeasureSpinMean μ β t ht q z.1))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro z
    exact continuous_vectorMeasureSpinMean_path μ β t ht z.1
  · intro q
    exact ((adapted_vectorMeasureSpinMean μ β t ht q).mono
      ((vectorBrownianFiltration n).le _) le_rfl).comp measurable_fst

theorem monotone_vectorSpinSecond_conditional_square (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (i j : Fin n) :
    Monotone (fun q : Paper.Overlap=>∫z : VectorMarkedSample n,
      ((vectorMeasureSpinPathLaw μ β t a ht)[
        (fun z : VectorMarkedSample n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j))|
          vectorSpinPast n (q:ℝ).toNNReal] z)^2∂vectorMeasureSpinPathLaw μ β t a ht) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  apply monotone_integral_sq_condExp
  · intro r q hrq
    exact MeasurableSpace.comap_mono ((vectorBrownianFiltration n).mono
      (Real.toNNReal_mono (show (r:ℝ)≤(q:ℝ) from hrq)))
  · intro q
    exact vectorSpinPast_le n _
  · apply MemLp.of_bound
      ((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))).comp
        measurable_snd).aestronglyMeasurable (1:ℝ)
    exact .of_forall fun z=>by
      change ‖Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)‖≤1
      simp [Real.norm_eq_abs,Paper.abs_spinSign]

theorem measurable_integral_vectorMeasureSpinCovariance_entry_square
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (i j : Fin n) :
    Measurable (fun q : Paper.Overlap=>∫z : VectorMarkedSample n,
      (vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2∂vectorMeasureSpinPathLaw μ β t a ht) := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hM:=measurable_vectorMeasureSpinMean_joint (n:=n) μ β t ht
  have hMi:=((PiLp.continuous_apply 2 (fun _ : Fin n=>ℝ) i).measurable.comp hM)
  have hMj:=((PiLp.continuous_apply 2 (fun _ : Fin n=>ℝ) j).measurable.comp hM)
  have hT : Measurable (fun p : Paper.Overlap×VectorMarkedSample n=>
      Paper.spinSign (p.2.2 i)*Paper.spinSign (p.2.2 j)) :=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))).comp
      (measurable_snd.comp measurable_snd)
  have hcross : Measurable (fun q : Paper.Overlap=>∫z : VectorMarkedSample n,
      Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)*
        (vectorMeasureSpinMean μ β t ht q z.1 i*vectorMeasureSpinMean μ β t ht q z.1 j)
        ∂vectorMeasureSpinPathLaw μ β t a ht) :=
    (hT.mul (hMi.mul hMj)).stronglyMeasurable.integral_prod_right'.measurable
  have hfour : Measurable (fun q : Paper.Overlap=>∫z : VectorMarkedSample n,
      (vectorMeasureSpinMean μ β t ht q z.1 i*vectorMeasureSpinMean μ β t ht q z.1 j)^2
        ∂vectorMeasureSpinPathLaw μ β t a ht) :=
    ((hMi.mul hMj).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hsq:=(monotone_vectorSpinSecond_conditional_square μ β t a ht i j).measurable
  have he : (fun q : Paper.Overlap=>∫z : VectorMarkedSample n,
      (vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2∂vectorMeasureSpinPathLaw μ β t a ht)=
    fun (q : Paper.Overlap)=>(∫z : VectorMarkedSample n,((vectorMeasureSpinPathLaw μ β t a ht)[
      (fun z : VectorMarkedSample n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j))|
        vectorSpinPast n (q:ℝ).toNNReal] z)^2∂vectorMeasureSpinPathLaw μ β t a ht)-
      2*(∫z : VectorMarkedSample n,Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)*
        (vectorMeasureSpinMean μ β t ht q z.1 i*vectorMeasureSpinMean μ β t ht q z.1 j)
          ∂vectorMeasureSpinPathLaw μ β t a ht)+
      (∫z : VectorMarkedSample n,(vectorMeasureSpinMean μ β t ht q z.1 i*
        vectorMeasureSpinMean μ β t ht q z.1 j)^2∂vectorMeasureSpinPathLaw μ β t a ht) :=
    funext fun q=>vectorMeasureSpinCovariance_entry_square_moment μ β t a ht q i j
  rw [he]
  exact (hsq.sub (measurable_const.mul hcross)).add hfour

theorem measurable_integral_vectorMeasureSpinCovariance_trace_square
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    Measurable (fun q : Paper.Overlap=>∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
        vectorMeasureSpinCovariance μ β t a ht q sample)∂vectorMeasureDisorderTilt μ β t a) := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  haveI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hentry (q : Paper.Overlap) (i j : Fin n) : Integrable
      (fun z : VectorMarkedSample n=>(vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2)
      (vectorMeasureSpinPathLaw μ β t a ht) := by
    apply (integrable_const (4:ℝ)).mono'
      (((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).comp measurable_fst).pow_const 2).aestronglyMeasurable
    have hb:=(measurePreserving_vectorMeasureSpinPathLaw_fst (n:=n) μ β t a ht).quasiMeasurePreserving.ae
      (vectorMeasureSpinCovariance_entry_bound μ β t a ht q)
    filter_upwards [hb] with z hz
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hi:=abs_le.mp (hz i j)
    nlinarith
  have he (q : Paper.Overlap) :
      (∫sample : VectorDisorderBrownianSample n,Matrix.trace
        (vectorMeasureSpinCovariance μ β t a ht q sample*vectorMeasureSpinCovariance μ β t a ht q sample)
          ∂vectorMeasureDisorderTilt μ β t a)=
      ∑i : Fin n,∑j : Fin n,∫z : VectorMarkedSample n,
        (vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2∂vectorMeasureSpinPathLaw μ β t a ht := by
    have hm : Measurable (fun sample : VectorDisorderBrownianSample n=>Matrix.trace
        (vectorMeasureSpinCovariance μ β t a ht q sample*vectorMeasureSpinCovariance μ β t a ht q sample)) := by
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
      exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
        (measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).mul
          (measurable_vectorMeasureSpinCovariance_entry μ β t a ht q j i)
    rw [←integral_vectorMeasureSpinPathLaw_sample μ β t a ht _ hm]
    simp_rw [symmetric_matrix_square_trace _ (vectorMeasureSpinCovariance_symmetric μ β t a ht q _)]
    rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=>hentry q i j)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ fun j _=>hentry q i j
  have hef : (fun q : Paper.Overlap=>∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
        vectorMeasureSpinCovariance μ β t a ht q sample)∂vectorMeasureDisorderTilt μ β t a)=
    fun q=>∑i : Fin n,∑j : Fin n,∫z : VectorMarkedSample n,
      (vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2∂vectorMeasureSpinPathLaw μ β t a ht :=
    funext he
  rw [hef]
  exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
    measurable_integral_vectorMeasureSpinCovariance_entry_square μ β t a ht i j

end QuantitativePaper
