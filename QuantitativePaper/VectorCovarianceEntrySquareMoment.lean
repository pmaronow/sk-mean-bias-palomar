module
public import FourPapersCommon.ConditionalSquareMoment
public import QuantitativePaper.VectorConditionalReplicaMoments
public import QuantitativePaper.VectorMeasureKernelMean

@[expose] public section

/-! The genuine conditional covariance square, expressed using a squared
conditional expectation and continuous magnetization observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped BigOperators NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem vectorMeasureSpinCovariance_entry_square_moment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    (∫z : VectorMarkedSample n,(vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2
      ∂vectorMeasureSpinPathLaw μ β t a ht)=
    (∫z : VectorMarkedSample n,((vectorMeasureSpinPathLaw μ β t a ht)[
      (fun z : VectorMarkedSample n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j))|
        vectorSpinPast n (q:ℝ).toNNReal] z)^2∂vectorMeasureSpinPathLaw μ β t a ht)-
    2*(∫z : VectorMarkedSample n,Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)*
      (vectorMeasureSpinMean μ β t ht q z.1 i*vectorMeasureSpinMean μ β t ht q z.1 j)
      ∂vectorMeasureSpinPathLaw μ β t a ht)+
    (∫z : VectorMarkedSample n,(vectorMeasureSpinMean μ β t ht q z.1 i*
      vectorMeasureSpinMean μ β t ht q z.1 j)^2∂vectorMeasureSpinPathLaw μ β t a ht) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  let ambient : MeasurableSpace (VectorMarkedSample n):=inferInstance
  let V:=vectorSpinPast n (q:ℝ).toNNReal
  let F:=fun z : VectorMarkedSample n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)
  let Z:=fun z : VectorMarkedSample n=>vectorMeasureSpinMean μ β t ht q z.1 i*
    vectorMeasureSpinMean μ β t ht q z.1 j
  letI : MeasurableSpace (VectorMarkedSample n):=ambient
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hFm : Measurable F:=(measurable_of_finite
    (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))).comp measurable_snd
  have hF : MemLp F 2 J:=MemLp.of_bound hFm.aestronglyMeasurable 1
    (.of_forall fun z=>by simp [F,Real.norm_eq_abs,abs_mul,Paper.abs_spinSign])
  have hknown : StronglyMeasurable[V] Z :=
    ((adapted_vectorMeasureSpinMean_joint μ β t ht q i).mul
      (adapted_vectorMeasureSpinMean_joint μ β t ht q j)).stronglyMeasurable
  have hZ : MemLp Z 2 J:=MemLp.of_bound
    (hknown.mono (vectorSpinPast_le n _)).aestronglyMeasurable 1 (.of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul (vectorMeasureSpinMean_component_bound μ β t ht q z.1 i)
        (vectorMeasureSpinMean_component_bound μ β t ht q z.1 j) (abs_nonneg _) zero_le_one).trans_eq
          (by ring))
  have he:=vectorMeasureSpinPathLaw_terminal_observable_condExp (n:=n) μ β t a ht q
    (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))
  have hsq : (∫z : VectorMarkedSample n,(vectorMeasureSpinCovariance μ β t a ht q z.1 i j)^2∂J)=
      ∫z,(J[F|V] z-Z z)^2∂J := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    dsimp only [vectorMeasureSpinCovariance]
    rw [hz]
  rw [hsq]
  exact integral_condExp_sub_known_sq V (vectorSpinPast_le n _) F Z hF hZ hknown

end QuantitativePaper
