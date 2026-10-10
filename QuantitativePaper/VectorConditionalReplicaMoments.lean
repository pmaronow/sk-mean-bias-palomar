module
public import QuantitativePaper.VectorConditionalReplicaLaw
public import QuantitativePaper.SpinPairMoments
public import QuantitativePaper.VectorMeasureCovarianceTrace

@[expose] public section

/-! Exact first/second conditional replica moments under the actual marked
spin law, and their identification with the genuine conditional covariance
matrix and magnetization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorConditionalTerminalSpinKernel_first_moment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (i : Fin n) :
    (fun z : VectorMarkedSample n=>∫σ,Paper.spinSign (σ i)
      ∂vectorConditionalTerminalSpinKernel μ β t a ht.le q z)
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
        fun z=>vectorMeasureSpinMean μ β t ht.le q z.1 i :=
  (vectorConditionalTerminalSpinKernel_condExp μ β t a ht.le q _).symm.trans
    (vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i)

theorem vectorConditionalTerminalSpinKernel_second_moment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    (fun z : VectorMarkedSample n=>∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j)
      ∂vectorConditionalTerminalSpinKernel μ β t a ht q z)
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
        fun z=>vectorMeasureSpinCovariance μ β t a ht q z.1 i j+
          vectorMeasureSpinMean μ β t ht q z.1 i*vectorMeasureSpinMean μ β t ht q z.1 j := by
  have he:=(vectorConditionalTerminalSpinKernel_condExp μ β t a ht q
    (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))).symm.trans
      (vectorMeasureSpinPathLaw_terminal_observable_condExp (n:=n) μ β t a ht q
        (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j)))
  filter_upwards [he] with z hz
  dsimp only [vectorMeasureSpinCovariance]
  rw [hz]
  ring

def vectorConditionalReplicaMatrixDefect (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  (1/(n:ℝ))^2*∑i : Fin n,∑j : Fin n,
    (vectorMeasureSpinCovariance μ β t a ht q sample i j+
      vectorMeasureSpinMean μ β t ht q sample i*vectorMeasureSpinMean μ β t ht q sample j)^2-
    2*(q:ℝ)*((1/(n:ℝ))*∑i : Fin n,(vectorMeasureSpinMean μ β t ht q sample i)^2)+(q:ℝ)^2

theorem vectorConditionalReplicaDefect_eq_matrix_integral (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    vectorConditionalReplicaDefect (n:=n) μ β t a ht.le q=
      ∫z : VectorMarkedSample n,vectorConditionalReplicaMatrixDefect μ β t a ht.le q z.1
        ∂vectorMeasureSpinPathLaw μ β t a ht.le := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let K:=vectorConditionalTerminalSpinKernel (n:=n) μ β t a ht.le q
  let P:=vectorConditionalReplicaLaw (n:=n) μ β t a ht.le q
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  haveI:=vectorConditionalReplicaLaw_probability (n:=n) μ β t a ht.le q
  have hm : Measurable (fun z : VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-(q:ℝ))^2) :=
    (measurable_of_finite (fun p : Configuration n×Configuration n=>
      (overlap n p.1 p.2-(q:ℝ))^2)).comp measurable_snd
  have hi : Integrable (fun z : VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-(q:ℝ))^2) P := by
    apply (integrable_const (4:ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have ho:=abs_le.mp (abs_vectorOverlap_le_one hn z.2.1 z.2.2)
      nlinarith [q.property.1,q.property.2]
  change (∫z,(overlap n z.2.1 z.2.2-(q:ℝ))^2∂(J ⊗ₘ (K×ₖK)))=_
  rw [Measure.integral_compProd hi]
  simp only [Kernel.prod_apply]
  apply integral_congr_ae
  have h1:=ae_all_iff.2 (fun i : Fin n=>
    vectorConditionalTerminalSpinKernel_first_moment μ β t a hβ ht q i)
  have h2:=ae_all_iff.2 (fun i : Fin n=>ae_all_iff.2 (fun j : Fin n=>
    vectorConditionalTerminalSpinKernel_second_moment μ β t a ht.le q i j))
  filter_upwards [h1,h2] with z hz1 hz2
  rw [integral_overlap_defect_spin_product]
  dsimp only [vectorConditionalReplicaMatrixDefect]
  simp_rw [hz1,hz2]

end QuantitativePaper
