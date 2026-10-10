module
public import QuantitativePaper.VectorMeasureMatrixOrder

@[expose] public section

/-! Exact conditional covariance trace and Hessian-square trace identities
for the actual arbitrary-profile vector process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1400000
variable {n : ℕ}

theorem vectorMeasureSpinCovariance_diagonal (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    vectorMeasureSpinCovariance μ β t a ht q sample i i=
      1-(vectorMeasureSpinMean μ β t ht q sample i)^2 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have he : vectorMeasureTerminalObservable μ β t ht
      (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ i))=
      (fun _ : VectorDisorderBrownianSample n=>(1 : ℝ)) := by
    funext sample
    unfold vectorMeasureTerminalObservable
    simp only [←pow_two,Paper.spinSign_sq,terminalMean_const]
  unfold vectorMeasureSpinCovariance
  rw [he,condExp_const ((vectorBrownianFiltration n).le _)]
  ring

theorem vectorMeasureSpinCovariance_trace (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample)=
      (n : ℝ)-‖vectorMeasureSpinMean μ β t ht q sample‖^2 := by
  simp only [Matrix.trace,Matrix.diag,vectorMeasureSpinCovariance_diagonal,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,EuclideanSpace.real_norm_sq_eq]

theorem integral_vectorMeasureSpinCovariance_trace (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    (∫sample,Matrix.trace (vectorMeasureSpinCovariance (n:=n) μ β t a ht q sample)
      ∂vectorMeasureDisorderTilt μ β t a)=
      (n : ℝ)*(1-vectorMeanOverlap (n:=n) μ β t a ht q) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hi (i : Fin n) : Integrable (fun sample=>(vectorMeasureSpinMean μ β t ht q sample i)^2)
      (vectorMeasureDisorderTilt μ β t a) := by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht q q i
  simp_rw [vectorMeasureSpinCovariance_trace,EuclideanSpace.real_norm_sq_eq]
  rw [integral_sub (integrable_const _) (integrable_finsetSum _ fun i _=>hi i),
    integral_const,probReal_univ,one_smul,integral_finsetSum _ fun i _=>hi i]
  unfold vectorMeanOverlap
  by_cases hn : n=0
  · subst n
    simp
  · have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
    field_simp

theorem vectorMeasureHessianMatrix_trace_square (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Matrix.trace (vectorMeasureHessianMatrix μ β t ht q sample*
      vectorMeasureHessianMatrix μ β t ht q sample)=
      vectorHessianHilbertSquare (vectorMeasureHessian μ β t q sample.1
        (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  simp_rw [vectorMeasureHessianMatrix_symmetric μ β t ht q sample,
    ←pow_two]
  unfold vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_comm]
  rfl

end QuantitativePaper
