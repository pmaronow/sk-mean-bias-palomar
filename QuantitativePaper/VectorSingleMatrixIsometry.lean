module
public import QuantitativePaper.VectorMatrixBrownianSums

@[expose] public section

/-! The exact one-interval matrix Brownian isometry, including zero duration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem integral_tilted_bounded_matrix_increment_norm_sq
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (r q : ℝ≥0) (hrq : r≤q)
    (H : VectorDisorderBrownianSample n→(Field n→L[ℝ]Field n))
    (hH : Measurable[vectorBrownianFiltration n r] H) (K : ℝ≥0)
    (hK : ∀sample,‖H sample‖≤K) :
    (∫sample,‖H sample (disorderVectorBrownianIncrement r q sample)‖^2∂vectorMeasureDisorderTilt μ β t a)=
      ((q:ℝ)-r)*∫sample,vectorHessianHilbertSquare (H sample)∂vectorMeasureDisorderTilt μ β t a := by
  let T : Fin 2→ℝ≥0 := ![r,q]
  let A : Fin 1→VectorDisorderBrownianSample n→(Field n→L[ℝ]Field n) := fun _=>H
  have hT : Monotone T := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T]
  have h := integral_vectorMatrixBrownianSum_norm_sq μ β t a ht T hT A
    (fun i => by fin_cases i; exact hH) K (fun _=>hK)
  simpa only [vectorMatrixBrownianSum,T,A,Fin.sum_univ_one,Fin.castSucc_zero,Fin.succ_zero_eq_one,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using h

end QuantitativePaper
