module
public import QuantitativePaper.ResponseMeanUpper
public import QuantitativeFollowup.FoundationContinuousDerivative
public import QuantitativeFollowup.VectorMeanMartingale

@[expose] public section

/-! Sharp diagonal/trace bounds from the genuine conditional-spin covariance
sandwich. Every expectation uses the actual arbitrary-profile tilted law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Matrix Paper
open scoped BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem vectorMeasureHessianMatrix_diagonal_mem_unit (μ : ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      ∀i : Fin n, vectorMeasureHessianMatrix μ β t ht.le q sample i i ∈ Icc (0:ℝ) 1 := by
  filter_upwards [vectorMeasure_matrix_order (n:=n) μ β t a hβ ht q] with sample hs
  intro i
  have hl:= (vectorMeasureHessianMatrix_posSemidef μ β t ht.le q sample).diag_nonneg (i:=i)
  have hu:=hs.2.2.diag_nonneg (i:=i)
  simp only [Matrix.sub_apply,vectorMeasureSpinCovariance_diagonal] at hu
  exact ⟨hl,by nlinarith [sq_nonneg (vectorMeasureSpinMean μ β t ht.le q sample i)]⟩

theorem vectorMeasureHessianMatrix_trace_mem_dimension (μ : ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q sample) ∈ Icc (0:ℝ) (n:ℝ) := by
  filter_upwards [vectorMeasureHessianMatrix_diagonal_mem_unit μ β t a hβ ht q] with sample hs
  refine ⟨(vectorMeasureHessianMatrix_posSemidef μ β t ht.le q sample).trace_nonneg,?_⟩
  change (∑i : Fin n,vectorMeasureHessianMatrix μ β t ht.le q sample i i) ≤ (n:ℝ)
  calc
    _ ≤ ∑_i : Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _=>(hs i).2)
    _ = _ := by simp

/-- The sharp normalized mean response bound, with no minimizing-profile
or supplied trace-bound hypothesis. -/
theorem responseMeanHessian_le_beta (hn : 0<n) (μ : ParisiMeasure)
    (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (q : Overlap) :
    responseMeanHessian (n:=n) μ β t lam ht.le q ≤ β := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t (lam/β) ht.le
  have hi:Integrable (responseHessianTrace (n:=n) μ β t ht.le q)
      (vectorMeasureDisorderTilt μ β t (lam/β)) :=
    (memLp_responseHessianTrace μ β t lam ht.le q).integrable (by norm_num)
  have hp : (responseHessianTrace (n:=n) μ β t ht.le q) ≤ᵐ[vectorMeasureDisorderTilt μ β t (lam/β)]
      (fun _=>β*(n:ℝ)) := by
    filter_upwards [vectorMeasureHessianMatrix_trace_mem_dimension μ β t (lam/β) hβ.ne' ht q] with sample hs
    exact mul_le_mul_of_nonneg_left hs.2 hβ.le
  have hh:=integral_mono_ae hi (integrable_const (β*(n:ℝ))) hp
  rw [integral_const,probReal_univ,one_smul] at hh
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  unfold responseMeanHessian
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤1/(n:ℝ))).trans_eq
  field_simp

/-- Literal follow-up `eq:loc-b`: actual mean-overlap/curvature normalization,
unit bounds and sharp mean-response bound, including physical endpoints. -/
theorem localization_response_basics (hn : 0<n) (μ : ParisiMeasure)
    (β rho lam : ℝ) (hβ : 0<β) (hrho : 0<rho) :
    vectorMeanOverlap (n:=n) μ β (1-rho) (lam/β) (by linarith) 0=0 ∧
    ∀q : Overlap,
      vectorMeanOverlap (n:=n) μ β (1-rho) (lam/β) (by linarith) q ∈ Icc (0:ℝ) 1 ∧
      HasDerivAt (vectorMeanOverlapPrimitive (n:=n) μ β (1-rho) (lam/β) (by linarith))
        (rho*responseAveragedCurvature (n:=n) μ β (1-rho) lam (by linarith) q) (q:ℝ) ∧
      0≤rho*responseAveragedCurvature (n:=n) μ β (1-rho) lam (by linarith) q ∧
      responseMeanHessian (n:=n) μ β (1-rho) lam (by linarith) q ∈ Icc (0:ℝ) β := by
  have ht : 1-rho<1 := by linarith
  refine ⟨vectorMeanOverlap_zero μ β (1-rho) (lam/β) ht.le,?_⟩
  intro q
  have hd:=hasDerivAt_vectorMeanOverlapPrimitive (n:=n) μ β (1-rho) (lam/β) ht.le (q:ℝ)
  rw [projIcc_of_mem zero_le_one q.property,vectorMeanOverlapDerivative_eq_responseCurvature] at hd
  have hd0:=vectorMeanOverlapDerivative_nonneg (n:=n) μ β (1-rho) (lam/β) ht.le q
  rw [vectorMeanOverlapDerivative_eq_responseCurvature] at hd0
  have he : 1-(1-rho)=rho := by ring
  rw [he] at hd hd0
  exact ⟨vectorMeanOverlap_nonneg_le_one μ β (1-rho) (lam/β) ht.le q,hd,hd0,
    responseMeanHessian_nonneg μ β (1-rho) lam hβ.le ht.le q,
    responseMeanHessian_le_beta hn μ β (1-rho) lam hβ ht q⟩

end QuantitativePaper
