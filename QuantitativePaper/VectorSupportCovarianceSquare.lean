module
public import QuantitativePaper.VectorSupportSlope
public import QuantitativePaper.VectorMeasureRandomReaction
public import QuantitativePaper.ScalarFloorContinuity

@[expose] public section

/-! The actual conditional covariance square bound at free support contact.
The matrix comparison and every integrability condition are proved for the
constructed joint law, rather than supplied as trace-order hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem integrable_vectorMeasureSpinCovariance_trace_square
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
        vectorMeasureSpinCovariance μ β t a ht q sample))
      (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hi (i j : Fin n) : Integrable (fun sample=>
      vectorMeasureSpinCovariance μ β t a ht q sample i j*
        vectorMeasureSpinCovariance μ β t a ht q sample j i)
      (vectorMeasureDisorderTilt μ β t a):=by
    apply (integrable_const (4 : ℝ)).mono'
      ((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).mul
        (measurable_vectorMeasureSpinCovariance_entry μ β t a ht q j i)).aestronglyMeasurable
    filter_upwards [vectorMeasureSpinCovariance_entry_bound μ β t a ht q] with sample hs
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (hs i j) (hs j i) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  exact integrable_finsetSum Finset.univ fun i _=>integrable_finsetSum Finset.univ fun j _=>hi i j

theorem vector_free_support_trace_covariance_square_bound
    (hn : 0<n) (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Ioo (0 : ℝ) 1)
    (hμ : μ∈scalarFloor s) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)
      ∂vectorMeasureDisorderTilt μ β t s)≤
        (n : ℝ)/(((1-t)*β^2)*(Paper.parisiCDF μ q)^2) := by
  let m:=Paper.parisiCDF μ q
  let c:=(1-t)*β^2
  have hm : 0 < m := hs.1.trans_le (scalarFloor_cdf_lower hμ q.property.1)
  have hc : 0 < c := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hpoint : ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t s,
      m^2*Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)≤
      Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q sample*
        vectorMeasureHessianMatrix μ β t ht.le q sample):=by
    filter_upwards [vectorMeasure_trace_covariance_order μ β t s hβ ht q] with sample h
    calc
      _ = m*(m*Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)):=by ring
      _ ≤ m*Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample):=
          mul_le_mul_of_nonneg_left h.2.2.1 hm.le
      _ ≤ _ := h.2.1
  have hC:=integrable_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t s ht.le q
  have hH : Integrable (fun sample : VectorDisorderBrownianSample n=>
      Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q sample*
        vectorMeasureHessianMatrix μ β t ht.le q sample))
      (vectorMeasureDisorderTilt μ β t s):=by
    simp_rw [vectorMeasureHessianMatrix_trace_square]
    exact integrable_vectorMeasureHessianEnergy μ β t s ht.le q
  have hi:=integral_mono_ae (hC.const_mul (m^2)) hH hpoint
  rw [integral_const_mul] at hi
  have he:=vector_free_support_trace_hessian_square_bound hn μ s ⟨hs.1.le,hs.2⟩
    hμ β t s hβ ht hs.1.le hmin q hq
  have hfinal : m^2*(∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)
      ∂vectorMeasureDisorderTilt μ β t s)≤(n : ℝ)/c:=hi.trans he
  apply (le_div_iff₀ (mul_pos hc (sq_pos_of_pos hm))).mpr
  have hx:=mul_le_mul_of_nonneg_left hfinal hc.le
  rw [mul_div_cancel₀ _ hc.ne'] at hx
  nlinarith [hx]

end QuantitativePaper
