module
public import QuantitativePaper.VectorDyadicUniformResponseHessian
public import QuantitativePaper.VectorDyadicUniformResponseTilt
public import QuantitativePaper.VectorMeanHessianTrace

@[expose] public section

/-! The literal physical response observables converge uniformly over the
whole overlap interval under the genuine varying dyadic profile laws. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem abs_responseHessianTrace_sub_le (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    |responseHessianTrace μ β t ht q sample-responseHessianTrace ν β t ht q sample| ≤
      (|β| *(n : ℝ))*‖vectorMeasureHessianProcess μ β t ht q sample-
        vectorMeasureHessianProcess ν β t ht q sample‖ := by
  unfold responseHessianTrace Matrix.trace Matrix.diag vectorMeasureHessianMatrix
  rw [← mul_sub,abs_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, |(vectorMeasureHessianProcess μ β t ht q sample (EuclideanSpace.single i 1)) i-
        (vectorMeasureHessianProcess ν β t ht q sample (EuclideanSpace.single i 1)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖vectorMeasureHessianProcess μ β t ht q sample-
        vectorMeasureHessianProcess ν β t ht q sample‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs,ContinuousLinearMap.sub_apply,PiLp.sub_apply] using
        norm_operator_diagonal_le (vectorMeasureHessianProcess μ β t ht q sample-
          vectorMeasureHessianProcess ν β t ht q sample) i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem tendstoUniformly_vectorDyadicResponseTrace (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformly (fun j (z : Paper.Overlap × VectorDisorderBrownianSample n) =>
      responseHessianTrace (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2)
      (fun z => responseHessianTrace μ β t ht z.1 z.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let C := |β| *(n : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ := ε/(C+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hu := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicGridHessianProcess (n := n) μ β t ht)) δ hδ
  filter_upwards [hu] with j hj
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  have hb := abs_responseHessianTrace_sub_le (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) μ β t ht z.1 z.2
  have hh : ‖vectorMeasureHessianProcess (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2-
      vectorMeasureHessianProcess μ β t ht z.1 z.2‖ ≤ δ := by
    simpa only [dist_eq_norm,norm_sub_rev] using (hj z).le
  apply (hb.trans (mul_le_mul_of_nonneg_left hh hC)).trans_lt
  dsimp only [C,δ]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

theorem tendstoUniformly_vectorDyadicResponseEnergy (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformly (fun j (z : Paper.Overlap × VectorDisorderBrownianSample n) =>
      vectorMeasureHessianEnergy (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2)
      (fun z => vectorMeasureHessianEnergy μ β t ht z.1 z.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let C := 2*(n : ℝ)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ := ε/(C+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hu := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicGridHessianProcess (n := n) μ β t ht)) δ hδ
  filter_upwards [hu] with j hj
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  have hb := abs_vectorHessianHilbertSquare_sub_le
    (vectorMeasureHessianProcess (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2)
    (vectorMeasureHessianProcess μ β t ht z.1 z.2)
    (norm_vectorMeasureHessianProcess_le _ β t ht z.1 z.2)
    (norm_vectorMeasureHessianProcess_le μ β t ht z.1 z.2)
  have hh : ‖vectorMeasureHessianProcess (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2-
      vectorMeasureHessianProcess μ β t ht z.1 z.2‖ ≤ δ := by
    simpa only [dist_eq_norm,norm_sub_rev] using (hj z).le
  apply (hb.trans (mul_le_mul_of_nonneg_left hh hC)).trans_lt
  dsimp only [C,δ]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

theorem tendstoUniformly_responseMeanHessian_grid (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t ≤ 1) :
    TendstoUniformly (fun j q => responseMeanHessian (n := n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q)
      (responseMeanHessian (n := n) μ β t lam ht) atTop := by
  have h := tendstoUniformly_integral_vectorDyadicGridTilt_bounded μ β t (lam/β) ht
    (fun j q => responseHessianTrace (n := n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht q)
    (responseHessianTrace (n := n) μ β t ht) (|β| *(n : ℝ)^2) (by positivity)
    (fun j q => measurable_responseHessianTrace _ β t ht q)
    (measurable_responseHessianTrace μ β t ht)
    (fun j q sample => by simpa only [Real.norm_eq_abs] using abs_responseHessianTrace_le _ β t ht q sample)
    (fun q sample => by simpa only [Real.norm_eq_abs] using abs_responseHessianTrace_le μ β t ht q sample)
    (tendstoUniformly_vectorDyadicResponseTrace μ β t ht)
  let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ (1/(n : ℝ))
  change TendstoUniformly _ (fun q => (1/(n : ℝ))*∫sample,responseHessianTrace μ β t ht q sample
    ∂vectorMeasureDisorderTilt μ β t (lam/β)) atTop
  simpa only [L,ContinuousLinearMap.lsmul_apply,smul_eq_mul,Function.comp_def,responseMeanHessian] using
    L.uniformContinuous.comp_tendstoUniformly h

theorem tendstoUniformly_responseAveragedCurvature_grid (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t ≤ 1) :
    TendstoUniformly (fun j q => responseAveragedCurvature (n := n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q)
      (responseAveragedCurvature (n := n) μ β t lam ht) atTop := by
  have h := tendstoUniformly_integral_vectorDyadicGridTilt_bounded μ β t (lam/β) ht
    (fun j q => vectorMeasureHessianEnergy (n := n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht q)
    (vectorMeasureHessianEnergy (n := n) μ β t ht) ((n : ℝ)^3) (by positivity)
    (fun j q => measurable_vectorMeasureHessianEnergy _ β t ht q)
    (measurable_vectorMeasureHessianEnergy μ β t ht)
    (fun j q sample => by rw [Real.norm_eq_abs,abs_of_nonneg (vectorMeasureHessianEnergy_nonneg_le _ β t ht q sample).1]; exact (vectorMeasureHessianEnergy_nonneg_le _ β t ht q sample).2)
    (fun q sample => by rw [Real.norm_eq_abs,abs_of_nonneg (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1]; exact (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2)
    (tendstoUniformly_vectorDyadicResponseEnergy μ β t ht)
  let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ (β^2/(n : ℝ))
  change TendstoUniformly _ (fun q => (β^2/(n : ℝ))*∫sample,vectorMeasureHessianEnergy μ β t ht q sample
    ∂vectorMeasureDisorderTilt μ β t (lam/β)) atTop
  simpa only [L,ContinuousLinearMap.lsmul_apply,smul_eq_mul,Function.comp_def,responseAveragedCurvature] using
    L.uniformContinuous.comp_tendstoUniformly h

end QuantitativePaper
