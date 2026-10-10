module
public import QuantitativeFollowup.FollowupCavitySignedResponseHessianOrder
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureHessianIntegral

@[expose] public section

/-! Actual diagonal covariance/Hessian trace moments used in T3. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem measurable_uncurry_cavityHessianEntry (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i j : Fin n) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      nativeAnisotropicProcessHessianMatrix D μ z.1 z.2 i j) := by
  simp_rw [nativeAnisotropicProcessHessianMatrix_polarization]
  exact ((measurable_uncurry_nativeAnisotropicProcessDirectionalHessian D μ
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1)).sub
      (measurable_uncurry_nativeAnisotropicProcessDirectionalHessian D μ
        (EuclideanSpace.single i 1-EuclideanSpace.single j 1))).div_const 4

theorem measurable_uncurry_cavityCovarianceEntry (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i j : Fin n) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicProcessSpinCovariance D μ z.1 z.2 i j) := by
  have hP : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (z.1,anisotropicProcessParameter D μ z.1 z.2)) :=
    measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ)
  have hm (w : Field n) : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicTailCovarianceQuadratic D μ z.1 (anisotropicProcessParameter D μ z.1 z.2) w) := by
    have h := (continuous_anisotropicTailCovarianceQuadratic_joint D μ).measurable.comp
      (hP.prodMk (measurable_const (a:=w)))
    dsimp only [Function.comp_def] at h
    exact h
  simp_rw [nativeAnisotropicCovarianceMatrix_polarization]
  exact ((hm (EuclideanSpace.single i 1+EuclideanSpace.single j 1)).sub
    (hm (EuclideanSpace.single i 1-EuclideanSpace.single j 1))).div_const 4

theorem measurable_uncurry_cavityHessianSquareTrace (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ z.1 z.2*
        nativeAnisotropicProcessHessianMatrix D μ z.1 z.2)) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
    (measurable_uncurry_cavityHessianEntry D μ i j).mul (measurable_uncurry_cavityHessianEntry D μ j i)

theorem measurable_uncurry_cavityCovarianceSquareTrace (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      Matrix.trace (anisotropicProcessSpinCovariance D μ z.1 z.2*anisotropicProcessSpinCovariance D μ z.1 z.2)) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
    (measurable_uncurry_cavityCovarianceEntry D μ i j).mul (measurable_uncurry_cavityCovarianceEntry D μ j i)

theorem norm_cavityCovarianceSquareTrace_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖Matrix.trace (anisotropicProcessSpinCovariance D μ q sample*anisotropicProcessSpinCovariance D μ q sample)‖≤4*(n:ℝ)^2 := by
  let C := anisotropicProcessSpinCovariance D μ q sample
  change ‖∑i : Fin n,∑j : Fin n,C i j*C j i‖≤_
  calc
    _≤∑i : Fin n,∑j : Fin n,‖C i j*C j i‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>norm_sum_le _ _)
    _≤∑i : Fin n,∑j : Fin n,(4:ℝ) := Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>by
      rw [norm_mul]
      exact (mul_le_mul (anisotropicTailSpinCovariance_entry_bound D μ q _ i j)
        (anisotropicTailSpinCovariance_entry_bound D μ q _ j i) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    _=_ := by simp;ring

theorem norm_cavityHessianSquareTrace_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ q sample*nativeAnisotropicProcessHessianMatrix D μ q sample)‖≤4*(n:ℝ)^2 := by
  have h := cavitySignedResponse_Hessian_trace_order D μ q sample
  rw [Real.norm_of_nonneg h.1]
  exact ((h.2.1.trans h.2.2).trans (le_abs_self _)).trans
    (by simpa only [Real.norm_eq_abs] using norm_cavityCovarianceSquareTrace_le D μ q sample)

def cavitySignedResponseCovarianceTraceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) : ℝ :=
  (∫sample,Matrix.trace (anisotropicProcessSpinCovariance D μ q sample*anisotropicProcessSpinCovariance D μ q sample)
    ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)^2

def cavitySignedResponseHessianTraceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) : ℝ :=
  (∫sample,Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ q sample*nativeAnisotropicProcessHessianMatrix D μ q sample)
    ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)^2

theorem measurable_cavitySignedResponseCovarianceTraceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Measurable (cavitySignedResponseCovarianceTraceMoment D μ a) :=
  ((measurable_uncurry_cavityCovarianceSquareTrace D μ).stronglyMeasurable.integral_prod_right'
    (ν:=anisotropicMeasureSampleLaw D μ a)).measurable.div_const _

theorem measurable_cavitySignedResponseHessianTraceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Measurable (cavitySignedResponseHessianTraceMoment D μ a) :=
  ((measurable_uncurry_cavityHessianSquareTrace D μ).stronglyMeasurable.integral_prod_right'
    (ν:=anisotropicMeasureSampleLaw D μ a)).measurable.div_const _

theorem cavitySignedResponseHessianTraceMoment_bounds (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    0≤cavitySignedResponseHessianTraceMoment D μ a q ∧
      cavitySignedResponseHessianTraceMoment D μ a q≤cavitySignedResponseCovarianceTraceMoment D μ a q := by
  have h := fun sample=>cavitySignedResponse_Hessian_trace_order D μ q sample
  have hmC : Measurable (fun sample=>Matrix.trace (anisotropicProcessSpinCovariance D μ q sample*anisotropicProcessSpinCovariance D μ q sample)) := by
    have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(q,sample)) := measurable_const.prodMk measurable_id
    have h := (measurable_uncurry_cavityCovarianceSquareTrace D μ).comp hmap
    dsimp only [Function.comp_def] at h
    exact h
  have hmH : Measurable (fun sample=>Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ q sample*nativeAnisotropicProcessHessianMatrix D μ q sample)) := by
    have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(q,sample)) := measurable_const.prodMk measurable_id
    have h := (measurable_uncurry_cavityHessianSquareTrace D μ).comp hmap
    dsimp only [Function.comp_def] at h
    exact h
  have hiC : Integrable (fun sample=>Matrix.trace (anisotropicProcessSpinCovariance D μ q sample*anisotropicProcessSpinCovariance D μ q sample))
      (anisotropicMeasureSampleLaw D μ a) := bounded_real_integrable _ hmC _ (norm_cavityCovarianceSquareTrace_le D μ q)
  have hiH : Integrable (fun sample=>Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ q sample*nativeAnisotropicProcessHessianMatrix D μ q sample))
      (anisotropicMeasureSampleLaw D μ a) := bounded_real_integrable _ hmH _ (norm_cavityHessianSquareTrace_le D μ q)
  refine ⟨div_nonneg (integral_nonneg fun sample=>(h sample).1) (sq_nonneg _),?_⟩
  exact div_le_div_of_nonneg_right (integral_mono hiH hiC fun sample=>(h sample).2.1.trans (h sample).2.2) (sq_nonneg _)

theorem cavitySignedResponseCovarianceTraceMoment_bounds (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    0≤cavitySignedResponseCovarianceTraceMoment D μ a q ∧ cavitySignedResponseCovarianceTraceMoment D μ a q≤4 := by
  have h0 := (cavitySignedResponseHessianTraceMoment_bounds D μ a q).1.trans
    (cavitySignedResponseHessianTraceMoment_bounds D μ a q).2
  have hb := norm_integral_le_of_norm_le_const (μ:=anisotropicMeasureSampleLaw D μ a)
    (.of_forall (norm_cavityCovarianceSquareTrace_le D μ q))
  simp only [probReal_univ,mul_one] at hb
  unfold cavitySignedResponseCovarianceTraceMoment at h0 ⊢
  refine ⟨h0,?_⟩
  by_cases hn : n=0
  · simp [hn]
  · have hn0 : 0<(n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    apply (div_le_iff₀ hn0).mpr
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)

def cavitySignedResponseWeightedA (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) : ℝ :=
  ∫q,Gamma β0 μ q*cavitySignedResponseCovarianceTraceMoment D μ a q ∂parisiFreeMeasure μ a

end QuantitativeFollowup
