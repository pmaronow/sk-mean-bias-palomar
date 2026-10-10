module
public import QuantitativePaper.VectorFutureCovarianceCorrection
public import QuantitativePaper.VectorConditionalVariance
public import FourPapersCommon.FiniteStateCascadePropagation

@[expose] public section

/-! Actual normalized future kernels and conditional covariance tests for
the finite vector recursion, in depth rather than chronological coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def vectorDepthKernel {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    Kernel (VectorState n) (VectorState n) :=
  vectorStateKernel ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    (fun p x => vectorRecursion s β t p j x)

instance vectorDepthKernel_markov {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    IsMarkovKernel (vectorDepthKernel (n:=n) s β t j) :=
  isMarkovKernel_vectorStateKernel _ (measurable_vectorRecursion s β t j)
    (Real.sqrt (n:ℝ)).toNNReal (fun p => vectorRecursion_lipschitz s β t p j) _ _

def vectorDepthCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (b : Configuration n → ℝ) (j : ℕ) (x : VectorState n) : ℝ :=
  vectorObservableCovariance s β t x.1 b j 0 x.2

theorem measurable_vectorDepthCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (b : Configuration n → ℝ) (j : ℕ) : Measurable (vectorDepthCovariance s β t b j) := by
  have he : vectorDepthCovariance s β t b j = fun x : VectorState n =>
      vectorConditionalMean s β t x.1 (fun _ => 0) (fun σ => b σ^2) j 0 x.2 -
        (vectorConditionalMean s β t x.1 (fun _ => 0) b j 0 x.2)^2 := by
    funext x
    unfold vectorDepthCovariance vectorObservableCovariance
    rw [vectorConditionalMean_zero_independent_tilt]
    rw [←vectorConditionalMean_self,
      vectorConditionalMean_zero_independent_tilt s β t x.1 b b j x.2]
  rw [he]
  exact (measurable_vectorConditionalMean_state_zero s β t _ j).sub
    ((measurable_vectorConditionalMean_state_zero s β t b j).pow_const 2)

theorem vectorDepthCovariance_abs_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (b : Configuration n → ℝ) (R : ℝ≥0) (hb : ∀σ, |b σ| ≤ R) (j : ℕ)
    (x : VectorState n) : |vectorDepthCovariance s β t b j x| ≤ (R:ℝ)^2 :=
  abs_vectorObservableCovariance_le s β t x.1 b R hb j 0 x.2

def vectorFutureCovarianceKernelSum {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (b : Configuration n → ℝ) (j : ℕ) (x : VectorState n) : ℝ :=
  ∑p ∈ Finset.range j, (observableDepthMass s p - observableDepthMass s (p+1)) *
    sourceKernelExpectation (fun u => vectorDepthKernel s β t (p+u)) (j-p)
      (vectorDepthCovariance s β t b p) x

theorem measurable_vectorFutureCovarianceKernelSum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    Measurable (vectorFutureCovarianceKernelSum s β t b j) :=
  Finset.measurable_sum _ (fun p _ =>
    (sourceKernelExpectation_measurable _ _ (measurable_vectorDepthCovariance s β t b p) _).const_mul _)

theorem vectorFutureCovarianceKernelSum_step {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (b : Configuration n → ℝ) (R : ℝ≥0) (hb : ∀σ, |b σ| ≤ R)
    (j : ℕ) (x : VectorState n) :
    vectorFutureCovarianceKernelSum s β t b (j+1) x =
      ∫y, (observableDepthMass s j - observableDepthMass s (j+1)) *
        vectorDepthCovariance s β t b j y + vectorFutureCovarianceKernelSum s β t b j y
        ∂vectorDepthKernel s β t j x := by
  let K := vectorDepthKernel (n:=n) s β t
  let C := vectorDepthCovariance s β t b
  let a := observableDepthMass s
  let T := fun p y => sourceKernelExpectation (fun u => K (p+u)) (j-p) (C p) y
  have hT (p : ℕ) : Measurable (T p) :=
    sourceKernelExpectation_measurable _ _ (measurable_vectorDepthCovariance s β t b p) _
  have hbT (p : ℕ) (y) : |T p y| ≤ (R:ℝ)^2 :=
    sourceKernelExpectation_abs_le _ (fun _ => inferInstance) _
      (measurable_vectorDepthCovariance s β t b p) _ (sq_nonneg _)
      (vectorDepthCovariance_abs_le s β t b R hb p) _ y
  have hi (p : ℕ) : Integrable (fun y => (a p-a (p+1))*T p y) (K j x) :=
    (source_bounded_integrable _ _ (hT p) _ (hbT p)).const_mul _
  have hCj : Integrable (fun y => (a j-a (j+1))*C j y) (K j x) :=
    (source_bounded_integrable _ _ (measurable_vectorDepthCovariance s β t b j) _
      (vectorDepthCovariance_abs_le s β t b R hb j)).const_mul _
  have hSum : Integrable (fun y => ∑p ∈ Finset.range j, (a p-a (p+1))*T p y) (K j x) :=
    integrable_finsetSum _ (fun p _ => hi p)
  change (∑p ∈ Finset.range (j+1), (a p-a (p+1))*
    sourceKernelExpectation (fun u => K (p+u)) (j+1-p) (C p) x) =
      ∫y, (a j-a (j+1))*C j y + ∑p ∈ Finset.range j, (a p-a (p+1))*T p y ∂K j x
  rw [integral_add hCj hSum, integral_const_mul, integral_finsetSum _ (fun p _ => hi p),
    Finset.sum_range_succ]
  have hlast : sourceKernelExpectation (fun u => K (j+u)) (j+1-j) (C j) x = ∫y, C j y ∂K j x := by
    simp only [show j+1-j=1 by omega, sourceKernelExpectation, add_zero]
  rw [hlast, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_const_mul]
  have hj : j+1-p=(j-p)+1 := by have := Finset.mem_range.mp hp; omega
  have hpj : p+(j-p)=j := by have := Finset.mem_range.mp hp; omega
  simp only [hj, sourceKernelExpectation, hpj, T]

end QuantitativePaper
