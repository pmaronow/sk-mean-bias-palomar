module
public import FourPapersCommon.FiniteStateCascadeTraceDecomposition

@[expose] public section

/-! Exact covariance telescope. Its linear functionals are integrals under
actual cascade probability laws, so the cancellation carries no assumed
replica expectation or interpolation identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1400000

private theorem sum_range_cutoff {j n : ℕ} (h : j ≤ n) (f : ℕ → ℝ) :
    (∑ p ∈ Finset.range j, f p) = ∑ p ∈ Finset.range n, if p < j then f p else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem sum_range_triangle (n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range n, ∑ p ∈ Finset.range j, f p j) =
      ∑ p ∈ Finset.range n, ∑ j ∈ Finset.range n, if p < j then f p j else 0 := by
  classical
  calc
    _ = ∑ j ∈ Finset.range n, ∑ p ∈ Finset.range n, if p < j then f p j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_range_cutoff (Finset.mem_range.mp hj).le _
    _ = _ := Finset.sum_comm

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def cascadeCovarianceResponseLinear (D : E →ₗ[ℝ] ℝ) (P : ℕ → E →ₗ[ℝ] ℝ)
    (a : ℕ → ℝ) (j : ℕ) : E →ₗ[ℝ] ℝ :=
  D + (a 0-1) • P 0 + ∑ p ∈ Finset.range j, (a (p+1)-a p) • P (p+1)

def cascadeCovarianceGap (C : E) (G : ℕ → E) (n p : ℕ) : E :=
  C - ∑ j ∈ Finset.range n, if p ≤ j then G j else 0

theorem cascadeCovarianceResponse_telescope (D : E →ₗ[ℝ] ℝ)
    (P : ℕ → E →ₗ[ℝ] ℝ) (a : ℕ → ℝ) (n : ℕ) (C : E) (G : ℕ → E) :
    cascadeCovarianceResponseLinear D P a n C -
      ∑ j ∈ Finset.range n, cascadeCovarianceResponseLinear D P a j (G j) =
    D (cascadeCovarianceGap C G n 0) +
      (a 0-1)*P 0 (cascadeCovarianceGap C G n 0) +
      ∑ p ∈ Finset.range n, (a (p+1)-a p)*P (p+1) (cascadeCovarianceGap C G n (p+1)) := by
  classical
  simp only [cascadeCovarianceResponseLinear, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, cascadeCovarianceGap, map_sub, map_sum,
    Nat.zero_le, ite_true]
  simp_rw [apply_ite, map_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_range_triangle]
  simp only [Nat.add_one_le_iff]
  have hs : (∑ p ∈ Finset.range n, (a (p+1)-a p) *
      (P (p+1) C - ∑ j ∈ Finset.range n, if p < j then P (p+1) (G j) else 0)) =
      (∑ p ∈ Finset.range n, (a (p+1)-a p)*P (p+1) C) -
        ∑ p ∈ Finset.range n, ∑ j ∈ Finset.range n,
          if p < j then (a (p+1)-a p)*P (p+1) (G j) else 0 := by
    simp_rw [mul_sub, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
  rw [hs]
  ring
end Algebra

variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteStateCascadeDiagonalLinear (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n : ℕ) (H : FiniteStateField S) : (S → S → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun C => finiteStateCascadeDiagonalMoment V a L n H C
  map_add' := fun C G => by
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L n
    exact integral_add Integrable.of_finite Integrable.of_finite
  map_smul' := fun c C => integral_const_mul c _

def finiteStateCascadePairLinear (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n p : ℕ) (H : FiniteStateField S) : (S → S → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun C => finiteStateCascadeCovarianceMoment V a L p (n-p) H C
  map_add' := fun C G => by
    haveI := isProbabilityMeasure_finiteStateCascadeSplitLaw V a ha L p (n-p) H
    exact integral_add Integrable.of_finite Integrable.of_finite
  map_smul' := fun c C => integral_const_mul c _

theorem finiteStateCascade_covariance_telescope (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n : ℕ) (H : FiniteStateField S) (C : S → S → ℝ) (G : ℕ → S → S → ℝ) :
    cascadeCovarianceResponseLinear (finiteStateCascadeDiagonalLinear V a ha L n H)
        (fun p => finiteStateCascadePairLinear V a ha L n p H) a n C -
      ∑ j ∈ Finset.range n,
        cascadeCovarianceResponseLinear (finiteStateCascadeDiagonalLinear V a ha L n H)
          (fun p => finiteStateCascadePairLinear V a ha L n p H) a j (G j) =
    finiteStateCascadeDiagonalMoment V a L n H (cascadeCovarianceGap C G n 0) +
      (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 n H (cascadeCovarianceGap C G n 0) +
      ∑ p ∈ Finset.range n, (a (p+1)-a p)*
        finiteStateCascadeCovarianceMoment V a L (p+1) (n-(p+1)) H (cascadeCovarianceGap C G n (p+1)) := by
  exact cascadeCovarianceResponse_telescope _ _ _ _ _ _

end FourPapersCommon
