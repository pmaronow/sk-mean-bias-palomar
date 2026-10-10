module
public import FourPapersCommon.FiniteStateCascadeResponses
public import FourPapersCommon.FiniteStateCascadeCovarianceAlgebra

@[expose] public section

/-! Actual disorder-minus-auxiliary Gaussian covariance telescope. Each
response is a propagated genuine Hessian/gradient-square expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1800000

theorem finiteStateCascadeCovarianceResponse_eq_linear (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n j : ℕ) (hj : j ≤ n) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L j (n-j) H A =
      cascadeCovarianceResponseLinear (finiteStateCascadeDiagonalLinear V a ha L n H)
        (fun p => finiteStateCascadePairLinear V a ha L n p H) a j (finiteStateSpectralCovariance A) := by
  rw [finiteStateCascadeCovarianceResponse_eq_split_moments V a ha L,
    Nat.add_sub_of_le hj]
  simp only [cascadeCovarianceResponseLinear, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, finiteStateCascadeDiagonalLinear,
    finiteStateCascadePairLinear, LinearMap.coe_mk, AddHom.coe_mk, Nat.sub_zero]
  rfl

theorem finiteStateCascadeHessian_trace_covariance_telescope (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n : ℕ) (han : a n = 0) (H : FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateHessianTrace M (finiteStateGaussianTerminalCascade V a L n) H -
      ∑ j ∈ Finset.range n, finiteStateCascadeCovarianceResponse V a L j (n-j) H (A j) =
    finiteStateCascadeDiagonalMoment V a L n H
        (cascadeCovarianceGap (finiteStateSpectralCovariance M) (fun j => finiteStateSpectralCovariance (A j)) n 0) +
      (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 n H
        (cascadeCovarianceGap (finiteStateSpectralCovariance M) (fun j => finiteStateSpectralCovariance (A j)) n 0) +
      ∑ p ∈ Finset.range n, (a (p+1)-a p)*finiteStateCascadeCovarianceMoment V a L (p+1) (n-(p+1)) H
        (cascadeCovarianceGap (finiteStateSpectralCovariance M) (fun j => finiteStateSpectralCovariance (A j)) n (p+1)) := by
  have hz := finiteStateCascadeCovarianceResponse_eq_kernelExpectation V a ha L n 0 H M
  simp only [sourceKernelExpectation, han, zero_mul, add_zero] at hz
  rw [← hz]
  have hn := finiteStateCascadeCovarianceResponse_eq_linear V a ha L n n le_rfl H M
  simp only [Nat.sub_self] at hn
  rw [hn]
  have hs : (∑ j ∈ Finset.range n, finiteStateCascadeCovarianceResponse V a L j (n-j) H (A j)) =
      ∑ j ∈ Finset.range n,
        cascadeCovarianceResponseLinear (finiteStateCascadeDiagonalLinear V a ha L n H)
          (fun p => finiteStateCascadePairLinear V a ha L n p H) a j (finiteStateSpectralCovariance (A j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact finiteStateCascadeCovarianceResponse_eq_linear V a ha L n j (Finset.mem_range.mp hj).le H (A j)
  rw [hs]
  exact finiteStateCascade_covariance_telescope V a ha L n H _ _

private theorem weighted_theta_telescope (a θ : ℕ → ℝ) (n : ℕ) :
    -a 0*θ 0 + (∑ p ∈ Finset.range n, (a p-a (p+1))*θ (p+1)) =
      -a n*θ n - ∑ p ∈ Finset.range n, a p*(θ p-θ (p+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem finiteStateCascadeHessian_covariance_upper_bound (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (n : ℕ) (han : a n = 0) (ha0 : a 0 ≤ 1)
    (hanti : ∀ j < n, a (j+1) ≤ a j) (H : FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (δ : ℝ) (θ : ℕ → ℝ)
    (hself : ∀ σ, cascadeCovarianceGap (finiteStateSpectralCovariance M)
      (fun j => finiteStateSpectralCovariance (A j)) n 0 σ σ ≤ δ-θ 0)
    (hpair : ∀ p ≤ n, ∀ σ τ, -θ p ≤ cascadeCovarianceGap (finiteStateSpectralCovariance M)
      (fun j => finiteStateSpectralCovariance (A j)) n p σ τ) :
    finiteStateHessianTrace M (finiteStateGaussianTerminalCascade V a L n) H -
      ∑ j ∈ Finset.range n, finiteStateCascadeCovarianceResponse V a L j (n-j) H (A j) ≤
      δ - ∑ p ∈ Finset.range n, a p*(θ p-θ (p+1)) := by
  let C := finiteStateSpectralCovariance M
  let G := fun j => finiteStateSpectralCovariance (A j)
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L n
  have hdiag : finiteStateCascadeDiagonalMoment V a L n H (cascadeCovarianceGap C G n 0) ≤ δ-θ 0 := by
    calc
      _ ≤ ∫ _ : S, δ-θ 0 ∂finiteStateCascadeGibbsKernel V a L n H :=
        integral_mono Integrable.of_finite (integrable_const _) hself
      _ = _ := by simp
  have hp (p : ℕ) (hp : p ≤ n) : -θ p ≤
      finiteStateCascadeCovarianceMoment V a L p (n-p) H (cascadeCovarianceGap C G n p) := by
    haveI := isProbabilityMeasure_finiteStateCascadeSplitLaw V a ha L p (n-p) H
    calc
      _ = ∫ _ : S × S, -θ p ∂finiteStateCascadeSplitLaw V a L p (n-p) H := by simp
      _ ≤ _ := integral_mono (integrable_const _) Integrable.of_finite (fun z => hpair p hp z.1 z.2)
  have hzero : (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 n H (cascadeCovarianceGap C G n 0) ≤
      (1-a 0)*θ 0 := by
    have hh := mul_le_mul_of_nonpos_left (hp 0 (Nat.zero_le n)) (sub_nonpos.mpr ha0)
    simpa only [Nat.sub_zero] using hh.trans_eq (by ring)
  have hsum : (∑ p ∈ Finset.range n, (a (p+1)-a p)*
        finiteStateCascadeCovarianceMoment V a L (p+1) (n-(p+1)) H (cascadeCovarianceGap C G n (p+1))) ≤
      ∑ p ∈ Finset.range n, (a p-a (p+1))*θ (p+1) := by
    apply Finset.sum_le_sum
    intro p hp'
    have hpn := Finset.mem_range.mp hp'
    have hh := mul_le_mul_of_nonpos_left (hp (p+1) (by omega)) (sub_nonpos.mpr (hanti p hpn))
    exact hh.trans_eq (by ring)
  rw [finiteStateCascadeHessian_trace_covariance_telescope V a ha L A n han H M]
  have ht := weighted_theta_telescope a θ n
  simp only [han, neg_zero, zero_mul, zero_sub] at ht
  dsimp [C, G] at hdiag hzero hsum
  linarith

end FourPapersCommon
