module
public import FourPapersCommon.FiniteStateCascadeTraceTelescope

@[expose] public section

/-! The signed covariance cancellation keeps the outer fractional Gaussian
average in the actual total cascade; no zero outer-mass hypothesis is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1800000

theorem finiteStateCascade_fixed_total_covariance_telescope
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (T N : ℕ) (hNT : N≤T) (H : FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L N (T-N) H M-
      ∑j∈Finset.range N,finiteStateCascadeCovarianceResponse V a L j (T-j) H (A j)=
    finiteStateCascadeDiagonalMoment V a L T H
        (cascadeCovarianceGap (finiteStateSpectralCovariance M)
          (fun j=>finiteStateSpectralCovariance (A j)) N 0)+
      (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 T H
        (cascadeCovarianceGap (finiteStateSpectralCovariance M)
          (fun j=>finiteStateSpectralCovariance (A j)) N 0)+
      ∑p∈Finset.range N,(a (p+1)-a p)*finiteStateCascadeCovarianceMoment V a L
        (p+1) (T-(p+1)) H (cascadeCovarianceGap (finiteStateSpectralCovariance M)
          (fun j=>finiteStateSpectralCovariance (A j)) N (p+1)) := by
  rw [finiteStateCascadeCovarianceResponse_eq_linear V a ha L T N hNT H M]
  have he : (∑j∈Finset.range N,finiteStateCascadeCovarianceResponse V a L j (T-j) H (A j))=
      ∑j∈Finset.range N,cascadeCovarianceResponseLinear
        (finiteStateCascadeDiagonalLinear V a ha L T H)
        (fun p=>finiteStateCascadePairLinear V a ha L T p H) a j (finiteStateSpectralCovariance (A j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact finiteStateCascadeCovarianceResponse_eq_linear V a ha L T j
      ((Finset.mem_range.mp hj).le.trans hNT) H (A j)
  rw [he,cascadeCovarianceResponse_telescope]
  rfl

theorem sum_range_tail_sub (f : ℕ→ℝ) (N p : ℕ) (hp : p≤N) :
    (∑j∈Finset.range N,if p≤j then f j-f (j+1) else 0)=f p-f N := by
  have he : (∑j∈Finset.range N,if p≤j then f j-f (j+1) else 0)+
      (∑j∈Finset.range p,(f j-f (j+1)))=∑j∈Finset.range N,(f j-f (j+1)) := by
    have hs : (∑j∈Finset.range p,(f j-f (j+1)))=
        ∑j∈Finset.range N,if j<p then f j-f (j+1) else 0 := by
      rw [←Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_range,Finset.mem_filter]
      omega
    rw [hs,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjp : p≤j
    · simp [hjp,show ¬j<p by omega]
    · simp [hjp,show j<p by omega]
  rw [Finset.sum_range_sub',Finset.sum_range_sub'] at he
  linarith

end FourPapersCommon
