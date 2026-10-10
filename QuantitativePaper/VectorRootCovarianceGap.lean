module
public import QuantitativePaper.VectorInterpolationRootSchedule
public import FourPapersCommon.FixedTotalCovarianceTelescope

@[expose] public section

/-! The actual completed SK disorder covariance minus the remaining field
covariances is the literal overlap-square interpolation gap. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
variable {n k : ℕ}

theorem vectorRootInterpolationDirection_spectral_field (hn : 0<n) (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (hj : j<k+1) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j) σ τ=
      β^2*(s.q (k+2-j)-s.q (k+1-j))*(n:ℝ)*overlap n σ τ := by
  have hq:=s.q_mono (k+1-j) (by omega)
  rw [show k+1-j+1=k+2-j by omega] at hq
  rw [vectorRootInterpolationDirection,if_pos hj,
    vectorInterpolationFieldDirection_spectral_overlap n hn _
      (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq))]

theorem vectorRootInterpolation_field_covariance_tail (hn : 0<n) (s : RSBScheme k)
    (β : ℝ) (p : ℕ) (hp : p≤k+1) (σ τ : Configuration n) :
    (∑j∈Finset.range (k+1),if p≤j then
      finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j) σ τ else 0)=
      β^2*(n:ℝ)*overlap n σ τ*(s.q (k+2-p)-s.q 1) := by
  classical
  let f : ℕ→ℝ:=fun j=>s.q (k+2-j)
  have he : (∑j∈Finset.range (k+1),if p≤j then
      finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j) σ τ else 0)=
      (β^2*(n:ℝ)*overlap n σ τ)*∑j∈Finset.range (k+1),if p≤j then f j-f (j+1) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj':j<k+1:=Finset.mem_range.mp hj
    by_cases h : p≤j
    · rw [if_pos h,if_pos h,vectorRootInterpolationDirection_spectral_field hn s β j hj']
      dsimp only [f]
      rw [show k+2-(j+1)=k+1-j by omega]
      ring
    · simp only [if_neg h,mul_zero]
  rw [he,sum_range_tail_sub f (k+1) p hp]
  dsimp only [f]
  rw [show k+2-(k+1)=1 by omega]

theorem vectorRootInterpolation_covariance_gap (hn : 0<n) (s : RSBScheme k)
    (β : ℝ) (hq : s.q 1=0) (p : ℕ) (hp : p≤k+1) (σ τ : Configuration n) :
    cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
      (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j))
      (k+1) p σ τ=(n:ℝ)*β^2/2*((overlap n σ τ)^2-2*s.q (k+2-p)*overlap n σ τ) := by
  simp only [cascadeCovarianceGap,Pi.sub_apply,Finset.sum_apply,ite_apply,Pi.zero_apply]
  rw [vectorInterpolationDisorderDirection_spectral n hn β,
    vectorRootInterpolation_field_covariance_tail hn s β p hp,hq]
  ring

end QuantitativePaper
