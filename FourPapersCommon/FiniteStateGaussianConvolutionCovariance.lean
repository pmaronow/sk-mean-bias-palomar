module
public import FourPapersCommon.FiniteStateGaussianConvolution

@[expose] public section

/-! The independent-input convolution has the sum of the two actual
spectral covariance matrices, so any Gaussian realization of that sum gives
the same logarithmic average. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace FourPapersCommon
variable {S I J K : Type*} [Fintype S] [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq S] [DecidableEq I] [DecidableEq J] [DecidableEq K]
set_option maxHeartbeats 1300000

@[simp] theorem finiteGaussianLeft_single_inl (i : I) :
    finiteGaussianLeft (J:=J) (EuclideanSpace.single (Sum.inl i) 1)=EuclideanSpace.single i 1 := by
  ext j
  simp [finiteGaussianLeft,EuclideanSpace.single_apply,Pi.single_apply]

@[simp] theorem finiteGaussianLeft_single_inr (i : J) :
    finiteGaussianLeft (I:=I) (EuclideanSpace.single (Sum.inr i) 1)=0 := by
  ext j
  simp [finiteGaussianLeft,EuclideanSpace.single_apply,Pi.single_apply]

@[simp] theorem finiteGaussianRight_single_inl (i : I) :
    finiteGaussianRight (J:=J) (EuclideanSpace.single (Sum.inl i) 1)=0 := by
  ext j
  simp [finiteGaussianRight,EuclideanSpace.single_apply,Pi.single_apply]

@[simp] theorem finiteGaussianRight_single_inr (i : J) :
    finiteGaussianRight (I:=I) (EuclideanSpace.single (Sum.inr i) 1)=EuclideanSpace.single i 1 := by
  ext j
  simp [finiteGaussianRight,EuclideanSpace.single_apply,Pi.single_apply]

theorem finiteStateSpectralCovariance_sumMap
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (σ τ : S) :
    finiteStateSpectralCovariance (finiteStateGaussianSumMap L M) σ τ=
      finiteStateSpectralCovariance L σ τ+finiteStateSpectralCovariance M σ τ := by
  simp [finiteStateSpectralCovariance,Fintype.sum_sum_type]

theorem finiteStateGaussianStep_convolution_of_covariance (a : ℝ)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (A : FiniteStateGaussianInput K→L[ℝ]FiniteStateField S)
    (hcov : ∀σ τ,finiteStateSpectralCovariance A σ τ=
      finiteStateSpectralCovariance L σ τ+finiteStateSpectralCovariance M σ τ)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) (H : FiniteStateField S) :
    finiteStateGaussianStep a L (finiteStateGaussianStep a M F) H=finiteStateGaussianStep a A F H := by
  rw [finiteStateGaussianStep_convolution a L M F hF H]
  apply finiteStateGaussianStep_eq_of_spectral_covariance _ A _ a F hF.continuous.measurable H
  intro σ τ
  rw [finiteStateSpectralCovariance_sumMap,hcov]

end FourPapersCommon
