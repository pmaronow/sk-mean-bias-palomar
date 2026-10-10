module
public import QuantitativePaper.VectorProfileFieldSources

@[expose] public section

/-! True cell reaction extensions for one-sided trace time derivatives.
At a profile atom the global derivative is not either one-sided value. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellTraceTimeExtension (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  -(1-t)/2*responseMatrixPair
    (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
      vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
    (euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m))-
    (1-t)*(β*vectorProfileMass s₀ s₁ a.2.1 i)*Matrix.trace
      (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
        vectorProfileCellHessianMatrix s₀ s₁ β t i a m)

theorem vectorProfileCellTraceTimeExtension_eq_time
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellTraceTimeExtension s₀ s₁ β t i a m=
      vectorProfileCellTraceTime s₀ s₁ β t i a m := by
  have hh:=vectorProfileCellTrace_generator s₀ s₁ β t hβ ht i hi a hq hθ m hm
  unfold vectorProfileCellTraceTimeExtension vectorProfileCellTraceTime
  linarith

theorem vectorProfileCellTraceTimeExtension_jump
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) :
    vectorProfileCellTraceTimeExtension s₀ s₁ β t j a m-
        vectorProfileCellTraceTimeExtension s₀ s₁ β t i a m=
      -(1-t)*(β*(vectorProfileMass s₀ s₁ a.2.1 j-vectorProfileMass s₀ s₁ a.2.1 i))*
        Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  have hh : vectorProfileCellHessianMatrix s₀ s₁ β t j a m=
      vectorProfileCellHessianMatrix s₀ s₁ β t i a m:=rfl
  have hN : vectorProfileCellTraceHessian s₀ s₁ β t j a m=
      vectorProfileCellTraceHessian s₀ s₁ β t i a m:=rfl
  unfold vectorProfileCellTraceTimeExtension
  rw [hh,hN]
  ring

end QuantitativePaper
