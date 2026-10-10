module
public import QuantitativePaper.VectorProfileTraceTimeExtension

@[expose] public section

/-! Exact shared-tail matching and literal one-sided trace-reaction jumps
at finite profile nodes. The global derivative at a node is not used. -/
noncomputable section
open Set
open scoped Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
variable {n k : ℕ}

def vectorProfileCellFieldTraceTimeExtension (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileCellTraceTimeExtension s₀ s₁ β t i z.1
    (vectorProfileCellJointGradient s₀ s₁ β t i z)

theorem vectorProfileCellJointGradient_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i ≤ k+1) (hj : j ≤ k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) (x : Field n) :
    vectorProfileCellJointGradient s₀ s₁ β t j (a,x)=
      vectorProfileCellJointGradient s₀ s₁ β t i (a,x) := by
  rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t j hj a hqj hθ,
    vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a hqi hθ]

theorem vectorProfileCellFieldSecondVariation_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i ≤ k+1) (hj : j ≤ k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) (x : Field n) :
    vectorProfileCellFieldSecondVariation s₀ s₁ β t j (a,x)=
      vectorProfileCellFieldSecondVariation s₀ s₁ β t i (a,x) := by
  unfold vectorProfileCellFieldSecondVariation
  rw [vectorProfileCellJointGradient_match s₀ s₁ β t i j hi hj a hqi hqj hθ x]
  rfl

theorem vectorProfileCellFieldCurvaturePairing_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i ≤ k+1) (hj : j ≤ k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) (x : Field n) :
    vectorProfileCellFieldCurvaturePairing s₀ s₁ β t j (a,x)=
      vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x) := by
  unfold vectorProfileCellFieldCurvaturePairing
  rw [vectorProfileCellJointGradient_match s₀ s₁ β t i j hi hj a hqi hqj hθ x]
  rfl

theorem vectorProfileCellFieldTraceTimeExtension_jump
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i ≤ k+1) (hj : j ≤ k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) (x : Field n) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t j (a,x)-
        vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i (a,x)=
      -(1-t)*(β*(vectorProfileMass s₀ s₁ a.2.1 j-vectorProfileMass s₀ s₁ a.2.1 i))*
        Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  unfold vectorProfileCellFieldTraceTimeExtension
  rw [vectorProfileCellJointGradient_match s₀ s₁ β t i j hi hj a hqi hqj hθ x]
  exact vectorProfileCellTraceTimeExtension_jump s₀ s₁ β t i j a _

end QuantitativePaper
