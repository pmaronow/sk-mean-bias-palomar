module
public import QuantitativePaper.VectorProfileInteriorSmooth
public import QuantitativePaper.VariableGaussianShiftJets

@[expose] public section

/-! Literal variable-variance Gaussian representation of an affine-profile
Cole--Hopf cell. No smoothing or differentiated PDE is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1500000
variable {n k : ℕ}

def vectorProfileCellFunction (s₀ s₁ : RSBScheme k) (β t c Q : ℝ)
    (i j : ℕ) (w : ℝ×(ℝ×VectorParameter n)) : ℝ:=
  vectorColeHopfStep (c*(Q-w.1)) (vectorProfileMass s₀ s₁ w.2.1 i)
    (vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j) w.2.2.2

def vectorProfileCellEvaluation (c Q : ℝ) (z : Field n)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ×VectorParameter n:=
  variableGaussianEvaluation (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n))
    (vectorProfileJointShift n 1) (fun r=>Real.sqrt (c*(Q-r))) z w

theorem vectorProfileCellEvaluation_eq (c Q : ℝ) (z : Field n)
    (w : ℝ×(ℝ×VectorParameter n)) :
    vectorProfileCellEvaluation c Q z w=
      (w.2.1,w.2.2.1,fieldShift (c*(Q-w.1)) w.2.2.2 z) := by
  ext
  · simp [vectorProfileCellEvaluation,variableGaussianEvaluation,vectorProfileJointShift]
  · simp [vectorProfileCellEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift]
  · simp [vectorProfileCellEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift]
  · simp [vectorProfileCellEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift,fieldShift]

theorem vectorProfileCellFunction_eq_average_partition (s₀ s₁ : RSBScheme k)
    (β t c Q : ℝ) (i j : ℕ) (w : ℝ×(ℝ×VectorParameter n)) :
    vectorProfileCellFunction s₀ s₁ β t c Q i j w=
      if vectorProfileMass s₀ s₁ w.2.1 i=0 then
        ∫ z,vectorProfileJointFunction s₀ s₁ β t j (vectorProfileCellEvaluation c Q z w) ∂fieldGaussian n
      else (vectorProfileMass s₀ s₁ w.2.1 i)⁻¹*
        Real.log (∫ z,Real.exp (vectorProfileMass s₀ s₁
          (vectorProfileCellEvaluation c Q z w).1 i*
            vectorProfileJointFunction s₀ s₁ β t j (vectorProfileCellEvaluation c Q z w)) ∂fieldGaussian n) := by
  simp_rw [vectorProfileCellEvaluation_eq]
  dsimp only [vectorProfileCellFunction,vectorColeHopfStep,vectorStepPartition,vectorProfileJointFunction]
  split_ifs <;> simp_all only [div_eq_mul_inv,mul_comm]

end QuantitativePaper
