module
public import QuantitativePaper.VectorProfileCellRepresentation
public import QuantitativePaper.VectorProfileKernelEnvelopes

@[expose] public section

/-! A Gaussian amplitude extension of the actual profile cell. The amplitude
can cross zero; the overlap-time square root is applied only after this
smooth extension has been constructed. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileTailAmplitudeEvaluation (z : Field n)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ×VectorParameter n :=
  variableGaussianEvaluation (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n))
    (vectorProfileJointShift n 1) id z w

theorem vectorProfileTailAmplitudeEvaluation_eq (z : Field n)
    (w : ℝ×(ℝ×VectorParameter n)) :
    vectorProfileTailAmplitudeEvaluation z w = (w.2.1,w.2.2.1,w.2.2.2+w.1 • z) := by
  ext
  · simp [vectorProfileTailAmplitudeEvaluation,variableGaussianEvaluation,vectorProfileJointShift]
  · simp [vectorProfileTailAmplitudeEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift]
  · simp [vectorProfileTailAmplitudeEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift]
  · simp [vectorProfileTailAmplitudeEvaluation,variableGaussianEvaluation,vectorProfileJointShift,vectorJointShift,
      fieldShift,Real.sqrt_one]

def vectorProfileTailAmplitudePartition (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ :=
  ∫ z, Real.exp (vectorProfileCellExponent s₀ s₁ β t i j
    (vectorProfileTailAmplitudeEvaluation z w)) ∂fieldGaussian n

def vectorProfileTailAmplitudeFunction (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ :=
  if vectorProfileMass s₀ s₁ w.2.1 i = 0 then
    ∫ z, vectorProfileJointFunction s₀ s₁ β t j
      (vectorProfileTailAmplitudeEvaluation z w) ∂fieldGaussian n
  else (vectorProfileMass s₀ s₁ w.2.1 i)⁻¹*
    Real.log (vectorProfileTailAmplitudePartition s₀ s₁ β t i j w)

theorem vectorProfileTailAmplitudePartition_pos (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i j : ℕ) (w : ℝ×(ℝ×VectorParameter n))
    (hθ : w.2.1 ∈ Icc (0:ℝ) 1) :
    0 < vectorProfileTailAmplitudePartition s₀ s₁ β t i j w := by
  have hh := gaussianShiftPartition_pos (vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j)
    (Real.sqrt (n:ℝ)).toNNReal (vectorProfileRecursion_lipschitz s₀ s₁ β t w.2.1 hθ w.2.2.1 j)
    (w.1 • ContinuousLinearMap.id ℝ (Field n)) (vectorProfileMass s₀ s₁ w.2.1 i) w.2.2.2
  simpa only [vectorProfileTailAmplitudePartition,vectorProfileTailAmplitudeEvaluation_eq,
    vectorProfileCellExponent,vectorProfileJointFunction,gaussianShiftPartition,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using hh

theorem vectorProfileTailAmplitudeFunction_eq_cell (s₀ s₁ : RSBScheme k)
    (β t c Q : ℝ) (i j : ℕ) (q : ℝ) (y : ℝ×VectorParameter n) :
    vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (Real.sqrt (c*(Q-q)),y) =
      vectorProfileCellFunction s₀ s₁ β t c Q i j (q,y) := by
  have he : ∀ z : Field n, vectorProfileTailAmplitudeEvaluation z (Real.sqrt (c*(Q-q)),y) =
      vectorProfileCellEvaluation c Q z (q,y) := by
    intro z
    rw [vectorProfileTailAmplitudeEvaluation_eq,vectorProfileCellEvaluation_eq]
    rfl
  rw [vectorProfileCellFunction_eq_average_partition]
  simp only [vectorProfileTailAmplitudeFunction,vectorProfileTailAmplitudePartition,he]
  rfl

end QuantitativePaper
