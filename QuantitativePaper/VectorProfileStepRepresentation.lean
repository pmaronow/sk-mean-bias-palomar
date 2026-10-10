module
public import QuantitativePaper.VectorProfileParameterJets
public import QuantitativePaper.SmoothOpenGaussianAverage
public import QuantitativePaper.OpenGaussianRelativeBounds

@[expose] public section

/-! The actual affine-profile step is the actual open-domain Gaussian
average or log partition. The affine mass is unchanged by the field shift. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000

def vectorProfileStepVariance {k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) : ℝ :=
  (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))

def vectorProfileStepMass {n k : ℕ} (s₀ s₁ : RSBScheme k) (j : ℕ)
    (x : ℝ×VectorParameter n) : ℝ := vectorProfileMass s₀ s₁ x.1 (k+1-j)

theorem vectorProfileJointFunction_step_eq {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (j : ℕ) (x : ℝ×VectorParameter n) :
    vectorProfileJointFunction s₀ s₁ β t (j+1) x =
      if vectorProfileStepMass s₀ s₁ j x=0 then
        gaussianShiftAverage (vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j))
          (vectorProfileJointFunction s₀ s₁ β t j) x
      else (vectorProfileStepMass s₀ s₁ j x)⁻¹ *
        Real.log (gaussianShiftPartition (vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j)) 1
          (fun y => vectorProfileStepMass s₀ s₁ j y*vectorProfileJointFunction s₀ s₁ β t j y) x) := by
  rw [vectorProfileJointFunction, vectorProfileRecursion]
  dsimp only [vectorColeHopfStep, gaussianShiftAverage, gaussianShiftPartition,
    vectorStepPartition, vectorProfileJointFunction, vectorProfileStepMass, vectorProfileStepVariance]
  simp_rw [vectorProfileJointShift_add]
  split_ifs <;> simp_all only [one_mul, div_eq_mul_inv, mul_comm]

theorem log_vectorProfileStepPartition_eq {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (j : ℕ) (x : ℝ×VectorParameter n)
    (hm : vectorProfileStepMass s₀ s₁ j x ≠ 0) :
    Real.log (gaussianShiftPartition (vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j)) 1
      (fun y => vectorProfileStepMass s₀ s₁ j y*vectorProfileJointFunction s₀ s₁ β t j y) x) =
      vectorProfileStepMass s₀ s₁ j x*vectorProfileJointFunction s₀ s₁ β t (j+1) x := by
  rw [vectorProfileJointFunction_step_eq, if_neg hm]
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]

theorem vectorProfileJointFunction_shift_lipschitz {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t c : ℝ) (j : ℕ) (x : ℝ×VectorParameter n) (hx : x.1 ∈ Icc (0:ℝ) 1)
    (z : Field n) :
    |vectorProfileJointFunction s₀ s₁ β t j (x+vectorProfileJointShift n c z)-
      vectorProfileJointFunction s₀ s₁ β t j x| ≤
      (vectorJointLipschitzConstant n β t:ℝ)*‖vectorJointShift n c‖*‖z‖ := by
  let s := vectorProfileScheme s₀ s₁ x.1 hx
  have hh := (vectorRecursion_joint_lipschitz (n:=n) s β t j).dist_le_mul
    (x.2+vectorJointShift n c z) x.2
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hh
  rw [vectorProfileJointShift_add]
  unfold vectorProfileJointFunction
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t x.1 hx]
  rw [vectorJointShift_add] at hh
  have hmul := mul_le_mul_of_nonneg_left ((vectorJointShift n c).le_opNorm z)
    (vectorJointLipschitzConstant n β t).coe_nonneg
  simpa only [mul_assoc] using hh.trans hmul

theorem vectorProfileStepExponent_shift_lipschitz {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t c : ℝ) (j : ℕ) (x : ℝ×VectorParameter n) (hx : x.1 ∈ Icc (0:ℝ) 1)
    (z : Field n) :
    |vectorProfileStepMass s₀ s₁ j (x+vectorProfileJointShift n c z)*
        vectorProfileJointFunction s₀ s₁ β t j (x+vectorProfileJointShift n c z)-
      vectorProfileStepMass s₀ s₁ j x*vectorProfileJointFunction s₀ s₁ β t j x| ≤
      (vectorJointLipschitzConstant n β t:ℝ)*‖vectorJointShift n c‖*‖z‖ := by
  have hm := vectorProfileMass_mem_unit s₀ s₁ (k+1-j) (Nat.sub_le _ _) x.1 hx
  have hmass : vectorProfileStepMass s₀ s₁ j (x+vectorProfileJointShift n c z)=
      vectorProfileStepMass s₀ s₁ j x := by
    rw [vectorProfileJointShift_add]
    rfl
  change 0 ≤ vectorProfileStepMass s₀ s₁ j x ∧ vectorProfileStepMass s₀ s₁ j x ≤ 1 at hm
  rw [hmass, ← mul_sub, abs_mul, abs_of_nonneg hm.1]
  exact (mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)).trans
    (by simpa only [one_mul] using vectorProfileJointFunction_shift_lipschitz s₀ s₁ β t c j x hx z)

end QuantitativePaper
