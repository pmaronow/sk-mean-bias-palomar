module
public import QuantitativePaper.VectorDyadicFixedHessianEnergy
public import QuantitativePaper.VectorFixedStateGradientCells

@[expose] public section

/-! Identification of every closed-cell component energy with the literal
restarted-tail Hessian Hilbert square along the fixed actual μ diffusion. -/
noncomputable section
open Set FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem sum_vectorFixedStateCellGradientEnergy_eq_tailHessian (s : RSBScheme k)
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (q : Paper.Overlap) (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1)))
    (sample : VectorDisorderBrownianSample n) :
    (∑l : Fin n,vectorFixedStateCellGradientEnergy s μ β t ht i (q : ℝ).toNNReal sample l)=
      vectorHessianHilbertSquare (vectorFiniteTailHessian s β t q sample.1
        (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)) := by
  have he:=vectorTailRecursion_eq_finiteCell s β t q sample.1 i hi hq
  have hs:ContDiff ℝ 2 (vectorTailRecursion s β t q sample.1 (k+2)):=
    (contDiff_vectorTailRecursion_field s β t q sample.1).of_le (by simp)
  rw [he] at hs
  unfold vectorFixedStateCellGradientEnergy
  rw [Real.coe_toNNReal _ q.property.1]
  rw [sum_gradient_component_energy_eq_hilbertSquare _ hs]
  unfold vectorFiniteTailHessian
  rw [he]

end QuantitativePaper
