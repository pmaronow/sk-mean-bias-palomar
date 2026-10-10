module
public import QuantitativeFollowup.ScalarResponseL2Order

@[expose] public section

/-! Source-quantifier wrapper: the literal completed scalar response is
self-adjoint and dominated by the actual Γ′ multiplier, with one norm
constant for every d in [β²/2,β²]. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem scalarResponseL2Bound_mono_square (b e : ℝ) (hbe : b^2 ≤ e^2) :
    scalarResponseL2Bound b ≤ scalarResponseL2Bound e := by
  have h1 : scalarResponseKernelBound b ≤ scalarResponseKernelBound e := by
    unfold scalarResponseKernelBound
    linarith [Real.exp_le_exp.mpr hbe]
  unfold scalarResponseL2Bound
  exact mul_le_mul (mul_le_mul_of_nonneg_left hbe (by norm_num)) h1
    (by unfold scalarResponseKernelBound;positivity) (by positivity)

/-- Literal Lemma 6.5, including the common temperature-dependent norm
constant, the actual endpoint-fixed Hilbert space, and multiplier order. -/
theorem scalar_multiplier_domination (β : ℝ) (hβ : 0<β) (d : ℝ)
    (hd : d∈Icc (β^2/2) (β^2)) (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) :
    IsSelfAdjoint (scalarResponseL2Operator (Real.sqrt d)
      (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1)).ne' μ s hs hμ) ∧
    ‖scalarResponseL2Operator (Real.sqrt d)
      (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1)).ne' μ s hs hμ‖ ≤ scalarResponseL2Bound β ∧
    ∀f : endpointFixedL2 (parisiFreeMeasure μ s),
      inner ℝ f (scalarResponseL2Operator (Real.sqrt d)
        (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1)).ne' μ s hs hμ f) ≤
        inner ℝ f (scalarGammaL2Multiplier (Real.sqrt d)
          (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1)).ne' μ s f) := by
  have hdp : 0<d := (half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1
  have hp : 0<Real.sqrt d := Real.sqrt_pos.mpr hdp
  refine ⟨scalarResponseL2Operator_isSelfAdjoint (Real.sqrt d) hp μ s hs hμ,?_,?_⟩
  · exact (scalarResponseL2Operator_norm_le (Real.sqrt d) hp.ne' μ s hs hμ).trans
      (scalarResponseL2Bound_mono_square (Real.sqrt d) β (by rw [Real.sq_sqrt hdp.le];exact hd.2))
  · exact scalarResponseL2Operator_le_multiplier (Real.sqrt d) hp μ s hs hμ

end QuantitativeFollowup
