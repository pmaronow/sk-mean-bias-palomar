module
public import QuantitativePaper.VectorProfileWeightedExpectedSource
public import FourPapersCommon.ExponentialPolynomial

@[expose] public section

/-! Genuine polynomial time testing of the actual finite profile generator.
No weighted stochastic identity is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_polynomial_expected_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (P : Polynomial ℝ) (a b : ℝ≥0) (hab : a≤b)
    (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (fun z=>P.eval z.1.1*F z)
      (fun z=>P.derivative.eval z.1.1*F z+P.eval z.1.1*H z) a b:=by
  apply vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
  · intro l u A B hl hu hA hB
    have hq:=exponentialSmoothOn_vectorProfile_time_coordinate (n:=n) l u A B
      ((s₀.q_nonneg (by omega)).trans hl) (hu.le.trans (s₀.q_le_one (by omega)))
    exact (hq.polynomial P).bilinear (hGrowth l u A B hl hu hA hB)
      (ContinuousLinearMap.mul ℝ ℝ)
  · intro q hq p x
    have hF:=(contDiffAt_vectorProfile_of_cell_growth s₀ i F hGrowth (q,θ,p) x hq hθ).of_le
      (show (2:ℕ∞ω)≤∞ by simp)
    have hw:=P.hasDerivAt q
    rw [vectorProfileCellFieldGenerator_time_mul s₀ s₁ β t i F _ (q,θ,p) x
      hF hw.differentiableAt,hw.deriv,hEq q hq p x]
  · exact hab
  · exact haq
  · exact hbq

end QuantitativePaper
