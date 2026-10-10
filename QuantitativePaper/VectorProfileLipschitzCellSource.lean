module
public import QuantitativePaper.ResponseLipschitzPrimitive

@[expose] public section

/-! Literal actual finite-cell C¹ and squared-C¹ source identities. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

theorem vectorProfile_curvature_pairing_Lipschitz_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let H:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i)
    w.value (s₀.q (i+1))*R (s₀.q (i+1))-w.value (s₀.q i)*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),w.slope q*R q+w.value q*H q.toNNReal:=by
  apply response_Lipschitz_tested_interval _ _ _ _ (s₀.q_mono i (by omega))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (s₀.q_mono i (by omega))).mpr
      (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1)
  intro q hq
  simpa only [Polynomial.eval_one,Polynomial.derivative_one,Polynomial.eval_zero,
    one_mul,zero_mul,zero_add] using
    vectorProfile_curvature_pairing_polynomial_closed_subcell hn s₀ s₁ β t outer θ hβ ht
      i hi hθ (1:Polynomial ℝ) (s₀.q i) q hq.1 le_rfl hq.2

theorem vectorProfile_trace_reaction_squared_Lipschitz_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let H:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i)
    (w.value (s₀.q (i+1)))^2*R (s₀.q (i+1))-(w.value (s₀.q i))^2*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),2*w.slope q*w.value q*R q+(w.value q)^2*H q.toNNReal:=by
  apply response_squared_Lipschitz_tested_interval _ _ _ _ (s₀.q_mono i (by omega))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (s₀.q_mono i (by omega))).mpr
      (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1)
  intro q hq
  simpa only [Polynomial.eval_one,Polynomial.derivative_one,Polynomial.eval_zero,
    one_mul,zero_mul,zero_add] using
    vectorProfile_trace_reaction_polynomial_closed_subcell hn s₀ s₁ β t outer θ hβ ht
      i hi hθ (1:Polynomial ℝ) (s₀.q i) q hq.1 le_rfl hq.2

end QuantitativePaper
