module
public import QuantitativePaper.ResponseC1Test

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

theorem vectorProfile_curvature_pairing_C1_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let H:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i)
    w.value (s₀.q (i+1))*R (s₀.q (i+1))-w.value (s₀.q i)*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),w.slope q*R q+w.value q*H q.toNNReal:=
  vectorProfile_curvature_pairing_C1_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ
    w.value w.slope w.continuous.continuousOn w.continuous_slope.continuousOn (fun q _=>w.hasDerivAt q)

theorem vectorProfile_trace_reaction_squared_C1_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let H:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i)
    (w.value (s₀.q (i+1)))^2*R (s₀.q (i+1))-(w.value (s₀.q i))^2*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),2*w.slope q*w.value q*R q+(w.value q)^2*H q.toNNReal:=by
  apply vectorProfile_trace_reaction_C1_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ
    (fun q=>(w.value q)^2) (fun q=>2*w.slope q*w.value q)
    (w.continuous.pow 2).continuousOn
    ((continuous_const.mul w.continuous_slope).mul w.continuous).continuousOn
  intro q _
  convert (w.hasDerivAt q).pow 2 using 1 <;> ring

end QuantitativePaper
