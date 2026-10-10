module
public import QuantitativePaper.VectorProfileSourceContinuity
public import QuantitativePaper.VectorProfileActualPolynomialSubcells
public import QuantitativePaper.ResponseC1WeightedSource

@[expose] public section

/-! Actual curvature-pairing and Hessian-reaction identities for genuine C¹
time tests on closed cells. All source continuity and integrability come
from the constructed finite diffusion and its checked generator. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_curvature_pairing_C1_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (w w₁ : ℝ→ℝ) (hw : ContinuousOn w (Icc (s₀.q i) (s₀.q (i+1))))
    (hw₁ : ContinuousOn w₁ (Icc (s₀.q i) (s₀.q (i+1))))
    (hwd : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),HasDerivAt w (w₁ q) q) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i)
    w (s₀.q (i+1))*ER (s₀.q (i+1))-w (s₀.q i)*ER (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),w₁ q*ER q+w q*EH q.toNNReal:=by
  let ER:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
  let EH : ℝ→ℝ:=fun q=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal
  apply response_C1_tested_interval ER EH w w₁ _ _ (s₀.q_mono i (by omega))
    (continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (s₀.q_mono i (by omega))).mpr
      (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1)
    _ _ hw hw₁ hwd
  · intro q hq
    exact (continuousAt_vectorProfileExpectedGeneratorSource s₀ s₁ β t outer θ hβ.ne' ht i hi hθ
      (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
      (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
      (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing
        hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
      (fun q hq p x=>vectorProfileCellFieldCurvaturePairing_generator
        s₀ s₁ β t hβ.ne' ht i hi (q,θ,p) hq hθ x) q hq).continuousWithinAt
  · intro q hq
    simpa only [Polynomial.eval_one,Polynomial.derivative_one,Polynomial.eval_zero,
      one_mul,zero_mul,zero_add] using
      vectorProfile_curvature_pairing_polynomial_closed_subcell hn s₀ s₁ β t outer θ hβ ht
        i hi hθ (1:Polynomial ℝ) (s₀.q i) q hq.1 le_rfl hq.2

theorem vectorProfile_trace_reaction_C1_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (w w₁ : ℝ→ℝ) (hw : ContinuousOn w (Icc (s₀.q i) (s₀.q (i+1))))
    (hw₁ : ContinuousOn w₁ (Icc (s₀.q i) (s₀.q (i+1))))
    (hwd : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),HasDerivAt w (w₁ q) q) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i)
    w (s₀.q (i+1))*ER (s₀.q (i+1))-w (s₀.q i)*ER (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),w₁ q*ER q+w q*EH q.toNNReal:=by
  let ER:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
  let EH : ℝ→ℝ:=fun q=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal
  apply response_C1_tested_interval ER EH w w₁ _ _ (s₀.q_mono i (by omega))
    (continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (s₀.q_mono i (by omega))).mpr
      (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1)
    _ _ hw hw₁ hwd
  · intro q hq
    exact (continuousAt_vectorProfileExpectedGeneratorSource s₀ s₁ β t outer θ hβ.ne' ht i hi hθ
      (vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i)
      (vectorProfileFieldTraceTimeSource s₀ s₁ β t i)
      (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldTraceTimeExtension
        hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
      (fun q hq p x=>vectorProfileCellFieldTraceTimeExtension_generator
        s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) q hq).continuousWithinAt
  · intro q hq
    simpa only [Polynomial.eval_one,Polynomial.derivative_one,Polynomial.eval_zero,
      one_mul,zero_mul,zero_add] using
      vectorProfile_trace_reaction_polynomial_closed_subcell hn s₀ s₁ β t outer θ hβ ht
        i hi hθ (1:Polynomial ℝ) (s₀.q i) q hq.1 le_rfl hq.2

end QuantitativePaper
