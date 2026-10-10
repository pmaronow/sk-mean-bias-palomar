module
public import QuantitativePaper.VectorProfileActualPolynomialSource
public import QuantitativePaper.VectorProfileClosedTestedSubcells
public import QuantitativePaper.VectorProfilePolynomialExpectedSource

@[expose] public section

/-! Literal polynomial curvature-pairing and reaction tests on closed
finite cells. Endpoint source integrability is proved by the actual model. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_curvature_pairing_polynomial_closed_subcell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (P : Polynomial ℝ)
    (a b : ℝ) (hab : a≤b) (ha : s₀.q i≤a) (hb : b≤ s₀.q (i+1)) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i)
    P.eval b*ER b-P.eval a*ER a=
      ∫q in a..b,P.derivative.eval q*ER q+P.eval q*EH q.toNNReal:=by
  refine vectorProfile_closed_tested_source_subinterval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi a b hab ha hb
    (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
    (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
    (continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ?_ ?_ ?_
    (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
    P.eval P.derivative.eval P.continuous.continuousOn P.derivative.continuous.continuousOn ?_
  · intro q hq
    exact integrable_vectorProfile_retained_pairing hn s₀ s₁ β t outer θ ht.le i hi hθ q
      ⟨hq.1.le,hq.2.le⟩
  · intro q hq p x
    exact vectorProfileRetainedCurvaturePairing_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ
  · intro q hq
    exact integrable_vectorProfile_curvature_pairing_source hn s₀ s₁ β t outer θ hβ.ne' ht i hi hθ q hq
  · intro a b hab ha hb
    exact vectorProfile_polynomial_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
      (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
      (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
      (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing
        hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
      (fun q hq p x=>vectorProfileCellFieldCurvaturePairing_generator
        s₀ s₁ β t hβ.ne' ht i hi (q,θ,p) hq hθ x) P a b hab ha hb

theorem vectorProfile_trace_reaction_polynomial_closed_subcell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (P : Polynomial ℝ)
    (a b : ℝ) (hab : a≤b) (ha : s₀.q i≤a) (hb : b≤ s₀.q (i+1)) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i)
    P.eval b*ER b-P.eval a*ER a=
      ∫q in a..b,P.derivative.eval q*ER q+P.eval q*EH q.toNNReal:=by
  refine vectorProfile_closed_tested_source_subinterval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi a b hab ha hb
    (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
    (vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i)
    (vectorProfileFieldTraceTimeSource s₀ s₁ β t i)
    (continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ?_ ?_ ?_
    (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
    P.eval P.derivative.eval P.continuous.continuousOn P.derivative.continuous.continuousOn ?_
  · intro q hq
    exact integrable_vectorProfile_retained_reaction hn s₀ s₁ β t outer θ ht.le i hi hθ q
      ⟨hq.1.le,hq.2.le⟩
  · intro q hq p x
    exact (vectorProfileRetainedTraceReaction_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ).trans
      (vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ.ne' ht i hi
        (q,θ,p) hq hθ x).symm
  · intro q hq
    exact integrable_vectorProfile_trace_time_source hn s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  · intro a b hab ha hb
    apply vectorProfile_polynomial_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
      (vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i)
      (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) ?_ ?_ P a b hab ha hb
    · intro l u A B hl hu hA hB
      exact exponentialSmoothOn_vectorProfileCellFieldTraceTimeExtension
        hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB
    · intro q hq p x
      exact vectorProfileCellFieldTraceTimeExtension_generator s₀ s₁ β t hβ ht i hi
        (q,θ,p) hq hθ x

end QuantitativePaper
