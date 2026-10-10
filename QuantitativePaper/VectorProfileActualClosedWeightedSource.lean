module
public import QuantitativePaper.VectorProfileClosedWeightedSource

@[expose] public section

/-! Literal affine pairing and squared-affine trace reaction tests on
closed finite cells. All growth, integrability and endpoint obligations
are discharged by the actual profile diffusion. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem integrable_vectorProfile_retained_pairing (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Icc (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedCurvaturePairing s₀ s₁ β t i q
        ((θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t ht q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_retained_observable s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩ i hi
    (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩ _
    (retainedExponentialContinuousOn_vectorProfileRetainedCurvaturePairing hn s₀ s₁ β t ht i hi
      _ _ (by linarith [hθ.1]) (by linarith [hθ.2])) q hq

theorem integrable_vectorProfile_retained_reaction (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Icc (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedTraceReaction s₀ s₁ β t i q
        ((θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t ht q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_retained_observable s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩ i hi
    (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩ _
    (retainedExponentialContinuousOn_vectorProfileRetainedTraceReaction hn s₀ s₁ β t ht i hi
      _ _ (by linarith [hθ.1]) (by linarith [hθ.2])) q hq

theorem vectorProfile_curvature_pairing_affine_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (α δ : ℝ) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i)
    (α+δ*s₀.q (i+1))*ER (s₀.q (i+1))-(α+δ*s₀.q i)*ER (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),δ*ER q+(α+δ*q)*EH q.toNNReal := by
  refine vectorProfile_closed_tested_source_interval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi
    (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
    (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
    (continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ?_ ?_ ?_
    (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
    (fun q=>α+δ*q) (fun _=>δ) (by fun_prop) continuousOn_const ?_
  · intro q hq
    exact integrable_vectorProfile_retained_pairing hn s₀ s₁ β t outer θ ht.le i hi hθ q
      ⟨hq.1.le,hq.2.le⟩
  · intro q hq p x
    exact vectorProfileRetainedCurvaturePairing_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ
  · intro q hq
    exact integrable_vectorProfile_curvature_pairing_source hn s₀ s₁ β t outer θ hβ.ne' ht i hi hθ q hq
  · intro a b hab ha hb
    exact vectorProfile_curvature_pairing_affine_expected_source hn s₀ s₁ β t outer θ hβ.ne' ht i hi hθ α δ a b hab ha hb

theorem vectorProfile_trace_reaction_squared_affine_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (α δ : ℝ) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i)
    (α+δ*s₀.q (i+1))^2*ER (s₀.q (i+1))-(α+δ*s₀.q i)^2*ER (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),2*δ*(α+δ*q)*ER q+(α+δ*q)^2*EH q.toNNReal := by
  refine vectorProfile_closed_tested_source_interval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi
    (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
    (vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i)
    (vectorProfileFieldTraceTimeSource s₀ s₁ β t i)
    (continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ?_ ?_ ?_
    (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
    (fun q=>(α+δ*q)^2) (fun q=>2*δ*(α+δ*q)) (by fun_prop) (by fun_prop) ?_
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
    exact vectorProfile_trace_time_squared_affine_expected_source hn s₀ s₁ β t outer θ hβ ht i hi hθ α δ a b hab ha hb

end QuantitativePaper
