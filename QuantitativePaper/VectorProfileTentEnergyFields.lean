module
public import QuantitativePaper.VectorProfileExpectedXiEnergy
public import QuantitativePaper.ResponseTentEnergyIntegrable

@[expose] public section

/-! Literal expected Xi pairing and energy on true closed finite cells,
and genuine integrability up to every node. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileTentCellPairing (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) (i : ℕ) (q : ℝ) : ℝ:=
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
  responseTentSlope ell q*R (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i) q+
    responseTent ell q*E (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal-
    (1-t)*(β*(s₁.m i-s₀.m i))*responseTent ell q*R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q

def vectorProfileTentCellXiEnergy (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) (i : ℕ) (q : ℝ) : ℝ:=
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
  (responseTentSlope ell q)^2*R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q+
    2*(2*responseTentSlope ell q*responseTent ell q*R (vectorProfileRetainedTraceReaction s₀ s₁ β t i) q+
      (responseTent ell q)^2*E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal)

theorem intervalIntegrable_vectorProfileTentCellPairing (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (i : ℕ) (hi : i≤k+1) :
    IntervalIntegrable (vectorProfileTentCellPairing (n:=n) s₀ s₁ β t outer θ ht.le
      ⟨hθ.1.le,hθ.2.le⟩ ell i) volume (s₀.q i) (s₀.q (i+1)):=by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  have hab:=s₀.q_mono i (by omega)
  have hR : ContinuousOn (R (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i))
      (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    exact continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi
  have hS:=((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1)
  have hT : ContinuousOn (R (vectorProfileRetainedTraceSquare s₀ s₁ β t i))
      (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ i hi
      (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
    exact retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare s₀ s₁ β t ht.le i hi
      _ _ (by linarith [hθ.1]) (by linarith [hθ.2])
  have hterm : IntervalIntegrable (fun q=>responseTent ell q*
      R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q) volume (s₀.q i) (s₀.q (i+1)):=
    (hT.intervalIntegrable (μ:=volume)).continuousOn_mul (continuous_responseTent ell).continuousOn
  have hh:=(intervalIntegrable_responseTent_tested ell (s₀.q i) (s₀.q (i+1)) _ _ hR hS).sub
    (hterm.const_mul ((1-t)*(β*(s₁.m i-s₀.m i))))
  convert hh using 1
  funext q
  unfold vectorProfileTentCellPairing
  dsimp only
  ring

theorem intervalIntegrable_vectorProfileTentCellXiEnergy (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (i : ℕ) (hi : i≤k+1) :
    IntervalIntegrable (vectorProfileTentCellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le
      ⟨hθ.1.le,hθ.2.le⟩ ell i) volume (s₀.q i) (s₀.q (i+1)):=by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  have hab:=s₀.q_mono i (by omega)
  have hV : ContinuousOn (R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i))
      (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    exact continuousOn_vectorProfileRetainedPhysicalTrace_expectation s₀ s₁ β t outer θ ht.le hθ i hi
  have hJ : ContinuousOn (R (vectorProfileRetainedTraceReaction s₀ s₁ β t i))
      (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    exact continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi
  have hN:=(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
  exact (intervalIntegrable_responseTentSlope_sq_mul ell (s₀.q i) (s₀.q (i+1)) _ hV.intervalIntegrable).add
    ((intervalIntegrable_responseTent_squared_tested ell (s₀.q i) (s₀.q (i+1)) _ _ hJ hN).const_mul 2)

end QuantitativePaper
