module
public import QuantitativePaper.VectorProfileTentIntegralEnergy
public import QuantitativePaper.VectorProfileTentJumpTelescope

@[expose] public section

/-! Literal tent signal and denominator, with their genuine finite-cell
Xi telescopes. The denominator contains exactly the mass-jump term. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileTentSignal (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) : ℝ:=
  ∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
    β*(s₁.m i-s₀.m i)*responseTent ell q*
      vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
        (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q

def vectorProfileTentDenominator (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) : ℝ:=
  (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),(responseTentSlope ell q)^2*
    vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
      (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q)+
  2*(1-t)*β*∑i∈Finset.range (k+1),
    (vectorProfileMass s₀ s₁ θ (i+1)-vectorProfileMass s₀ s₁ θ i)*
      (responseTent ell (s₀.q (i+1)))^2*
      vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
        (vectorProfileRetainedTraceSquare s₀ s₁ β t i) (s₀.q (i+1))

theorem vectorProfile_tent_pairing_integral_sum (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
      vectorProfileTentCellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell i q)=
      -(1-t)*vectorProfileTentSignal (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell := by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  have hc (i : ℕ) (hi : i∈Finset.range (k+2)) :
      (∫q in (s₀.q i)..(s₀.q (i+1)),vectorProfileTentCellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell i q)=
      (∫q in (s₀.q i)..(s₀.q (i+1)),responseTentSlope ell q*R (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i) q+
        responseTent ell q*E (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal)-
      (1-t)*(∫q in (s₀.q i)..(s₀.q (i+1)),β*(s₁.m i-s₀.m i)*responseTent ell q*R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q):=by
    have hin : i≤k+1:=by have:=Finset.mem_range.mp hi;omega
    have hab:=s₀.q_mono i (by omega)
    have hS:=(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hin hθ).1
    have hR : ContinuousOn (R (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)) (uIcc (s₀.q i) (s₀.q (i+1))):=by
      rw [uIcc_of_le hab]
      exact continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hin
    have hT : ContinuousOn (R (vectorProfileRetainedTraceSquare s₀ s₁ β t i)) (uIcc (s₀.q i) (s₀.q (i+1))):=by
      rw [uIcc_of_le hab]
      apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ i hin
        (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
      exact retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare s₀ s₁ β t ht.le i hin
        _ _ (by linarith [hθ.1]) (by linarith [hθ.2])
    have hTI:=(hT.intervalIntegrable (μ:=volume)).continuousOn_mul (continuous_responseTent ell).continuousOn
    have hsig : IntervalIntegrable (fun q=>β*(s₁.m i-s₀.m i)*responseTent ell q*
        R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q) volume (s₀.q i) (s₀.q (i+1)):=by
      convert hTI.const_mul (β*(s₁.m i-s₀.m i)) using 1
      funext q
      ring
    have htest:=intervalIntegrable_responseTent_tested ell (s₀.q i) (s₀.q (i+1)) _ _ hR hS
    have he : vectorProfileTentCellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell i=
      (fun q=>responseTentSlope ell q*R (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i) q+
        responseTent ell q*E (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal-
        (1-t)*(β*(s₁.m i-s₀.m i)*responseTent ell q*R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q)):=by
      funext q;unfold vectorProfileTentCellPairing;dsimp only;ring
    rw [he,intervalIntegral.integral_sub htest (hsig.const_mul (1-t)),intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl hc,Finset.sum_sub_distrib,←Finset.mul_sum,
    vectorProfile_curvature_pairing_tent_sum hn s₀ s₁ β t outer θ hβ ht hθ ell hell]
  unfold vectorProfileTentSignal
  ring

theorem vectorProfile_tent_Xi_integral_sum (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
      vectorProfileTentCellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell i q)=
      vectorProfileTentDenominator (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell := by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  have hc (i : ℕ) (hi : i∈Finset.range (k+2)) :
      (∫q in (s₀.q i)..(s₀.q (i+1)),vectorProfileTentCellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell i q)=
      (∫q in (s₀.q i)..(s₀.q (i+1)),(responseTentSlope ell q)^2*R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q)+
      2*(∫q in (s₀.q i)..(s₀.q (i+1)),2*responseTentSlope ell q*responseTent ell q*R (vectorProfileRetainedTraceReaction s₀ s₁ β t i) q+
        (responseTent ell q)^2*E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal):=by
    have hin : i≤k+1:=by have:=Finset.mem_range.mp hi;omega
    have hab:=s₀.q_mono i (by omega)
    have hV : ContinuousOn (R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i)) (uIcc (s₀.q i) (s₀.q (i+1))):=by
      rw [uIcc_of_le hab]
      exact continuousOn_vectorProfileRetainedPhysicalTrace_expectation s₀ s₁ β t outer θ ht.le hθ i hin
    have hJ : ContinuousOn (R (vectorProfileRetainedTraceReaction s₀ s₁ β t i)) (uIcc (s₀.q i) (s₀.q (i+1))):=by
      rw [uIcc_of_le hab]
      exact continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hin
    have hN:=(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hin hθ).1
    have hfirst:=intervalIntegrable_responseTentSlope_sq_mul ell (s₀.q i) (s₀.q (i+1)) _ (hV.intervalIntegrable (μ:=volume))
    have hsecond:=intervalIntegrable_responseTent_squared_tested ell (s₀.q i) (s₀.q (i+1)) _ _ hJ hN
    unfold vectorProfileTentCellXiEnergy
    rw [intervalIntegral.integral_add hfirst (hsecond.const_mul 2),intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl hc,Finset.sum_add_distrib,←Finset.mul_sum,
    vectorProfile_trace_reaction_squared_tent_sum hn s₀ s₁ β t outer θ hβ ht hθ ell hell]
  unfold vectorProfileTentDenominator
  ring

end QuantitativePaper
