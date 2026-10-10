module
public import QuantitativePaper.ResponseTentProductIntegrable
public import QuantitativePaper.VectorProfileActualClosedSubcells

@[expose] public section

/-! Genuine tent and squared-tent source identities on each closed
actual finite profile cell, with all regularity inputs discharged. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_curvature_pairing_tent_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : 0<ell) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
    let H:=fun q : ℝ=>vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i) q.toNNReal
    responseTent ell (s₀.q (i+1))*R (s₀.q (i+1))-responseTent ell (s₀.q i)*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),responseTentSlope ell q*R q+responseTent ell q*H q := by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
  let H:=fun q : ℝ=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal
  have hab:=s₀.q_mono i (by omega)
  have hR : ContinuousOn R (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    exact continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi
  have hH : IntervalIntegrable H volume (s₀.q i) (s₀.q (i+1)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (vectorProfile_curvature_pairing_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
  have hh:=responseTent_tested_interval ell (s₀.q i) (s₀.q (i+1)) hell hab 1 R H
    (by simpa only [Nat.cast_one,Nat.reduceSub,pow_zero,pow_one,one_mul,mul_one] using
      intervalIntegrable_responseTent_tested ell (s₀.q i) (s₀.q (i+1)) R H hR hH)
    (fun α δ l u hlu hl hu=>by simpa only [Nat.cast_one,Nat.reduceSub,pow_zero,pow_one,one_mul,mul_one] using
      vectorProfile_curvature_pairing_affine_closed_subcell hn s₀ s₁ β t outer θ hβ ht i hi hθ α δ l u hlu hl hu)
  simpa only [Nat.cast_one,Nat.reduceSub,pow_zero,pow_one,one_mul,mul_one] using hh

theorem vectorProfile_trace_reaction_squared_tent_closed_cell (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : 0<ell) :
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
    let H:=fun q : ℝ=>vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i) q.toNNReal
    (responseTent ell (s₀.q (i+1)))^2*R (s₀.q (i+1))-(responseTent ell (s₀.q i))^2*R (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),2*responseTentSlope ell q*responseTent ell q*R q+
        (responseTent ell q)^2*H q := by
  let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
  let H:=fun q : ℝ=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal
  have hab:=s₀.q_mono i (by omega)
  have hR : ContinuousOn R (uIcc (s₀.q i) (s₀.q (i+1))):=by
    rw [uIcc_of_le hab]
    exact continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi
  have hH : IntervalIntegrable H volume (s₀.q i) (s₀.q (i+1)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
  have hh:=responseTent_tested_interval ell (s₀.q i) (s₀.q (i+1)) hell hab 2 R H
    (by simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using
      intervalIntegrable_responseTent_squared_tested ell (s₀.q i) (s₀.q (i+1)) R H hR hH)
    (fun α δ l u hlu hl hu=>by simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using
      vectorProfile_trace_reaction_squared_affine_closed_subcell hn s₀ s₁ β t outer θ hβ ht i hi hθ α δ l u hlu hl hu)
  simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using hh

end QuantitativePaper
