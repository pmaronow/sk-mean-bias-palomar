module
public import QuantitativePaper.VectorProfileWeightedExpectedSource
public import QuantitativePaper.VectorProfileTraceExtensionSource

@[expose] public section

/-! Closed actual strict-cell weighted source laws. The squared trace-time
test uses the reaction extension, so it has the correct one-sided value
when these identities are later joined at profile atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_curvature_pairing_affine_expected_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (α δ : ℝ) (a b : ℝ≥0) (hab : a≤b)
    (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (fun z=>(α+δ*z.1.1)*vectorProfileCellFieldCurvaturePairing (n:=n) s₀ s₁ β t i z)
      (fun z=>δ*vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i z+
        (α+δ*z.1.1)*vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i z) a b := by
  exact vectorProfile_affine_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
    _ _ (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing
      hn s₀ s₁ β t hβ ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldCurvaturePairing_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) α δ a b hab haq hbq

theorem vectorProfile_trace_time_extension_expected_source_interval (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileCellFieldTraceTimeExtension (n:=n) s₀ s₁ β t i)
      (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) a b := by
  exact vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ _ _
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldTraceTimeExtension
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldTraceTimeExtension_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) a b hab haq hbq

theorem vectorProfile_trace_time_squared_affine_expected_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (α δ : ℝ) (a b : ℝ≥0) (hab : a≤b)
    (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (fun z=>(α+δ*z.1.1)^2*vectorProfileCellFieldTraceTimeExtension (n:=n) s₀ s₁ β t i z)
      (fun z=>2*δ*(α+δ*z.1.1)*vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i z+
        (α+δ*z.1.1)^2*vectorProfileFieldTraceTimeSource s₀ s₁ β t i z) a b := by
  exact vectorProfile_squared_affine_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
    _ _ (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldTraceTimeExtension
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldTraceTimeExtension_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) α δ a b hab haq hbq

end QuantitativePaper
