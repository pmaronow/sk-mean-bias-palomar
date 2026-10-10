module
public import QuantitativePaper.VectorProfileExpectedSource

@[expose] public section

/-! The three literal profile-generator expectation identities under the
actual fractional finite diffusion law. Every smoothness, growth,
Itô-limit and generator hypothesis is discharged by the constructed model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def VectorProfileExpectedIntervalIdentity (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ) (a b : ℝ≥0) : Prop:=
  let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ
  IntegrableOn (E H) (Ioc a b) nonnegativeLebesgueMeasure ∧
    E F b-E F a=∫r in Ioc a b,E H r ∂nonnegativeLebesgueMeasure

theorem vectorProfile_second_variation_expected_source_interval (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileCellFieldSecondVariation (n:=n) s₀ s₁ β t i)
      (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) a b := by
  exact vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
    (vectorProfileCellFieldSecondVariation s₀ s₁ β t i)
    (vectorProfileFieldSecondVariationSource s₀ s₁ β t i)
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldSecondVariation
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldSecondVariation_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) a b hab haq hbq

theorem vectorProfile_curvature_pairing_expected_source_interval (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileCellFieldCurvaturePairing (n:=n) s₀ s₁ β t i)
      (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) a b := by
  exact vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
    (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing
      hn s₀ s₁ β t hβ ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldCurvaturePairing_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) a b hab haq hbq

theorem vectorProfile_trace_time_expected_source_interval (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileCellFieldTraceTime (n:=n) s₀ s₁ β t i)
      (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) a b := by
  exact vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
    (vectorProfileCellFieldTraceTime s₀ s₁ β t i)
    (vectorProfileFieldTraceTimeSource s₀ s₁ β t i)
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldTraceTime
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldTraceTime_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) a b hab haq hbq

end QuantitativePaper
