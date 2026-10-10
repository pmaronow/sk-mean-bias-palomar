module
public import QuantitativeFollowup.FollowupCavityGeneratedForestConstruction
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Products of actual independent tree expectations are literal moments
of the native forest law. Each component keeps its own genuine tilted
root and full record; independence is proved by the product construction,
not supplied as a law or moment premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedNativeForest_product_expectations
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : (i : I) → (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (T i)) → ℝ) :
    (∫ z, ∏i, F i (z i) ∂cavityGeneratedNativeForestLaw D μ a J T q) =
      ∏i, ∫ z, F i z ∂anisotropicRecordedProfileTreeLaw D μ a (q i) (T i) := by
  exact integral_fintype_prod_eq_prod F

theorem cavityGeneratedNativeForest_terminal_product_expectations
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : (i : I) → TerminalSpins (Configuration (n+1)) (T i) → ℝ) :
    (∫ σ : CavityGeneratedForestTerminalSample (n:=n) J T, ∏i, F i (σ i)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q :
        Measure (CavityGeneratedForestTerminalSample (n:=n) J T))) =
      ∏i, ∫ z, F i (finiteCascadeRecordTerminalSpins (T i) z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a (q i) (T i) := by
  rw [←cavityGeneratedNativeForest_integral_terminal D μ a J T q (fun σ => ∏i, F i (σ i))]
  exact cavityGeneratedNativeForest_product_expectations D μ a J T q
    (fun i z => F i (finiteCascadeRecordTerminalSpins (T i) z.2))

end QuantitativeFollowup
