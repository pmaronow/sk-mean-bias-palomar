module
public import QuantitativePaper.VectorMeasureMinimizer
public import FourPapersCommon.CompactLipschitzEnvelope

@[expose] public section

/-! The literal optimized interpolation and its two physical endpoints.
The zero endpoint is the constrained scalar Parisi value; the one endpoint
is the completed fractional pressure of the actual finite SK model. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 800000

def vectorInterpolationMinimum (n : ℕ) (β s t : ℝ) : ℝ :=
  compactMinimumValue (scalarFloor s) (fun u μ => vectorMeasureFunctional n μ β u s) t

theorem vectorInterpolationMinimum_zero (n : ℕ) (hn : 0 < n)
    (β s : ℝ) (hβ : β ≠ 0) :
    vectorInterpolationMinimum n β s 0 = constrainedParisiValue β s := by
  unfold vectorInterpolationMinimum compactMinimumValue constrainedParisiValue
  congr 1
  apply Set.image_congr
  intro μ _
  exact vectorMeasureFunctional_zero n hn μ β hβ s

theorem vectorInterpolationMinimum_one (n : ℕ) (β s : ℝ)
    (hs : s ≤ 1) (hs0 : s ≠ 0) :
    vectorInterpolationMinimum n β s 1 = completedFractionalPressure n β s := by
  have he : (fun μ => vectorMeasureFunctional n μ β 1 s) '' scalarFloor s =
      {completedFractionalPressure n β s} := by
    ext r
    constructor
    · rintro ⟨μ, _, rfl⟩
      simpa only [Set.mem_singleton_iff] using vectorMeasureFunctional_one n μ β s hs0
    · intro hr
      obtain ⟨μ, hμ⟩ := scalarFloor_nonempty s hs
      refine ⟨μ, hμ, ?_⟩
      change vectorMeasureFunctional n μ β 1 s = r
      rw [vectorMeasureFunctional_one n μ β s hs0]
      exact (Set.mem_singleton_iff.mp hr).symm
  unfold vectorInterpolationMinimum compactMinimumValue
  rw [he, csInf_singleton]

theorem vectorInterpolationMinimum_endpoint_gap (n : ℕ) (hn : 0 < n)
    (β s : ℝ) (hβ : β ≠ 0) (hs : s ≤ 1) (hs0 : s ≠ 0) :
    vectorInterpolationMinimum n β s 0 - vectorInterpolationMinimum n β s 1 =
      constrainedParisiValue β s - completedFractionalPressure n β s := by
  rw [vectorInterpolationMinimum_zero n hn β s hβ, vectorInterpolationMinimum_one n β s hs hs0]

end QuantitativePaper
