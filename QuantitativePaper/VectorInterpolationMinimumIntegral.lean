module
public import QuantitativePaper.VectorInterpolationLipschitz
public import QuantitativePaper.VectorInterpolationMinimumEndpoints
public import FourPapersCommon.MinimumEnvelopeIntegral

@[expose] public section

/-! The actual compact minimum is Lipschitz. Its endpoint gap is an
integral of its genuine almost-everywhere derivative, without choosing
or assuming a measurable family of minimizing measures. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1600000

def optimizedVectorInterpolationDefect (n : ℕ) (β s t : ℝ) : ℝ :=
  -4*deriv (vectorInterpolationMinimum n β s) t/β^2

theorem vectorInterpolationMinimum_lipschitz (n : ℕ) (hn : 0<n)
    (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) :
    LipschitzOnWith (vectorInterpolationLipschitzConstant β s hs.2.le)
      (vectorInterpolationMinimum n β s) (Icc (0:ℝ) 1) := by
  apply lipschitzOnWith_minimum_envelope
    (fun t μ=>vectorMeasureFunctional n μ β t s)
    (vectorInterpolationMinimum n β s) (scalarFloor s) (Icc 0 1)
  · intro t ht μ hμ
    obtain ⟨ν,hν,he,hle⟩:=compactMinimumValue_attained (scalarFloor s)
      (isCompact_scalarFloor s) (scalarFloor_nonempty s hs.2.le)
      (fun t μ=>vectorMeasureFunctional n μ β t s) t
      (continuous_vectorMeasureFunctional n hn β t s ht.2).continuousOn
    exact hle μ hμ
  · intro t ht
    obtain ⟨μ,hμ,he,_⟩:=compactMinimumValue_attained (scalarFloor s)
      (isCompact_scalarFloor s) (scalarFloor_nonempty s hs.2.le)
      (fun t μ=>vectorMeasureFunctional n μ β t s) t
      (continuous_vectorMeasureFunctional n hn β t s ht.2).continuousOn
    exact ⟨μ,hμ,he⟩
  · intro μ hμ
    exact vectorMeasureFunctional_interpolation_lipschitz hn μ β s hs hμ hβ

theorem vectorInterpolationMinimum_ae_differentiable (n : ℕ) (hn : 0<n)
    (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) :
    ∀ᵐt : ℝ,t∈Icc (0:ℝ) 1→DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t := by
  have hl:=vectorInterpolationMinimum_lipschitz n hn β s hs hβ
  rw [←uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hl ⊢
  exact (lipschitz_envelope_endpoint_integral _ 0 1 _ hl).2.1

theorem vectorInterpolationMinimum_integral (n : ℕ) (hn : 0<n)
    (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) :
    IntervalIntegrable (optimizedVectorInterpolationDefect n β s) volume 0 1 ∧
      constrainedParisiValue β s-completedFractionalPressure n β s=
        β^2/4*(∫t in (0:ℝ)..1,optimizedVectorInterpolationDefect n β s t) := by
  have hc : β^2/4≠0:=div_ne_zero (pow_ne_zero 2 hβ) (by norm_num)
  have hl:=vectorInterpolationMinimum_lipschitz n hn β s hs hβ
  rw [←uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hl
  have he:=minimumEnvelopeDefect_integral (scalarFloor s)
    (fun t μ=>vectorMeasureFunctional n μ β t s) 0 1 (β^2/4) hc _ hl
  have hEq : minimumEnvelopeDefect (scalarFloor s)
      (fun t μ=>vectorMeasureFunctional n μ β t s) (β^2/4)=
      optimizedVectorInterpolationDefect n β s := by
    funext t
    unfold minimumEnvelopeDefect optimizedVectorInterpolationDefect vectorInterpolationMinimum
    field_simp
  rw [hEq] at he
  refine ⟨he.1,?_⟩
  have hgap:=he.2
  change vectorInterpolationMinimum n β s 0-vectorInterpolationMinimum n β s 1=_ at hgap
  rw [vectorInterpolationMinimum_endpoint_gap n hn β s hβ hs.2.le hs.1.ne'] at hgap
  exact hgap

end QuantitativePaper
