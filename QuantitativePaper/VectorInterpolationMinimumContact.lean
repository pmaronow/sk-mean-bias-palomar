module
public import QuantitativePaper.VectorInterpolationMinimumIntegral

@[expose] public section

/-! Touching the actual compact minimum at any minimizing measure gives
derivative contact once the fixed-profile derivative is supplied. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem vectorInterpolationMinimum_eq_of_minimizer (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β s t : ℝ) (hs : s≤1) (ht : t≤1)
    (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    vectorMeasureFunctional n μ β t s=vectorInterpolationMinimum n β s t := by
  obtain ⟨ν,hν,he,hle⟩:=compactMinimumValue_attained (scalarFloor s)
    (isCompact_scalarFloor s) (scalarFloor_nonempty s hs)
    (fun u μ=>vectorMeasureFunctional n μ β u s) t
    (continuous_vectorMeasureFunctional n hn β t s ht).continuousOn
  exact le_antisymm ((hmin ν hν).trans_eq he) (hle μ hμ)

theorem vectorInterpolationMinimum_derivative_contact_of_hasDerivAt
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s t d : ℝ)
    (hs : s≤1) (ht : t∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t)
    (hd : HasDerivAt (fun u=>vectorMeasureFunctional n μ β u s) d t) :
    deriv (vectorInterpolationMinimum n β s) t=d := by
  exact compactMinimumValue_derivative_contact (scalarFloor s)
    (isCompact_scalarFloor s) (scalarFloor_nonempty s hs)
    (fun u μ=>vectorMeasureFunctional n μ β u s) 0 1 t ht
    (fun u hu=>(continuous_vectorMeasureFunctional n hn β u s hu.2).continuousOn)
    μ hμ (vectorInterpolationMinimum_eq_of_minimizer hn μ β s t hs ht.2.le hμ hmin) hf d hd

theorem optimizedVectorInterpolationDefect_eq_of_hasDerivAt
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s t : ℝ)
    (hs : s≤1) (hβ : β≠0) (ht : t∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t)
    (hd : HasDerivAt (fun u=>vectorMeasureFunctional n μ β u s)
      (-β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le) t) :
    optimizedVectorInterpolationDefect n β s t=vectorInterpolationDefect (n:=n) μ s β t ht.2.le := by
  unfold optimizedVectorInterpolationDefect
  rw [vectorInterpolationMinimum_derivative_contact_of_hasDerivAt
    hn μ β s t _ hs ht hμ hmin hf hd]
  field_simp [hβ]

end QuantitativePaper
