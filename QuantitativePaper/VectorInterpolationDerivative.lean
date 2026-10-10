module
public import QuantitativePaper.VectorInterpolationDefectGridLimit
public import QuantitativePaper.VectorInterpolationIntegralLimit
public import QuantitativePaper.VectorInterpolationMinimumContact
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The actual arbitrary-measure physical interpolation is C¹. The
minimum derivative touches every genuine minimizing measure; no analytic
limit or measurable-selection conclusion is supplied as a premise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 2000000

theorem vectorMeasureFunctional_interpolation_integral
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (r u : ℝ) (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) (hru : r≤u) :
    vectorMeasureFunctional n μ β u s-vectorMeasureFunctional n μ β r s=
      -β^2/4*(∫t in r..u,vectorInterpolationTimeDefect (n:=n) μ s β t) :=
  vectorMeasureFunctional_interpolation_integral_of_grid_defect hn μ β s hs hμ hβ
    (fun t ht=>tendsto_vectorInterpolationDefect_grid hn μ s β t ⟨hs.1.le,hs.2.le⟩ hμ hβ ht)
    r u hr hu hru

theorem hasDerivAt_vectorMeasureFunctional_interpolation
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u=>vectorMeasureFunctional n μ β u s)
      (-β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le) t :=
  hasDerivAt_vectorMeasureFunctional_interpolation_of_grid_defect hn μ β s hs hμ hβ
    (fun u hu=>tendsto_vectorInterpolationDefect_grid hn μ s β u ⟨hs.1.le,hs.2.le⟩ hμ hβ hu) t ht

theorem continuousOn_deriv_vectorMeasureFunctional_interpolation
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    ContinuousOn (deriv (fun t=>vectorMeasureFunctional n μ β t s)) (Ioo (0:ℝ) 1) := by
  have hc:=((continuousOn_vectorInterpolationTimeDefect hn μ s β hβ).mono
    (show Ioo (0:ℝ) 1⊆Iio 1 from fun t ht=>ht.2)).const_mul (-β^2/4)
  apply hc.congr
  intro t ht
  simpa only [vectorInterpolationTimeDefect_of_lt μ s β t ht.2] using
    (hasDerivAt_vectorMeasureFunctional_interpolation hn μ β s hs hμ hβ t ht).deriv

theorem contDiffOn_vectorMeasureFunctional_interpolation
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    ContDiffOn ℝ 1 (fun t=>vectorMeasureFunctional n μ β t s) (Ioo (0:ℝ) 1) := by
  rw [show (1:ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun t ht=>(hasDerivAt_vectorMeasureFunctional_interpolation
    hn μ β s hs hμ hβ t ht).differentiableAt.differentiableWithinAt,by simp,?_⟩
  exact contDiffOn_zero.mpr (continuousOn_deriv_vectorMeasureFunctional_interpolation hn μ β s hs hμ hβ)

theorem vectorInterpolationMinimum_derivative_contact
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t) :
    deriv (vectorInterpolationMinimum n β s) t=
      -β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le :=
  vectorInterpolationMinimum_derivative_contact_of_hasDerivAt hn μ β s t _ hs.2.le ht hμ hmin hf
    (hasDerivAt_vectorMeasureFunctional_interpolation hn μ β s hs hμ hβ t ht)

theorem optimizedVectorInterpolationDefect_eq_of_minimizer
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t) :
    optimizedVectorInterpolationDefect n β s t=vectorInterpolationDefect (n:=n) μ s β t ht.2.le :=
  optimizedVectorInterpolationDefect_eq_of_hasDerivAt hn μ β s t hs.2.le hβ ht hμ hmin hf
    (hasDerivAt_vectorMeasureFunctional_interpolation hn μ β s hs hμ hβ t ht)

end QuantitativePaper
