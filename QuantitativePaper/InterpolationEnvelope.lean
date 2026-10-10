module
public import QuantitativePaper.VectorInterpolationDerivative
public import QuantitativePaper.VectorInterpolationMonotonicity

@[expose] public section

/-! The complete literal optimized interpolation proposition. All laws,
fixed-profile derivatives and limiting conditional replica moments are
the genuine completed finite-SK objects. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 2000000

theorem interpolation_envelope (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) (1/2)) :
    (∀μ∈scalarFloor s,
      LipschitzOnWith (vectorInterpolationLipschitzConstant β s (by linarith [hs.2]))
        (fun t=>vectorMeasureFunctional n μ β t s) (Icc (0:ℝ) 1) ∧
      ContDiffOn ℝ 1 (fun t=>vectorMeasureFunctional n μ β t s) (Ioo (0:ℝ) 1) ∧
      ∀t : ℝ,∀ht:t∈Ioo (0:ℝ) 1,
        HasDerivAt (fun u=>vectorMeasureFunctional n μ β u s)
          (-β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le) t) ∧
    (∀μ∈scalarFloor s,∀t : ℝ,∀ht:t∈Ioo (0:ℝ) 1,
      0≤vectorInterpolationDefect (n:=n) μ s β t ht.2.le ∧
        vectorInterpolationDefect (n:=n) μ s β t ht.2.le≤4*(1-s)) ∧
    (∀t∈Icc (0:ℝ) 1,∃μ∈scalarFloor s,∀ν∈scalarFloor s,
      vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) ∧
    LipschitzOnWith (vectorInterpolationLipschitzConstant β s (by linarith [hs.2]))
      (vectorInterpolationMinimum n β s) (Icc (0:ℝ) 1) ∧
    (vectorInterpolationMinimum n β s 0=constrainedParisiValue β s ∧
      vectorInterpolationMinimum n β s 1=completedFractionalPressure n β s) ∧
    (∀t : ℝ,∀ht:t∈Ioo (0:ℝ) 1,
      DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t→
      ∀μ∈scalarFloor s,
      (∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)→
      deriv (vectorInterpolationMinimum n β s) t=
        -β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le) ∧
    (IntervalIntegrable (optimizedVectorInterpolationDefect n β s) volume 0 1 ∧
      constrainedParisiValue β s-completedFractionalPressure n β s=
        β^2/4*(∫t in (0:ℝ)..1,optimizedVectorInterpolationDefect n β s t)) ∧
    (∀ᵐt : ℝ,∀ht:t∈Ioo (0:ℝ) 1,∀μ∈scalarFloor s,
      (∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)→
      optimizedVectorInterpolationDefect n β s t=vectorInterpolationDefect (n:=n) μ s β t ht.2.le) := by
  have hs1 : s∈Ioo (0:ℝ) 1:=⟨hs.1,by linarith [hs.2]⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro μ hμ
    exact ⟨vectorMeasureFunctional_interpolation_lipschitz hn μ β s hs1 hμ hβ.ne',
      contDiffOn_vectorMeasureFunctional_interpolation hn μ β s hs1 hμ hβ.ne',
      fun t ht=>hasDerivAt_vectorMeasureFunctional_interpolation hn μ β s hs1 hμ hβ.ne' t ht⟩
  · intro μ hμ t ht
    exact vectorInterpolationDefect_bounds hn μ s β t hs1.2.le hβ.ne' ht.2
  · intro t ht
    exact exists_vectorMeasure_minimizer n hn β t s ht.2 hs1.2.le
  · exact vectorInterpolationMinimum_lipschitz n hn β s hs1 hβ.ne'
  · exact ⟨vectorInterpolationMinimum_zero n hn β s hβ.ne',
      vectorInterpolationMinimum_one n β s hs1.2.le hs1.1.ne'⟩
  · intro t ht hf μ hμ hmin
    exact vectorInterpolationMinimum_derivative_contact hn μ β s hs1 hμ hβ.ne' t ht hmin hf
  · exact vectorInterpolationMinimum_integral n hn β s hs1 hβ.ne'
  · filter_upwards [vectorInterpolationMinimum_ae_differentiable n hn β s hs1 hβ.ne'] with t hdiff
    intro ht μ hμ hmin
    exact optimizedVectorInterpolationDefect_eq_of_minimizer hn μ β s hs1 hμ hβ.ne' t ht hmin
      (hdiff ⟨ht.1.le,ht.2.le⟩)

end QuantitativePaper
