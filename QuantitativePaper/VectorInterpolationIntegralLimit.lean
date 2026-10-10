module
public import QuantitativePaper.VectorGridInterpolationIntegral

@[expose] public section

/-! Dominated passage of the genuine grid interpolation identity. The
conditional-moment convergence hypothesis is explicit here; the physical
source theorem must instantiate it from the actual Wiener law. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem vectorMeasureFunctional_interpolation_integral_of_grid_defect
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (hD : ∀t : ℝ,∀ht:t<1,Tendsto
      (fun j=>vectorInterpolationDefect (n:=n)
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le) atTop
      (𝓝 (vectorInterpolationDefect (n:=n) μ s β t ht.le)))
    (r u : ℝ) (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) (hru : r≤u) :
    vectorMeasureFunctional n μ β u s-vectorMeasureFunctional n μ β r s=
      -β^2/4*(∫t in r..u,vectorInterpolationTimeDefect (n:=n) μ s β t) := by
  have hInts : Tendsto (fun j=>∫t in r..u,vectorInterpolationTimeDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t) atTop
      (𝓝 (∫t in r..u,vectorInterpolationTimeDefect (n:=n) μ s β t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>4*(1-s))
    · exact .of_forall fun j=>(measurable_vectorInterpolationTimeDefect hn
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β hβ).aestronglyMeasurable
    · exact .of_forall fun j=>.of_forall fun t _=>by
        rw [Real.norm_of_nonneg (vectorInterpolationTimeDefect_bounds hn
          (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t hs.2.le hβ).1]
        exact (vectorInterpolationTimeDefect_bounds hn
          (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t hs.2.le hβ).2
    · exact intervalIntegrable_const
    · exact .of_forall fun t _=>by
        by_cases ht:t<1
        · simpa only [vectorInterpolationTimeDefect_of_lt _ _ _ _ ht] using hD t ht
        · simpa only [vectorInterpolationTimeDefect,dif_neg ht] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
  have hF:=(tendsto_vectorMeasureFunctional_grid hn μ β u s hu.2).sub
    (tendsto_vectorMeasureFunctional_grid hn μ β r s hr.2)
  have hR:=(hInts.const_mul (-β^2/4)).congr' (.of_forall fun j=>
    (vectorMeasureFunctional_grid_interpolation_integral hn μ j β s hs hμ hβ r u hr hu hru).2.symm)
  exact tendsto_nhds_unique hF hR

theorem hasDerivAt_vectorMeasureFunctional_interpolation_of_grid_defect
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (hD : ∀t : ℝ,∀ht:t<1,Tendsto
      (fun j=>vectorInterpolationDefect (n:=n)
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le) atTop
      (𝓝 (vectorInterpolationDefect (n:=n) μ s β t ht.le)))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u=>vectorMeasureFunctional n μ β u s)
      (-β^2/4*vectorInterpolationDefect (n:=n) μ s β t ht.2.le) t := by
  let D:=vectorInterpolationTimeDefect (n:=n) μ s β
  have hi:=intervalIntegrable_vectorInterpolationTimeDefect hn μ s β hs.2.le hβ 0 t
  have hc : ContinuousAt D t:=
    (continuousOn_vectorInterpolationTimeDefect hn μ s β hβ).continuousAt
      (isOpen_Iio.mem_nhds ht.2)
  have hp:=intervalIntegral.integral_hasDerivAt_right hi
    (measurable_vectorInterpolationTimeDefect hn μ s β hβ).stronglyMeasurable.stronglyMeasurableAtFilter hc
  have hd:=(hp.const_mul (-β^2/4)).const_add (vectorMeasureFunctional n μ β 0 s)
  have he : (fun u=>vectorMeasureFunctional n μ β u s)=ᶠ[𝓝 t]
      fun u=>vectorMeasureFunctional n μ β 0 s+(-β^2/4)*(∫v in (0:ℝ)..u,D v) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    have hI:=vectorMeasureFunctional_interpolation_integral_of_grid_defect
      hn μ β s hs hμ hβ hD 0 u (by norm_num) ⟨hu.1.le,hu.2.le⟩ hu.1.le
    dsimp only [D]
    linarith
  simpa only [D,vectorInterpolationTimeDefect_of_lt _ _ _ _ ht.2] using hd.congr_of_eventuallyEq he

end QuantitativePaper
