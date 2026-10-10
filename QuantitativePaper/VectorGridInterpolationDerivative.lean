module
public import QuantitativePaper.VectorRootReplicaTelescope
public import QuantitativePaper.VectorGridReplicaDefect
public import QuantitativePaper.VectorInterpolationDefect
public import QuantitativePaper.ResponseDyadicCrossingStage

@[expose] public section

/-! The actual dyadic-grid interpolation derivative uses the literal
full-past conditionally independent terminal-spin replica defect. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2400000
variable {n : ℕ}

theorem vectorRootCascadeSplitDefect_grid_eq_actual (hn : 0<n) (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t a : ℝ) (ha : 0≤a) (hβ : β≠0) (ht : t<1)
    (p : ℕ) (hp : p≤vectorDyadicIndex j+2) :
    (∫z,(overlap n z.1 z.2-(vectorRootInterpolationOverlap
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) p:ℝ))^2∂finiteStateCascadeSplitLaw
      (fun _ : Configuration n=>0)
      (vectorRootInterpolationMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a)
      (vectorRootInterpolationScaledDirection (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t)
      p (vectorDyadicIndex j+3-p) 0)=
      vectorConditionalReplicaDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a ht.le
        (vectorRootInterpolationOverlap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) p) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hq:s.q 1=0:=by simp [s,Paper.parisiGridRSBScheme]
  have hfinite:=vectorRootCascadeSplitDefect_eq_finite hn s β t a ha hβ ht hq p hp
    (vectorRootInterpolationOverlap s p)
  have hactual:=vectorConditionalReplicaDefect_grid_eq_finite hn μ j β t a hβ ht
    (vectorDyadicIndex j+3-p) (by omega) (vectorRootInterpolationOverlap s p) rfl
  exact hfinite.trans hactual.symm

theorem finiteVectorRootInterpolationTime_grid_eq_defect (hn : 0<n) (μ : Paper.ParisiMeasure)
    (j : ℕ) (β a : ℝ) (ha : 0≤a) (hμ : μ∈scalarFloor a) (hβ : β≠0)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    finiteVectorRootInterpolationTime (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β a ha t=
      -β^2/4*vectorInterpolationDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a β t ht.2.le := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hq:s.q 1=0:=by simp [s,Paper.parisiGridRSBScheme]
  have hm:a ≤ s.m 1:=by
    rw [show s.m 1=Paper.parisiCDF μ 0 by exact parisiGridRSBScheme_firstMass μ _]
    exact scalarFloor_cdf_lower hμ le_rfl
  rw [finiteVectorRootInterpolationTime_eq_replica_defects hn s β a ha hq t ht]
  have he : (∑p∈Finset.range (vectorDyadicIndex j+2),
      (vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
      (∫z,(overlap n z.1 z.2-(vectorRootInterpolationOverlap s (p+1):ℝ))^2∂finiteStateCascadeSplitLaw
        (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
        (vectorRootInterpolationScaledDirection (n:=n) s β t) (p+1) (vectorDyadicIndex j+3-(p+1)) 0))=
      ∑p∈Finset.range (vectorDyadicIndex j+2),(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
        vectorConditionalReplicaDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a ht.2.le
          (vectorRootInterpolationOverlap s (p+1)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [vectorRootCascadeSplitDefect_grid_eq_actual hn μ j β t a ha hβ ht.2 (p+1)
      (by have:=Finset.mem_range.mp hp;omega)]
  rw [he,vectorRootInterpolation_free_measure_sum s a hm,
    vectorProfileFreeMeasure_eq_actual_free s a ha hm hq,FRSB.parisiSchemeMeasure_grid_eq]
  rfl

theorem hasDerivAt_vectorMeasureFunctional_grid_interpolation (hn : 0<n) (μ : Paper.ParisiMeasure)
    (j : ℕ) (β a : ℝ) (ha : 0<a) (hμ : μ∈scalarFloor a) (hβ : β≠0)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u=>vectorMeasureFunctional n (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β u a)
      (-β^2/4*vectorInterpolationDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a β t ht.2.le) t := by
  have hq : (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q 1=0:=by
    simp [Paper.parisiGridRSBScheme]
  have hd:=hasDerivAt_finiteVectorFunctional_root_interpolation (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β a ha hq t ht
  rw [finiteVectorRootInterpolationTime_grid_eq_defect hn μ j β a ha.le hμ hβ t ht] at hd
  have he : (fun u=>vectorMeasureFunctional n (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β u a)=ᶠ[𝓝 t]
      (fun u=>finiteVectorFunctional n (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β u a) := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with u hu
    exact vectorMeasureFunctional_grid_eq_finite μ j β u a ha.ne' hu.le
  exact hd.congr_of_eventuallyEq he

end QuantitativePaper
