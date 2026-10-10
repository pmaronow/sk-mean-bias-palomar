module
public import QuantitativePaper.VectorConditionalReplicaDefectLimit
public import QuantitativePaper.VectorMeanProductMovingTime
public import QuantitativePaper.VectorInterpolationFreeGridLimit

@[expose] public section

/-! Actual conditional spin-pair and mean convergence, followed by exact
free-measure pushforward and bounded convergence, closes the physical grid
defect limit for every admissible measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
variable {n : ℕ} {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
variable {ν : J→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure}
variable {qj : J→Paper.Overlap} {q : Paper.Overlap}
set_option maxHeartbeats 1600000

theorem tendsto_vectorConditionalReplicaDefect_of_weak_and_time
    (hn : 0<n) (β t s : ℝ) (hβ : β≠0) (ht : t<1)
    (hν : Tendsto ν l (𝓝 μ)) (hq : Tendsto qj l (𝓝 q)) :
    Tendsto (fun j=>vectorConditionalReplicaDefect (n:=n) (ν j) β t s ht.le (qj j)) l
      (𝓝 (vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q)) :=
  tendsto_vectorConditionalReplicaDefect_of_weak_and_time_of_mean_limits hn β t s hβ ht hν hq
    (fun i=>tendsto_integral_vectorBaseMeanProduct_of_weak_and_time β t s ht hν hq i i)

theorem tendsto_vectorInterpolationDefect_grid (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hβ : β≠0) (ht : t<1) :
    Tendsto (fun j=>vectorInterpolationDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le) atTop
      (𝓝 (vectorInterpolationDefect (n:=n) μ s β t ht.le)) := by
  apply tendsto_vectorInterpolationDefect_grid_of_conditional_limits hn μ s β t hs hμ hβ ht
  intro q
  exact tendsto_vectorConditionalReplicaDefect_of_weak_and_time hn β t s hβ ht
    ((FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex)
    ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)

end QuantitativePaper
