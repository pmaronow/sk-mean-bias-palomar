module
public import QuantitativePaper.VectorInterpolationDefect
public import QuantitativeFollowup.ParisiFreeGrid

@[expose] public section

/-! Exact free-measure transport reduces the physical defect limit to
the conditional replica moments at the genuine upward-rounded nodes. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
open QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem vectorInterpolationDefect_grid_eq_free_pushforward (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hβ : β≠0) (ht : t<1) (j : ℕ) :
    vectorInterpolationDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le=
      ∫q,vectorConditionalReplicaDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        β t s ht.le (Paper.parisiGridRound (vectorDyadicIndex j) q)∂parisiFreeMeasure μ s := by
  unfold vectorInterpolationDefect
  exact integral_parisiFreeMeasure_grid μ s hs hμ (vectorDyadicIndex j)
    (vectorConditionalReplicaDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s ht.le)
    (measurable_vectorConditionalReplicaDefect hn
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s hβ ht)

theorem tendsto_vectorInterpolationDefect_grid_of_conditional_limits
    (hn : 0<n) (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hβ : β≠0) (ht : t<1)
    (hDq : ∀q : Paper.Overlap,Tendsto (fun j=>vectorConditionalReplicaDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s ht.le
        (Paper.parisiGridRound (vectorDyadicIndex j) q)) atTop
      (𝓝 (vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q))) :
    Tendsto (fun j=>vectorInterpolationDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le) atTop
      (𝓝 (vectorInterpolationDefect (n:=n) μ s β t ht.le)) := by
  have hlim : Tendsto (fun j=>∫q,vectorConditionalReplicaDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s ht.le
        (Paper.parisiGridRound (vectorDyadicIndex j) q)∂parisiFreeMeasure μ s) atTop
      (𝓝 (vectorInterpolationDefect (n:=n) μ s β t ht.le)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _=>(4:ℝ))
    · exact .of_forall fun j=>((measurable_vectorConditionalReplicaDefect hn
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s hβ ht).comp
          (Paper.measurable_parisiGridRound (vectorDyadicIndex j))).aestronglyMeasurable
    · exact .of_forall fun j=>.of_forall fun q=>by
        rw [Real.norm_of_nonneg (vectorConditionalReplicaDefect_bounds hn
          (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s ht.le
            (Paper.parisiGridRound (vectorDyadicIndex j) q)).1]
        exact (vectorConditionalReplicaDefect_bounds hn
          (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s ht.le
            (Paper.parisiGridRound (vectorDyadicIndex j) q)).2
    · exact integrable_const 4
    · exact .of_forall hDq
  exact hlim.congr' (.of_forall fun j=>
    (vectorInterpolationDefect_grid_eq_free_pushforward hn μ s β t hs hμ hβ ht j).symm)

end QuantitativePaper
