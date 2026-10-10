module
public import QuantitativePaper.VectorDriftBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! The actual weighted vector drift sums converge in expectation. The drift
need only be jointly measurable and uniformly bounded, while the gradient
weight has continuous paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
variable {Ω : Type*} [MeasurableSpace Ω]

theorem stronglyMeasurable_vectorIntegratedDrift {n : ℕ}
    (d : ℝ≥0 → Ω → Field n) (hd : Measurable (Function.uncurry d)) (r : ℝ≥0) :
    StronglyMeasurable (fun ω=>vectorIntegratedDrift (fun s=>d s ω) r) := by
  exact hd.stronglyMeasurable.integral_prod_left

theorem stronglyMeasurable_vectorWeightedDriftApprox {n : ℕ}
    (d : ℝ≥0 → Ω → Field n) (hd : Measurable (Function.uncurry d))
    (w : ℝ≥0 → Ω → Field n →L[ℝ] ℝ) (hw : ∀ s,StronglyMeasurable (w s))
    (t : ℝ≥0) (N : ℕ) :
    StronglyMeasurable (fun ω=>vectorWeightedDriftApprox
      (fun s=>d s ω) (fun s=>w s ω) t N) := by
  unfold vectorWeightedDriftApprox
  apply Finset.stronglyMeasurable_fun_sum
  intro j _
  exact (show Continuous (fun p : (Field n →L[ℝ] ℝ) × Field n => p.1 p.2) from
    continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hw _).prodMk ((stronglyMeasurable_vectorIntegratedDrift d hd _).sub
        (stronglyMeasurable_vectorIntegratedDrift d hd _)))

theorem tendsto_integral_vectorWeightedDriftApprox {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (d : ℝ≥0 → Ω → Field n) (hd : Measurable (Function.uncurry d))
    (D : ℝ≥0) (hD : ∀ s ω,‖d s ω‖ ≤ D)
    (w : ℝ≥0 → Ω → Field n →L[ℝ] ℝ) (hw : ∀ s,StronglyMeasurable (w s))
    (hc : ∀ ω,Continuous (fun s=>w s ω)) (K : ℝ≥0) (t : ℝ≥0)
    (hK : ∀ s∈Icc 0 t,∀ ω,‖w s ω‖ ≤ K)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable Z) (C : ℝ≥0) (hC : ∀ ω,‖Z ω‖ ≤ C) :
    Tendsto (fun N=>∫ ω,Z ω*vectorWeightedDriftApprox
      (fun s=>d s ω) (fun s=>w s ω) t (N+1) ∂P) atTop
      (𝓝 (∫ ω,Z ω*(∫ s in Ioc 0 t,w s ω (d s ω)
        ∂nonnegativeLebesgueMeasure) ∂P)) := by
  have hds (ω : Ω) : Measurable (fun s=>d s ω) :=
    hd.comp (measurable_id.prodMk measurable_const)
  apply tendsto_integral_of_dominated_convergence
    (fun _ : Ω=>(C : ℝ)*K*D*t)
  · intro N
    exact (hZ.mul (stronglyMeasurable_vectorWeightedDriftApprox d hd w hw t (N+1))).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    apply Eventually.of_forall
    intro ω
    rw [norm_mul,Real.norm_eq_abs]
    have hb := vectorWeightedDriftApprox_bound (fun s=>d s ω) (hds ω) D
      (fun s=>hD s ω) (fun s=>w s ω) K t (fun s hs=>hK s hs ω) (Nat.succ_pos N)
    calc
      _ ≤ (C : ℝ)*(K*D*t) := mul_le_mul (hC ω) hb (abs_nonneg _) C.coe_nonneg
      _ = _ := by ring
  · apply Eventually.of_forall
    intro ω
    have hl := uniformPartition_vector_weighted_drift_tendsto
      (fun s=>d s ω) (fun s=>w s ω) t
      (integrableOn_bounded_vector_drift _ (hds ω) D (fun s=>hD s ω) 0 t) (hc ω)
    exact tendsto_const_nhds.mul hl

end QuantitativePaper
