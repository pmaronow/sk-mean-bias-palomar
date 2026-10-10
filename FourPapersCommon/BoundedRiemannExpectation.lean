module
public import Paper.WeightedDrift
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Genuine uniformly spaced left Riemann sums of bounded continuous random
paths converge in expectation. This will integrate the quadratic generator
after the adapted Gaussian cancellation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon

def boundedPartitionLeftSum (w : ℝ≥0 → ℝ) (t : ℝ≥0) (N : ℕ) : ℝ :=
  ∑ j∈Finset.range N,w (uniformPartitionTime t N j)*((t : ℝ)/(N : ℝ))

theorem boundedPartitionLeftSum_tendsto (w : ℝ≥0 → ℝ) (hw : Continuous w) (t : ℝ≥0) :
    Tendsto (fun N=>boundedPartitionLeftSum w t (N+1)) atTop
      (𝓝 (∫ s in Ioc 0 t,w s ∂nonnegativeLebesgueMeasure)) := by
  have hl := Paper.uniformPartition_weighted_integral_tendsto_signed
    (fun _=> (1 : ℝ)) w t
    (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)) hw
  have hint (r : ℝ≥0) : (∫ s in Ioc 0 r,(1 : ℝ) ∂nonnegativeLebesgueMeasure) = r := by
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,
      NNReal.coe_zero,sub_zero,
      ENNReal.toReal_ofReal r.coe_nonneg,smul_eq_mul,mul_one]
  simp only [hint,mul_one] at hl
  convert hl using 1
  funext N
  apply Finset.sum_congr rfl
  intro j _
  have hrt := monotone_uniformPartitionTime t (N+1) (Nat.le_add_right j 1)
  have hh := dist_uniformPartitionTime_succ_eq t (Nat.succ_pos N) j
  rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt))] at hh
  have he : ((uniformPartitionTime t (N+1) (j+1) : ℝ≥0) : ℝ)-
      ((uniformPartitionTime t (N+1) j : ℝ≥0) : ℝ) = (t : ℝ)/((N+1 : ℕ) : ℝ) := by
    simpa only [NNReal.coe_div,NNReal.coe_natCast] using hh
  exact congrArg (fun a=>w (uniformPartitionTime t (N+1) j)*a) he.symm

theorem boundedPartitionLeftSum_bound (w : ℝ≥0 → ℝ) (K : ℝ≥0) (t : ℝ≥0)
    (hK : ∀ s∈Icc 0 t,|w s| ≤ K) {N : ℕ} (hN : 0 < N) :
    |boundedPartitionLeftSum w t N| ≤ K*t := by
  have hdt : 0 ≤ (t : ℝ)/(N : ℝ) := by positivity
  calc
    _ ≤ ∑ j∈Finset.range N,|w (uniformPartitionTime t N j)*((t : ℝ)/(N : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.range N,(K : ℝ)*((t : ℝ)/(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_of_nonneg hdt]
      exact mul_le_mul_of_nonneg_right
        (hK _ (uniformPartitionTime_mem_Icc_of_le t hN (Finset.mem_range.mp hj).le)) hdt
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hne : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp

theorem tendsto_integral_boundedPartitionLeftSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (w : ℝ≥0 → Ω → ℝ)
    (hw : ∀ s,StronglyMeasurable (w s)) (hc : ∀ ω,Continuous (fun s=>w s ω))
    (K : ℝ≥0) (t : ℝ≥0) (hK : ∀ s∈Icc 0 t,∀ ω,|w s ω| ≤ K) :
    Tendsto (fun N=>∫ ω,boundedPartitionLeftSum (fun s=>w s ω) t (N+1) ∂P)
      atTop (𝓝 (∫ ω,(∫ s in Ioc 0 t,w s ω ∂nonnegativeLebesgueMeasure) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω=>(K : ℝ)*t)
  · intro N
    apply StronglyMeasurable.aestronglyMeasurable
    unfold boundedPartitionLeftSum
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact (hw _).mul stronglyMeasurable_const
  · exact integrable_const _
  · intro N
    apply Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs] using boundedPartitionLeftSum_bound
      (fun s=>w s ω) K t (fun s hs=>hK s hs ω) (Nat.succ_pos N)
  · exact Eventually.of_forall fun ω=>boundedPartitionLeftSum_tendsto (fun s=>w s ω) (hc ω) t

end FourPapersCommon
