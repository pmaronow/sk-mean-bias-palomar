module
public import QuantitativePaper.VectorBrownian
public import Paper.WeightedDrift
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Continuous vector gradient weights against a merely integrable drift.
Finite-dimensional basis expansion reduces the exact partition limit to the
proved signed scalar weighted integral theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace QuantitativePaper

def vectorIntegratedDrift {n : ℕ} (d : ℝ≥0 → Field n) (r : ℝ≥0) : Field n :=
  ∫ s in Ioc 0 r,d s ∂nonnegativeLebesgueMeasure

theorem field_clm_basis_expansion {n : ℕ} (L : Field n →L[ℝ] ℝ) (x : Field n) :
    L x = ∑ i : Fin n,x i*L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
  simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,smul_eq_mul]

theorem vectorIntegratedDrift_apply {n : ℕ} (d : ℝ≥0 → Field n) (r : ℝ≥0)
    (hd : IntegrableOn d (Ioc 0 r) nonnegativeLebesgueMeasure) (i : Fin n) :
    vectorIntegratedDrift d r i =
      ∫ s in Ioc 0 r,d s i ∂nonnegativeLebesgueMeasure := by
  have hi := (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).integral_comp_comm hd
  simpa only [innerSL_apply_apply,EuclideanSpace.basisFun_inner,vectorIntegratedDrift]
    using hi.symm

theorem uniformPartition_vector_weighted_drift_tendsto {n : ℕ}
    (d : ℝ≥0 → Field n) (w : ℝ≥0 → Field n →L[ℝ] ℝ) (t : ℝ≥0)
    (hd : IntegrableOn d (Ioc 0 t) nonnegativeLebesgueMeasure) (hw : Continuous w) :
    Tendsto (fun N => ∑ j ∈ Finset.range (N+1),
      w (uniformPartitionTime t (N+1) j)
        (vectorIntegratedDrift d (uniformPartitionTime t (N+1) (j+1))-
          vectorIntegratedDrift d (uniformPartitionTime t (N+1) j)))
      atTop (𝓝 (∫ s in Ioc 0 t,w s (d s) ∂nonnegativeLebesgueMeasure)) := by
  let e : Fin n → Field n := EuclideanSpace.basisFun (Fin n) ℝ
  let a : Fin n → ℝ≥0 → ℝ := fun i s => d s i
  let b : Fin n → ℝ≥0 → ℝ := fun i s => w s (e i)
  have hai (i : Fin n) : IntegrableOn (a i) (Ioc 0 t) nonnegativeLebesgueMeasure := by
    have hi := (innerSL ℝ (e i)).integrable_comp hd
    simpa only [IntegrableOn,innerSL_apply_apply,EuclideanSpace.basisFun_inner,e,a] using hi
  have hbi (i : Fin n) : Continuous (b i) := hw.clm_apply continuous_const
  have hprod (i : Fin n) : IntegrableOn (fun s => b i s*a i s)
      (Ioc 0 t) nonnegativeLebesgueMeasure := by
    obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hbi i).continuousOn : ContinuousOn (b i) (Icc 0 t))
    exact (hai i).bdd_mul (hbi i).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hK s ⟨hs.1.le,hs.2⟩)
  have hc (i : Fin n) := Paper.uniformPartition_weighted_integral_tendsto_signed
    (a i) (b i) t (hai i) (hbi i)
  have hl := tendsto_finset_sum Finset.univ (fun i _ => hc i)
  have htarget : (∑ i : Fin n,∫ s in Ioc 0 t,b i s*a i s ∂nonnegativeLebesgueMeasure) =
      ∫ s in Ioc 0 t,w s (d s) ∂nonnegativeLebesgueMeasure := by
    rw [← integral_finset_sum _ (fun i _=>hprod i)]
    apply integral_congr_ae
    filter_upwards with s
    rw [field_clm_basis_expansion]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [a,b,e]
    ring
  rw [htarget] at hl
  convert hl using 1
  funext N
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [field_clm_basis_expansion]
  apply Finset.sum_congr rfl
  intro i _
  have hj' : j < N+1 := Finset.mem_range.mp hj
  have hright := (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos N)
    (Nat.succ_le_iff.mpr hj')).2
  have hleft := (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos N)
    (Nat.le_of_lt hj')).2
  simp only [PiLp.sub_apply]
  rw [vectorIntegratedDrift_apply d _ (hd.mono_set (Ioc_subset_Ioc_right hright)),
    vectorIntegratedDrift_apply d _ (hd.mono_set (Ioc_subset_Ioc_right hleft))]
  dsimp only [a,b,e]
  ring

end QuantitativePaper
