module
public import FRSB.CDFMeasureExt
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-! The actual generalized inverse of an overlap CDF. The root and
terminal atoms are handled by right continuity; no atom-free hypothesis
is imposed. -/
noncomputable section
open MeasureTheory Set Filter Paper
open scoped Topology
namespace QuantitativeFollowup

def quantileLevel (u : ℝ) : ℝ := min 1 (max 0 u)

theorem quantileLevel_mem (u : ℝ) : quantileLevel u ∈ Icc (0:ℝ) 1 := by
  unfold quantileLevel
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem quantileLevel_eq {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : quantileLevel u=u := by
  simp only [quantileLevel,max_eq_right hu.1,min_eq_right hu.2]

theorem quantileLevel_monotone : Monotone quantileLevel := by
  intro u v huv
  exact min_le_min le_rfl (max_le_max le_rfl huv)

def parisiQuantileSet (μ : Paper.ParisiMeasure) (u : ℝ) : Set ℝ :=
  {q | q ∈ Icc (0:ℝ) 1 ∧ quantileLevel u ≤ parisiCDF μ q}

def parisiQuantile (μ : Paper.ParisiMeasure) (u : ℝ) : ℝ := sInf (parisiQuantileSet μ u)

theorem parisiQuantileSet_nonempty (μ : Paper.ParisiMeasure) (u : ℝ) :
    (parisiQuantileSet μ u).Nonempty := by
  refine ⟨1,⟨by constructor <;> norm_num,?_⟩⟩
  rw [parisiCDF_eq_one_of_one_le μ (by norm_num)]
  exact (quantileLevel_mem u).2

theorem parisiQuantileSet_bddBelow (μ : Paper.ParisiMeasure) (u : ℝ) :
    BddBelow (parisiQuantileSet μ u) := ⟨0,fun _ hq => hq.1.1⟩

theorem parisiQuantile_mem (μ : Paper.ParisiMeasure) (u : ℝ) :
    parisiQuantile μ u ∈ Icc (0:ℝ) 1 := by
  refine ⟨le_csInf (parisiQuantileSet_nonempty μ u) (fun _ hq => hq.1.1),?_⟩
  apply csInf_le (parisiQuantileSet_bddBelow μ u)
  exact ⟨by constructor <;> norm_num,by
    rw [parisiCDF_eq_one_of_one_le μ (by norm_num)]
    exact (quantileLevel_mem u).2⟩

theorem quantileLevel_le_parisiCDF_quantile (μ : Paper.ParisiMeasure) (u : ℝ) :
    quantileLevel u ≤ parisiCDF μ (parisiQuantile μ u) := by
  have hc := (FRSB.parisiCDF_right_continuous μ (parisiQuantile μ u)).mono
    Ioi_subset_Ici_self
  apply ge_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨q,hq,hqx⟩ := (csInf_lt_iff (parisiQuantileSet_bddBelow μ u)
    (parisiQuantileSet_nonempty μ u)).mp hx
  exact hq.2.trans (parisiCDF_monotone μ hqx.le)

theorem parisiQuantile_le_iff (μ : Paper.ParisiMeasure) (u x : ℝ)
    (hx : x ∈ Icc (0:ℝ) 1) :
    parisiQuantile μ u ≤ x ↔ quantileLevel u ≤ parisiCDF μ x := by
  constructor
  · intro hq
    exact (quantileLevel_le_parisiCDF_quantile μ u).trans (parisiCDF_monotone μ hq)
  · intro hu
    exact csInf_le (parisiQuantileSet_bddBelow μ u) ⟨hx,hu⟩

theorem parisiQuantile_monotone (μ : Paper.ParisiMeasure) : Monotone (parisiQuantile μ) := by
  intro u v huv
  apply (parisiQuantile_le_iff μ u _ (parisiQuantile_mem μ v)).mpr
  exact (quantileLevel_monotone huv).trans (quantileLevel_le_parisiCDF_quantile μ v)

theorem parisiQuantile_measurable (μ : Paper.ParisiMeasure) : Measurable (parisiQuantile μ) :=
  (parisiQuantile_monotone μ).measurable

theorem le_parisiCDF_quantile (μ : Paper.ParisiMeasure) {u : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) : u ≤ parisiCDF μ (parisiQuantile μ u) := by
  simpa only [quantileLevel_eq hu] using quantileLevel_le_parisiCDF_quantile μ u

end QuantitativeFollowup
