module
public import FourPapersCommon.MonotoneBinIntervals
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! Exact measure bounds for the two boundary strips of a bounded interval. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def intervalBoundaryStrips (I : Set ℝ) (δ : ℝ) : Set ℝ :=
  I∩(Icc (sInf I) (sInf I+δ)∪Icc (sSup I-δ) (sSup I))

theorem volume_intervalBoundaryStrips_le (I : Set ℝ) (δ : ℝ) (hδ : 0≤δ) :
    volume.real (intervalBoundaryStrips I δ)≤2*δ := by
  have hfin : volume (Icc (sInf I) (sInf I+δ)∪Icc (sSup I-δ) (sSup I))≠∞ := by
    exact (measure_union_lt_top (by rw [Real.volume_Icc];exact ENNReal.ofReal_lt_top)
      (by rw [Real.volume_Icc];exact ENNReal.ofReal_lt_top)).ne
  apply le_trans (measureReal_mono (μ:=volume) inter_subset_right hfin)
  have h:=measureReal_union_le (μ:=volume) (Icc (sInf I) (sInf I+δ)) (Icc (sSup I-δ) (sSup I))
  simpa only [Real.volume_real_Icc,add_sub_cancel_left,sub_sub_cancel,max_eq_left hδ,two_mul] using h

theorem mem_intervalBoundaryStrips_of_dist_to_endpoint (I : Set ℝ)
    (hb : BddBelow I) (ha : BddAbove I) {v δ : ℝ} (hv : v∈I)
    (h : v-sInf I≤δ ∨ sSup I-v≤δ) : v∈intervalBoundaryStrips I δ := by
  refine ⟨hv,?_⟩
  rcases h with hl|hr
  · exact Or.inl ⟨csInf_le hb hv,by linarith⟩
  · exact Or.inr ⟨by linarith,le_csSup ha hv⟩

theorem volume_set_le_boundary_strips (I E : Set ℝ) (hb : BddBelow I) (ha : BddAbove I)
    (δ : ℝ) (hδ : 0≤δ) (hE : ∀v∈E,v∈I ∧ (v-sInf I≤δ ∨ sSup I-v≤δ)) :
    volume.real E≤2*δ := by
  have hsub : E⊆intervalBoundaryStrips I δ:=fun v hv=>
    mem_intervalBoundaryStrips_of_dist_to_endpoint I hb ha (hE v hv).1 (hE v hv).2
  have hfin : volume (intervalBoundaryStrips I δ)≠∞ := by
    apply ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) ?_)
    exact measure_union_lt_top (by rw [Real.volume_Icc];exact ENNReal.ofReal_lt_top)
      (by rw [Real.volume_Icc];exact ENNReal.ofReal_lt_top)
  exact (measureReal_mono hsub hfin).trans (volume_intervalBoundaryStrips_le I δ hδ)

end FourPapersCommon
