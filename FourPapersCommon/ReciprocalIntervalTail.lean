module
public import FourPapersCommon.ReciprocalStripIntegration

@[expose] public section

/-! Integrating genuine bounded endpoint reciprocal tails. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem integral_right_reciprocal_tail_bound (g : ℝ→ℝ) (hg : Measurable g)
    (l r b M : ℝ) (hlr : l≤r) (hlen : r-l≤1) (hb : 0≤b) (hM : 1≤M)
    (hgBound : ∀v,0≤g v ∧ g v≤1)
    (hTail : ∀v∈Ioo l r,g v≤b/(r-v)) :
    (∫v in Ioo l r,g v)≤1/M+b*Real.log M := by
  have hiG : IntegrableOn g (Ioo l r):=Integrable.of_bound hg.aestronglyMeasurable 1
    (.of_forall fun v=>by rw [Real.norm_of_nonneg (hgBound v).1];exact (hgBound v).2)
  have hiR : IntegrableOn (fun v : ℝ=>min 1 (b/(r-v))) (Ioo l r):=by
    apply Integrable.of_bound ((measurable_const.min (measurable_const.div (measurable_const.sub measurable_id))).aestronglyMeasurable) 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    change ‖min 1 (b/(r-v))‖≤1
    rw [Real.norm_of_nonneg (le_min zero_le_one (div_nonneg hb (sub_pos.mpr hv.2).le))]
    exact min_le_left _ _
  have he:=integral_mono_ae hiG hiR (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact le_min (hgBound v).2 (hTail v hv))
  rw [integral_reflected_truncated_reciprocal l r b hlr] at he
  exact he.trans (truncated_reciprocal_cutoff_bound (r-l) b M (sub_nonneg.mpr hlr) hlen hb hM)

theorem integral_left_reciprocal_tail_bound (g : ℝ→ℝ) (hg : Measurable g)
    (l r b M : ℝ) (hlr : l≤r) (hlen : r-l≤1) (hb : 0≤b) (hM : 1≤M)
    (hgBound : ∀v,0≤g v ∧ g v≤1)
    (hTail : ∀v∈Ioo l r,g v≤b/(v-l)) :
    (∫v in Ioo l r,g v)≤1/M+b*Real.log M := by
  have hiG : IntegrableOn g (Ioo l r):=Integrable.of_bound hg.aestronglyMeasurable 1
    (.of_forall fun v=>by rw [Real.norm_of_nonneg (hgBound v).1];exact (hgBound v).2)
  have hiR : IntegrableOn (fun v : ℝ=>min 1 (b/(v-l))) (Ioo l r):=by
    apply Integrable.of_bound ((measurable_const.min (measurable_const.div (measurable_id.sub measurable_const))).aestronglyMeasurable) 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    change ‖min 1 (b/(v-l))‖≤1
    rw [Real.norm_of_nonneg (le_min zero_le_one (div_nonneg hb (sub_pos.mpr hv.1).le))]
    exact min_le_left _ _
  have he:=integral_mono_ae hiG hiR (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact le_min (hgBound v).2 (hTail v hv))
  rw [integral_translated_truncated_reciprocal l r b hlr] at he
  exact he.trans (truncated_reciprocal_cutoff_bound (r-l) b M (sub_nonneg.mpr hlr) hlen hb hM)

end FourPapersCommon
