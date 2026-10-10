module
public import FourPapersCommon.CouplingCDFL1
public import FourPapersCommon.CDFDistanceTriangle
public import Paper.ParisiRestartState
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Moving the actual restart level is controlled in time-L¹ even when
mass crosses zero.  This is the pushforward max(q-a,0), including atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem parisiRestartOverlap_level_dist_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (q : Paper.Overlap) :
    |(parisiRestartOverlap a ha q : ℝ)-(parisiRestartOverlap b hb q : ℝ)| ≤ |a-b| := by
  have hl : LipschitzWith 1 (fun x : ℝ => max x 0) :=
    by simpa using LipschitzWith.id.max (LipschitzWith.const 0)
  have hh := hl.norm_sub_le ((q : ℝ)-a) ((q : ℝ)-b)
  simpa only [parisiRestartOverlap,NNReal.coe_one,one_mul,Real.norm_eq_abs,
    show ((q : ℝ)-a)-((q : ℝ)-b)=b-a by ring,abs_sub_comm b a] using hh

theorem parisiCDFDistance_restart_levels_le (μ : Paper.ParisiMeasure)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Paper.parisiCDFDistance (parisiRestartMeasure μ a ha) (parisiRestartMeasure μ b hb) ≤ |a-b| := by
  let f : Paper.Overlap → Paper.Overlap×Paper.Overlap :=
    fun q => (parisiRestartOverlap a ha q,parisiRestartOverlap b hb q)
  have hf : Measurable f := (continuous_parisiRestartOverlap a ha).measurable.prodMk
    (continuous_parisiRestartOverlap b hb).measurable
  let P : Measure (Paper.Overlap×Paper.Overlap) := (μ : Measure Paper.Overlap).map f
  have : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hp1 : P.map Prod.fst=(parisiRestartMeasure μ a ha : Measure Paper.Overlap) := by
    dsimp only [P]
    rw [Measure.map_map measurable_fst hf]
    rfl
  have hp2 : P.map Prod.snd=(parisiRestartMeasure μ b hb : Measure Paper.Overlap) := by
    dsimp only [P]
    rw [Measure.map_map measurable_snd hf]
    rfl
  have hc := parisiCDFDistance_le_coupling (parisiRestartMeasure μ a ha)
    (parisiRestartMeasure μ b hb) P hp1 hp2
  have hi : Integrable (fun p : Paper.Overlap×Paper.Overlap => |(p.1 : ℝ)-(p.2 : ℝ)|) P :=
    (integrable_const (1 : ℝ)).mono'
      (((measurable_subtype_coe.comp measurable_fst).sub
        (measurable_subtype_coe.comp measurable_snd)).abs).aestronglyMeasurable
      (.of_forall fun p => by
        rw [Real.norm_eq_abs,abs_abs,abs_le]
        constructor <;> linarith [p.1.property.1,p.1.property.2,p.2.property.1,p.2.property.2])
  have hm : AEStronglyMeasurable (fun p : Paper.Overlap×Paper.Overlap =>
      |(p.1 : ℝ)-(p.2 : ℝ)|) P := hi.aestronglyMeasurable
  change _ ≤ ∫ p,|(p.1 : ℝ)-(p.2 : ℝ)| ∂((μ : Measure Paper.Overlap).map f) at hc
  rw [integral_map hf.aemeasurable hm] at hc
  have hbound := integral_mono ((integrable_map_measure hm hf.aemeasurable).mp hi)
    (integrable_const |a-b|) (fun q => parisiRestartOverlap_level_dist_le a b ha hb q)
  simpa only [integral_const,probReal_univ,one_smul] using hc.trans hbound

theorem tendsto_parisiRestartMeasure_CDFDistance {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μn L (𝓝 μ)) (an : ι → ℝ) (a : ℝ)
    (han : ∀ i,0 ≤ an i) (ha : 0 ≤ a) (hA : Tendsto an L (𝓝 a)) :
    Tendsto (fun i => Paper.parisiCDFDistance (parisiRestartMeasure (μn i) (an i) (han i))
      (parisiRestartMeasure μ a ha)) L (𝓝 0) := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μn μ hμ
    (continuous_parisiRestartOverlap a ha)
  have hCDF := FRSB.tendsto_parisiCDFDistance_of_tendsto hm
  apply squeeze_zero (fun _ => Paper.parisiCDFDistance_nonneg _ _) (fun i =>
    (parisiCDFDistance_triangle (parisiRestartMeasure (μn i) (an i) (han i))
      (parisiRestartMeasure (μn i) a ha) (parisiRestartMeasure μ a ha)).trans
      (add_le_add (parisiCDFDistance_restart_levels_le (μn i) (an i) a (han i) ha) le_rfl))
  simpa only [sub_self,abs_zero,zero_add,parisiRestartMeasure] using (hA.sub_const a).abs.add hCDF

end QuantitativeFollowup
