module
public import QuantitativePaper.VectorControlledState

@[expose] public section

/-! The actual general-profile gradient feedback is a genuine admissible
vector control, and its literal integrated-control state equals the
independently constructed Picard diffusion on the physical interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorMeasureFeedbackControl (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) sample.1
    (vectorMeasureState μ β t ht r sample)

theorem isVectorParisiControl_vectorMeasureFeedbackControl (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    IsVectorParisiControl (vectorMeasureFeedbackControl (n := n) μ β t ht) where
  continuous := by
    intro sample
    simpa only [Function.comp_def,vectorMeasureFeedbackControl] using
      (continuous_vectorMeasureGradient μ β t ht).comp
        (show Continuous (fun r : ℝ≥0 =>
          (projIcc (0 : ℝ) 1 zero_le_one r,(sample.1,vectorMeasureState μ β t ht r sample))) from
          (continuous_projIcc.comp NNReal.continuous_coe).prodMk
            (continuous_const.prodMk (continuous_vectorMeasureState μ β t ht sample)))
  adapted := by
    intro r
    have hg : Continuous (fun z : VectorParameter n =>
        vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) z.1 z.2) := by
      simpa only [Function.comp_def,id_eq] using (continuous_vectorMeasureGradient μ β t ht).comp
        (continuous_const.prodMk (continuous_id : Continuous (id : VectorParameter n→VectorParameter n)))
    exact (hg.measurable.comp ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk
      (stronglyAdapted_vectorMeasureState μ β t ht r).measurable)).stronglyMeasurable
  norm_le := fun r sample => norm_vectorMeasureGradient_le μ β t ht _ _ _

theorem vectorMeasureState_eq_controlled (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureState μ β t ht r sample=
      vectorControlledState ((1-t)*β^2) μ (vectorMeasureFeedbackControl μ β t ht) r sample := by
  let d := vectorMeasureDriftData (n := n) μ β t ht
  let σ := Real.sqrt ((1-t)*β^2)
  have hInt : vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ 0 1 s sample) r=
      vectorIntegratedDrift (fun s => vectorControlDrift ((1-t)*β^2) μ
        (vectorMeasureFeedbackControl μ β t ht) s sample) r := by
    unfold vectorIntegratedDrift
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hs1 : s≤(1 : ℝ≥0) := hs.2.trans hr
    simp only [vectorAdditiveDrift,ite_eq_left hs1,d,σ,vectorMeasureDriftData,
      vectorMeasureDrift,vectorControlDrift,vectorMeasureFeedbackControl,vectorMeasureState]
  have hh := vectorAdditiveState_decomposition d σ 0 1 r sample
  change vectorMeasureState μ β t ht r sample=0+
    vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ 0 1 s sample) r+
      σ • disorderVectorBrownian r sample at hh
  rw [zero_add,hInt] at hh
  simpa only [vectorControlledState,σ,add_comm] using hh

end QuantitativePaper
