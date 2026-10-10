module
public import QuantitativeFollowup.AnisotropicRecordedConditionalMean

@[expose] public section

/-! Actual one-point distributions of the native process under its genuine
initial Gaussian tilt. These are measure identities, not moment hypotheses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicNativeObservation_initial_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    (anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ 0)=
      anisotropicObservationInitialLaw D μ a := by
  have he : anisotropicNativeObservation D μ 0=
      (fun g : AnisotropicDisorder n=>(g,(0:Field n))) ∘ Prod.fst := by
    funext p
    simp only [anisotropicNativeObservation,Set.Icc.coe_zero,anisotropicMeasureState_zero,
      map_zero,Function.comp_apply]
  have hm : Measurable (fun g : AnisotropicDisorder n=>(g,(0:Field n))) := by fun_prop
  rw [he,←Measure.map_map hm measurable_fst,
    (hasLaw_anisotropicMeasureInitialDisorder D μ a).map_eq]
  rfl

theorem anisotropicNativeObservation_transition_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r) :
    (anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ r)=
      (anisotropicObservationTransition D μ q r) ∘ₘ
        ((anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ q)) := by
  have hh:=congrArg (fun P : Measure ((Unit×AnisotropicObservationState n)×AnisotropicObservationState n)=>P.snd)
    (anisotropic_native_full_past_transition_law D μ a q r hqr (fun _=>()) measurable_const)
  rw [Measure.snd_map_prodMk (measurable_const.prodMk (measurable_anisotropicNativeObservation D μ q))
    (measurable_anisotropicNativeObservation D μ r),Measure.snd_compProd] at hh
  refine hh.trans ?_
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.bind_apply hA (Kernel.aemeasurable _)]
  have hm : Measurable (fun z : Unit×AnisotropicObservationState n=>
      ((anisotropicObservationTransition D μ q r).comap Prod.snd measurable_snd) z A) :=
    ((anisotropicObservationTransition D μ q r).comap Prod.snd measurable_snd).measurable_coe hA
  rw [lintegral_map hm (measurable_const.prodMk (measurable_anisotropicNativeObservation D μ q)),
    lintegral_map ((anisotropicObservationTransition D μ q r).measurable_coe hA)
      (measurable_anisotropicNativeObservation D μ q)]
  rfl

theorem anisotropicNativeObservation_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ q)=
      (anisotropicObservationTransition D μ 0 q) ∘ₘ anisotropicObservationInitialLaw D μ a := by
  rw [anisotropicNativeObservation_transition_law D μ a 0 q q.property.1,
    anisotropicNativeObservation_initial_law]

end QuantitativeFollowup
