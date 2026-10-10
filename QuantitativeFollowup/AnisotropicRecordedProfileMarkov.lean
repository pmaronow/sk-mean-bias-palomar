module
public import QuantitativeFollowup.AnisotropicRecordedProfileFuture

@[expose] public section

/-! Genuine full-past Markov law of the actual arbitrary-profile anisotropic
state. The identity retains an arbitrary measurable past observation along
with both endpoint fields, so it supplies chronological histories without
losing conditioning information. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def anisotropicNativeObservation (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) : AnisotropicObservationState n :=
  (p.1,anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q p))

theorem adapted_anisotropicNativeObservation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (anisotropicNativeObservation D μ q) := by
  have hq1 : (q:ℝ).toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hs := adapted_anisotropicMeasureState D μ (q:ℝ).toNNReal hq1
  rw [Real.coe_toNNReal _ q.property.1] at hs
  exact (measurable_anisotropicInitialDisorder _).prodMk
    ((anisotropicInverseNoiseMap D).measurable.comp hs)

theorem measurable_anisotropicNativeObservation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (anisotropicNativeObservation D μ q) :=
  (adapted_anisotropicNativeObservation D μ q).mono ((anisotropicBrownianFiltration n).le _) le_rfl

theorem anisotropicNativeObservation_advance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (p : AnisotropicDisorderBrownianSample n) :
    anisotropicObservationNoiseAdvance D μ q r
      (anisotropicNativeObservation D μ q p,anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal p)=
      anisotropicNativeObservation D μ r p := by
  have hs : anisotropicRestartNoiseStatePath D μ q
    ((p.1,anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q p)),
      fun i=>canonicalFutureBrownianPath (q:ℝ).toNNReal (p.2 i)) ((r:ℝ)-(q:ℝ))=
      anisotropicInverseNoiseMap D (anisotropicMeasureState D μ r p) := by
    rw [anisotropicMeasureState_restart D μ q r hqr p,anisotropicInverseNoiseMap_noise]
  exact congrArg (Prod.mk p.1) hs

theorem anisotropic_native_full_past_transition_law {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q r : Paper.Overlap) (hqr : q≤r)
    (Z : AnisotropicDisorderBrownianSample n→X)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z) :
    (anisotropicMeasureSampleLaw D μ a).map
      (fun p=>((Z p,anisotropicNativeObservation D μ q p),anisotropicNativeObservation D μ r p))=
      ((anisotropicMeasureSampleLaw D μ a).map (fun p=>(Z p,anisotropicNativeObservation D μ q p))) ⊗ₘ
        (anisotropicObservationTransition D μ q r).comap Prod.snd measurable_snd := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let Y:=fun p=>(Z p,anisotropicNativeObservation D μ q p)
  have hY : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Y :=
    hZ.prodMk (adapted_anisotropicNativeObservation D μ q)
  have hYm : Measurable Y:=hY.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hI:=(indep_anisotropicRecordedFutureBrownianPath_known D μ a (q:ℝ).toNNReal Y hY).symm
  have hprod:=hI.hasLaw_prod (hasLaw_map hYm.aemeasurable)
    (hasLaw_anisotropicRecordedFutureBrownianPath D μ a (q:ℝ).toNNReal)
  let f : (X×AnisotropicObservationState n)×VectorWienerPath n→AnisotropicObservationState n:=
    fun z=>anisotropicObservationNoiseAdvance D μ q r (z.1.2,z.2)
  have hf : Measurable f:=(measurable_anisotropicObservationNoiseAdvance D μ q r).comp
    (measurable_fst.snd.prodMk measurable_snd)
  let fpair : (X×AnisotropicObservationState n)×VectorWienerPath n→
      (X×AnisotropicObservationState n)×AnisotropicObservationState n:=fun z=>(z.1,f z)
  have hfpair : Measurable fpair:=measurable_fst.prodMk hf
  have he := independentNoiseKernel_joint_law (P.map Y) (vectorWienerMeasure n) f hf
  have hk : independentNoiseKernel (vectorWienerMeasure n) f=
      (anisotropicObservationTransition D μ q r).comap Prod.snd measurable_snd := by
    ext z A hA
    rw [Kernel.comap_apply,independentNoiseKernel_apply _ _ hf,
      anisotropicObservationTransition_apply]
    rfl
  rw [hk] at he
  have hh:=congrArg (fun Q : Measure ((X×AnisotropicObservationState n)×VectorWienerPath n)=>Q.map fpair)
    hprod.map_eq
  rw [Measure.map_map hfpair (hYm.prodMk (measurable_anisotropicRecordedFutureBrownianPath _))] at hh
  have hmap : (fun p=>fpair (Y p,anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal p))=
      fun p=>((Z p,anisotropicNativeObservation D μ q p),anisotropicNativeObservation D μ r p) := by
    funext p
    exact congrArg (Prod.mk (Y p)) (anisotropicNativeObservation_advance D μ q r hqr p)
  change (P.map (fun p=>fpair (Y p,anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal p)))=_ at hh
  rw [hmap] at hh
  exact hh.trans he

end QuantitativeFollowup
