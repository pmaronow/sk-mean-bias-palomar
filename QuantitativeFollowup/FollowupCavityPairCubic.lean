module
public import QuantitativeFollowup.AnisotropicRecordedPairCollapse
public import QuantitativeFollowup.FollowupCavityThirdMoment

@[expose] public section

/-! Cubic moments of genuine selected descendants are exactly the actual
fresh-pair moments at the pair's common ancestral level. Products of three
physical defects use those actual marginals on the same recorded law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityRecorded_leafPair_cubic_eq (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hzero : q 0=1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0)
    (hq : ∀l,l<j→q (l+1)≤q l) (i k : ObservationLeaf T) (hik : i≠k) :
    (∫z,|cavityRestOverlap n (observationLeafSpin T i z.2)
      (observationLeafSpin T k z.2)-(q (observationCommonLevel T i k):ℝ)|^3
        ∂anisotropicRecordedProfileTreeLaw D μ a q T)=
      cavityCubicPairMoment D μ a (q (observationCommonLevel T i k)) := by
  let f : Configuration (n+1)×Configuration (n+1)→ℝ:=
    fun z=>|cavityRestOverlap n z.1 z.2-(q (observationCommonLevel T i k):ℝ)|^3
  have hm : Measurable (fun z : AnisotropicObservationState (n+1)×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T=>
      (observationLeafSpin T i z.2,observationLeafSpin T k z.2)):=
    ((measurable_observationLeafSpin T i).comp measurable_snd).prodMk
      ((measurable_observationLeafSpin T k).comp measurable_snd)
  have he:=integral_map (μ:=anisotropicRecordedProfileTreeLaw D μ a q T)
    hm.aemeasurable (measurable_of_finite f).aestronglyMeasurable
  rw [anisotropicRecordedProfile_leafPair_law D μ a q hzero T hroot hq i k hik] at he
  exact he.symm

theorem cavityRecorded_threeDefects_le_cubic_pair_moments
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hzero : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=0) (hq : ∀l,l<j→q (l+1)≤q l)
    (i k : Fin 3→ObservationLeaf T) (hik : ∀r,i r≠k r) :
    (∫z,|cavitySpinOverlapDefect n (q (observationCommonLevel T (i 0) (k 0)))
      (observationLeafSpin T (i 0) z.2) (observationLeafSpin T (k 0) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 1) (k 1)))
      (observationLeafSpin T (i 1) z.2) (observationLeafSpin T (k 1) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 2) (k 2)))
      (observationLeafSpin T (i 2) z.2) (observationLeafSpin T (k 2) z.2)|
      ∂anisotropicRecordedProfileTreeLaw D μ a q T)≤
      (cavityCubicPairMoment D μ a (q (observationCommonLevel T (i 0) (k 0)))+
        cavityCubicPairMoment D μ a (q (observationCommonLevel T (i 1) (k 1)))+
        cavityCubicPairMoment D μ a (q (observationCommonLevel T (i 2) (k 2))))/3 := by
  have hh:=integral_cavityThreeDefectProduct_le_cubic_moments
    (anisotropicRecordedProfileTreeLaw D μ a q T) n
    (fun r _=>q (observationCommonLevel T (i r) (k r))) (fun _=>measurable_const)
    (fun r z=>observationLeafSpin T (i r) z.2)
    (fun r z=>observationLeafSpin T (k r) z.2)
    (fun r=>(measurable_observationLeafSpin T (i r)).comp measurable_snd)
    (fun r=>(measurable_observationLeafSpin T (k r)).comp measurable_snd)
  rw [cavityRecorded_leafPair_cubic_eq D μ a q hzero T hroot hq (i 0) (k 0) (hik 0),
    cavityRecorded_leafPair_cubic_eq D μ a q hzero T hroot hq (i 1) (k 1) (hik 1),
    cavityRecorded_leafPair_cubic_eq D μ a q hzero T hroot hq (i 2) (k 2) (hik 2)] at hh
  exact hh

end QuantitativeFollowup
