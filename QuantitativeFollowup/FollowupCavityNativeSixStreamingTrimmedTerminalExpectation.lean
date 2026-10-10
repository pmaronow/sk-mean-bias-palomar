module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedSixAgreement
public import QuantitativeFollowup.FollowupCavityNativeTerminalApproximation

@[expose] public section

/-! Actual terminal expectations and marked expressions on the genuine
zero-time initial advance. Energy projection and depth casts retain the
original finite terminal test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPhysicalRecordObservable_advance_terminal
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (z : CavityPathRecordSpace T (n+1)) :
    followupCavityPhysicalRecordObservable n T.advance
      (cavityTerminalSampleObservable T.advance F) z=
      F (finiteCascadeRecordTerminalSpins T z.2) := by
  dsimp only [followupCavityPhysicalRecordObservable,cavityTerminalSampleObservable,
    trimRoot,trimmedSpinEquiv,terminalSampleEquiv,MeasurableEquiv.refl_apply]
  rw [←terminalSampleEquiv_recordSpins]
  simp

theorem followupCavityPhysicalExpectation_advance_terminal
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hs : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T.advance
      (cavityTerminalSampleObservable T.advance F) u=
      nativeStreamingOldTerminalExpectation (followupCavitySpinModel n β ρ hβ hρ u hu)
        (Paper.parisiSchemeMeasure s) a (anisotropicRecordedSchemeSchedule s) T F := by
  rw [followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hs]
  simp_rw [nativeStreamingPhysicalRecordObservable_advance_terminal]
  exact (nativeStreamingOldTerminalMoment_scheme_trimmed _ s a hs T F).symm

theorem followupCavityNativeTerminalExpectation_eq_old_terminal
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u=
      nativeStreamingOldTerminalExpectation (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a q T F := by
  rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ μ a q T F u hu,
    anisotropicRecordedEnergyProbability_measure]
  have hm : Measurable (Prod.map (anisotropicObservationEnergy
      (followupCavitySpinModel n β ρ hβ hρ u hu))
      (observationTreeMap (anisotropicObservationEnergy
        (followupCavitySpinModel n β ρ hβ hρ u hu)) T)) :=
    (measurable_anisotropicObservationEnergy _).prodMap
      (measurable_observationTreeMap (S:=Configuration (n+1)) _
        (measurable_anisotropicObservationEnergy _) T)
  have hF : Measurable (fun z : CavityPathRecordSpace T (n+1)=>
      F (finiteCascadeRecordTerminalSpins T z.2)) :=
    (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  simp only [Prod.map_snd,finiteCascadeRecordTerminalSpins_treeMap]
  rfl

theorem nativeStreamingOldTerminalExpectation_depthCast
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j l : ℕ} (h : j=l)
    (T : FiniteTerminalGenealogy j) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingOldTerminalExpectation D μ a q (observationTreeDepthCast h T)
      (fun σ=>F (finiteCascadeRecordTerminalSpins T
        (observationRecordDepthCast h T (observationUnitRecord _ σ))))=
      nativeStreamingOldTerminalExpectation D μ a q T F := by
  subst l
  simp only [observationTreeDepthCast,observationRecordDepthCast,id_eq,
    finiteCascadeRecordTerminalSpins_unit]

theorem nativeStreamingVertexSixBracket_depthCast
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (b : ℕ → ℝ) {j l : ℕ} (h : j=l)
    (T : FiniteTerminalGenealogy j) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingVertexSixBracket D μ a q b (observationTreeDepthCast h T)
      (fun σ=>F (finiteCascadeRecordTerminalSpins T
        (observationRecordDepthCast h T (observationUnitRecord _ σ))))=
      nativeStreamingVertexSixBracket D μ a q b T F := by
  subst l
  simp only [observationTreeDepthCast,observationRecordDepthCast,id_eq,
    finiteCascadeRecordTerminalSpins_unit]

end QuantitativeFollowup
