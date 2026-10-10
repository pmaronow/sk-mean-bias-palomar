module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingActualSource
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentation

@[expose] public section

/-! The first source formula is applied to the actual terminal genealogies
representing fixed vertex patterns. These are the genuine integrand
derivatives needed when differentiating the six source terms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeStreamingPatternParameterMoment
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (P : NativeStreamingAttachmentPattern T) (u : ℝ) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ u hu)
      μ a q T F P else 0

theorem hasDerivWithinAt_nativeStreamingPattern_of_terminalRepresentation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T U : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (P : NativeStreamingAttachmentPattern T)
    (G : TerminalSpins (Configuration (n+1)) U → ℝ)
    (hrep : ∀D : AnisotropicSpinModel (n+1),
      nativeStreamingPatternMoment D μ a q T F P =
        nativeStreamingOldTerminalExpectation D μ a q U G)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q U G) (Icc (0:ℝ) 1) u := by
  apply (hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop U G u hu).congr_of_mem ?_ hu
  intro v hv
  simp only [nativeStreamingPatternParameterMoment,dif_pos hv]
  exact (hrep _).trans (followupCavityNativeTerminalExpectation_eq_old_terminal
    (n:=n) β ρ hβ hρ μ a q U G v hv).symm

theorem hasDerivWithinAt_nativeStreamingPattern_originalFresh_vertex_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (v : FiniteCascadeRecordVertex T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i (.vertex v)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q
        (finiteCascadeContinuationGraft observationLinearTree v)
        (nativeStreamingPatternVertexTerminalTest .single T v
          (nativeStreamingOriginalFreshSpinTest T F i
            (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v)))))
      (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_nativeStreamingPattern_of_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q hq hJ hzero htop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_originalFresh_terminalRepresentation D μ a q T F i v) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_current_vertex_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current (.vertex v)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q
        (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
        (nativeStreamingPatternVertexTerminalTest .current T v
          (nativeStreamingDefectSpinTest T F (q v.depth)))) (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_nativeStreamingPattern_of_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q hq hJ hzero htop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_current_terminalRepresentation D μ a q T F v) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_cross_vertices_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.vertex v) (.vertex w)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q
        (finiteCascadeCrossContinuationGraft observationLinearTree v w)
        (nativeStreamingPatternCrossTerminalTest T v w
          (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w)))))
      (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_nativeStreamingPattern_of_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q hq hJ hzero htop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_cross_vertices_terminalRepresentation D μ a q T F v w) u hu

end QuantitativeFollowup
