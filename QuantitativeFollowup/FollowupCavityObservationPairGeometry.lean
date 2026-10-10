module
public import QuantitativeFollowup.FollowupCavityNativeTerminalApproximation
public import FourPapersCommon.FiniteObservationRefinementLeafGeometry
public import FourPapersCommon.FiniteObservationTrimLeafGeometry

@[expose] public section

/-! Exact old-leaf geometry and branch budgets for floor-preserving
observation refinements, including the zero root removal. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityObservationRefinedLeaf (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J)
    (h : observationRefinementDepth d J=k+2) (i : ObservationLeaf T) :
    ObservationLeaf (trimRoot (observationTreeDepthCast h (observationRefineTree d T))) :=
  observationTrimLeaf _ (observationRefinementDepthLeafEmbed d T h i)

private theorem terminalSpins_unitRecord {S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (σ : TerminalSpins S T) :
    finiteCascadeRecordTerminalSpins T (observationUnitRecord T σ)=σ := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih σ
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT σ.1) (ihU σ.2)

theorem cavityObservationRefinementTerminalProject_leafSpin {S : Type}
    (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J)
    (h : observationRefinementDepth d J=k+2) (i : ObservationLeaf T)
    (σ : TerminalSpins S (observationTreeDepthCast h (observationRefineTree d T))) :
    observationLeafTerminalSpin T i (observationRefinementTerminalProject d T h σ)=
      observationLeafTerminalSpin _ (observationRefinementDepthLeafEmbed d T h i) σ := by
  unfold observationRefinementTerminalProject
  rw [observationLeafTerminalSpin_record,←observationRefinementDepthLeafEmbed_spin,
    ←observationLeafTerminalSpin_record,terminalSpins_unitRecord]

theorem cavityObservationRefinedLeaf_terminalSpin {S : Type} [MeasurableSpace S]
    (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J)
    (h : observationRefinementDepth d J=k+2) (i : ObservationLeaf T)
    (σ : TerminalSpins S (trimRoot (observationTreeDepthCast h (observationRefineTree d T)))) :
    observationLeafTerminalSpin T i (observationRefinementTerminalProject d T h
      ((terminalSampleEquiv (S:=S) (observationTreeDepthCast h (observationRefineTree d T))).symm
        (trimmedSpinEquiv (S:=S) (observationTreeDepthCast h (observationRefineTree d T))
          (terminalSampleEquiv (S:=S) (trimRoot (observationTreeDepthCast h (observationRefineTree d T))) σ))))=
      observationLeafTerminalSpin _ (cavityObservationRefinedLeaf d T h i) σ := by
  rw [cavityObservationRefinementTerminalProject_leafSpin,observationTrimLeaf_terminalSpin]
  rfl

theorem cavityObservationRefinedLeaf_profileLevel (s : RSBScheme k) (hq : s.q 1=0)
    (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J)
    (h : observationRefinementDepth d J=k+2) (q : ℕ→Paper.Overlap)
    (hl : ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j)
    (i l : ObservationLeaf T) :
    cavityProfileLevel s (observationCommonLevel _ (cavityObservationRefinedLeaf d T h i)
      (cavityObservationRefinedLeaf d T h l))=q (observationCommonLevel T i l) := by
  have hroot : (cavityProfileLevel s (k+2):ℝ)=(cavityProfileLevel s ((k+2)-1):ℝ) := by
    have h1 : k+2-((k+2)-1)=1:=by omega
    simp only [cavityProfileLevel,scalarSchemeTransportNode,Nat.sub_self,h1,s.q_zero,hq]
  apply Subtype.ext
  rw [show (cavityProfileLevel s (observationCommonLevel _ (cavityObservationRefinedLeaf d T h i)
      (cavityObservationRefinedLeaf d T h l)):ℝ)=
    (cavityProfileLevel s (observationCommonLevel _ (observationRefinementDepthLeafEmbed d T h i)
      (observationRefinementDepthLeafEmbed d T h l)):ℝ) from
      observationTrimLeaf_commonLevel_clock (fun j=>(cavityProfileLevel s j:ℝ)) _ hroot _ _,
    observationRefinementDepthLeafEmbed_commonLevel,
    show cavityProfileLevel s (observationRefinementDepth d (observationCommonLevel T i l))=
      anisotropicRecordedSchemeSchedule s (observationRefinementDepth d (observationCommonLevel T i l)) from rfl,
    hl]

theorem cavityObservationRefined_branchSum (s : RSBScheme k) (hq : s.q 1=0)
    (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J)
    (h : observationRefinementDepth d J=k+2) (q : ℕ→Paper.Overlap)
    (hl : ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j)
    (χ : Paper.Overlap→ℝ) :
    finiteCascadeUnweightedBranchSum (fun j=>χ (cavityProfileLevel s j))
      (trimRoot (observationTreeDepthCast h (observationRefineTree d T)))=
      finiteCascadeUnweightedBranchSum (fun j=>χ (q j)) T := by
  have hroot : cavityProfileLevel s (k+2)=cavityProfileLevel s ((k+2)-1) := by
    apply Subtype.ext
    have h1 : k+2-((k+2)-1)=1:=by omega
    simp only [cavityProfileLevel,scalarSchemeTransportNode,Nat.sub_self,h1,s.q_zero,hq]
  rw [finiteCascadeUnweightedBranchSum_trimRoot _ _ (congrArg χ hroot),
    finiteCascadeUnweightedBranchSum_observationRefinementDepth]
  congr 1
  funext j
  exact congrArg χ (hl j)

end QuantitativeFollowup
