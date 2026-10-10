module
public import FourPapersCommon.FiniteCascadeCrossContinuationGraft
public import FourPapersCommon.FiniteCascadeFuturePairSpins

@[expose] public section

/-! Literal old and two fresh terminal leaves of the double linear
continuation tree, with their actual retained spins and split levels. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy MeasureTheory ProbabilityTheory SpinGlass.AT
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

private theorem linearLeaf_spin {E S : Type} (d : ℕ) (z : Records E S (observationLinearTree d)) :
    observationLeafSpin (observationLinearTree d) (observationLinearLeaf d) z=observationLinearSpin d z := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

@[reducible] def finiteCascadeLinearCrossOldLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (i : ObservationLeaf T) :=
  finiteCascadeContinuationOldLeaf observationLinearTree
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
      (finiteCascadeContinuationOldLeaf observationLinearTree v i)

@[reducible] def finiteCascadeLinearCrossFirstLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :=
  finiteCascadeContinuationOldLeaf observationLinearTree
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
      (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth))

@[reducible] def finiteCascadeLinearCrossSecondLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :=
  finiteCascadeContinuationNewLeaf observationLinearTree
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
      (observationLinearLeaf (finiteCascadeContinuationVertexEmbed observationLinearTree v w).depth)

theorem finiteCascadeLinearCrossOldLeaf_spin {E S : Type} {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (i : ObservationLeaf T) (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    observationLeafSpin _ (finiteCascadeLinearCrossOldLeaf v w i) z =
      observationLeafSpin T i (finiteCascadeCrossContinuationExtract observationLinearTree
        (fun d => observationLinearSpin d) v w z).1 := by
  simp only [finiteCascadeLinearCrossOldLeaf,finiteCascadeContinuationOldLeaf_spin,
    finiteCascadeCrossContinuationExtract,finiteCascadeContinuationExtract_eq_records]

theorem finiteCascadeLinearCrossFirstLeaf_spin {E S : Type} {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    observationLeafSpin _ (finiteCascadeLinearCrossFirstLeaf v w) z =
      (finiteCascadeCrossContinuationExtract observationLinearTree
        (fun d => observationLinearSpin d) v w z).2.1 := by
  simp only [finiteCascadeLinearCrossFirstLeaf,finiteCascadeContinuationOldLeaf_spin,
    finiteCascadeContinuationNewLeaf_spin,linearLeaf_spin,
    finiteCascadeCrossContinuationExtract,finiteCascadeContinuationExtract_eq_records]

theorem finiteCascadeLinearCrossSecondLeaf_spin {E S : Type} {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    observationLeafSpin _ (finiteCascadeLinearCrossSecondLeaf v w) z =
      (finiteCascadeCrossContinuationExtract observationLinearTree
        (fun d => observationLinearSpin d) v w z).2.2 := by
  simp only [finiteCascadeLinearCrossSecondLeaf,finiteCascadeContinuationNewLeaf_spin,
    linearLeaf_spin,finiteCascadeCrossContinuationExtract,
    finiteCascadeContinuationExtract_eq_records]

theorem finiteCascadeLinearCrossOldLeaf_commonLevel {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (i l : ObservationLeaf T) :
    observationCommonLevel _ (finiteCascadeLinearCrossOldLeaf v w i)
      (finiteCascadeLinearCrossOldLeaf v w l)=observationCommonLevel T i l := by
  simp only [finiteCascadeLinearCrossOldLeaf,finiteCascadeContinuationOldLeaf_commonLevel]

theorem finiteCascadeLinearCrossFresh_commonLevel {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    observationCommonLevel _ (finiteCascadeLinearCrossFirstLeaf v w)
      (finiteCascadeLinearCrossSecondLeaf v w)=finiteCascadeCommonPathDepth T v w := by
  rw [finiteCascadeLinearCrossFirstLeaf,finiteCascadeLinearCrossSecondLeaf,
    finiteCascadeContinuationOldNewLeaf_commonLevel]
  exact finiteCascadeContinuationNewLeaf_vertex_commonPathDepth observationLinearTree v _ w

theorem finiteCascadeLinearCross_branchSum (χ : ℕ → ℝ) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeCrossContinuationGraft observationLinearTree v w)=
      finiteCascadeUnweightedBranchSum χ T + χ v.depth + χ w.depth := by
  rw [finiteCascadeCrossContinuationGraft,finiteCascadeContinuationGraft_branchSum,
    finiteCascadeContinuationGraft_branchSum,finiteCascadeContinuationVertexEmbed_depth]
  simp only [observationLinearTree_branchSum,add_zero]

variable {S I J A : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S] [MeasurableSpace A]

theorem finiteCascadeGaussianJointLaw_cross_continuation_graft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0≤a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (finiteCascadeCrossContinuationGraft U v w) R H).map
      (fun z => ((z.1,(finiteCascadeCrossContinuationExtract U extract v w z.2).1),
        (finiteCascadeCrossContinuationExtract U extract v w z.2).2)) =
      finiteCascadeCrossContinuationMarkedLaw V a L U extract v w
        (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  exact finiteCascadeCrossContinuationGraft_joint_law V a ha L U extract he v w _

end FourPapersCommon
