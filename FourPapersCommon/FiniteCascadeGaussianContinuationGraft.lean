module
public import FourPapersCommon.FiniteCascadeContinuationGraftLaw
public import FourPapersCommon.FiniteCascadeGaussianGraft

@[expose] public section

/-! Grafting actual continuations also preserves the genuine tilted
Gaussian root law and its normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I J A : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S] [MeasurableSpace A]
set_option maxHeartbeats 600000

theorem finiteCascadeGaussianJointLaw_continuation_graft (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (finiteCascadeContinuationGraft U v) R H).map
      (fun z=>((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2))=
      finiteCascadeContinuationMarkedLaw V a L U extract v (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  exact finiteCascadeContinuationGraft_joint_law V a ha L U extract he v _

end FourPapersCommon
