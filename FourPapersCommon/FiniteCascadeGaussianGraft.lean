module
public import FourPapersCommon.FiniteCascadeCrossVertexGraft

@[expose] public section

/-! Conditional-mark grafts preserve the actual tilted initial Gaussian
law and its normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem finiteCascadeGaussianJointLaw_single_graft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (finiteCascadeVertexGraft v) R H).map
      (fun z => ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
        (finiteCascadeGraftRecordExtract v z.2).2)) =
      finiteCascadeSingleVertexMarkedLaw V a L v (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  exact finiteCascadeVertexGraft_joint_law V a ha L v _

theorem finiteCascadeGaussianJointLaw_cross_graft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (finiteCascadeCrossVertexGraft v w) R H).map
      (fun z => ((z.1,(finiteCascadeCrossGraftExtract v w z.2).1),
        (finiteCascadeCrossGraftExtract v w z.2).2)) =
      finiteCascadeCrossVertexMarkedLaw V a L v w (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  exact finiteCascadeCrossVertexGraft_joint_law V a ha L v w _

end FourPapersCommon
