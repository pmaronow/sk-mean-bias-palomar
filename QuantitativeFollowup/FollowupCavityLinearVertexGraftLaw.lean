module
public import FourPapersCommon.FiniteCascadeGaussianContinuationGraft
public import FourPapersCommon.FiniteCascadeFuturePairSpins
public import QuantitativeFollowup.FollowupCavityVertexGraftLaw

@[expose] public section

/-! The linear continuation family realizes the actual one-fresh mark
while retaining the common generic leaf geometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem anisotropicSingleVertexMarkedLaw_eq_linear_graft (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v))).map
      (fun z=>((z.1,(finiteCascadeContinuationExtract observationLinearTree
        (fun d=>observationLinearSpin d) v z.2).1),
        (finiteCascadeContinuationExtract observationLinearTree (fun d=>observationLinearSpin d) v z.2).2))=
      anisotropicSingleVertexMarkedLaw D s a T v := by
  rw [show anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v))=
      finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (finiteCascadeContinuationGraft observationLinearTree v)
        (anisotropicRootEnergyMap D) 0 from rfl,
    finiteCascadeGaussianJointLaw_continuation_graft _ _ (anisotropicSchemeMass_nonneg s) _ a _ _
      (fun d=>measurable_observationLinearSpin d)]
  unfold finiteCascadeContinuationMarkedLaw anisotropicSingleVertexMarkedLaw finiteCascadeSingleVertexMarkedLaw
  congr 1
  unfold finiteCascadeContinuationVertexKernel finiteCascadeSingleVertexKernel finiteCascadeContinuationKernel
  rw [finiteCascadeObservationLinearKernel_spin _ _ (anisotropicSchemeMass_nonneg s)]

end QuantitativeFollowup
