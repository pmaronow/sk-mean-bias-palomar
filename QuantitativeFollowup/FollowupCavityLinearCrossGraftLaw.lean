module
public import FourPapersCommon.FiniteCascadeLinearCrossGeometry
public import QuantitativeFollowup.FollowupCavityLinearVertexGraftLaw

@[expose] public section

/-! The genuine two independent cavity continuation marks, at arbitrary
and possibly coincident retained vertices, are an actual enlarged tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicCrossVertexMarkedLaw_eq_linear_graft (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicTrimmedRecordedTreeLaw D s a
      (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w))).map
      (fun z => ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree
        (fun d => observationLinearSpin d) v w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree
          (fun d => observationLinearSpin d) v w z.2).2)) =
      anisotropicCrossVertexMarkedLaw D s a T v w := by
  rw [show anisotropicTrimmedRecordedTreeLaw D s a
      (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w)) =
      finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (finiteCascadeCrossContinuationGraft observationLinearTree v w)
        (anisotropicRootEnergyMap D) 0 from rfl,
    finiteCascadeGaussianJointLaw_cross_continuation_graft _ _ (anisotropicSchemeMass_nonneg s) _ a _ _
      (fun d => measurable_observationLinearSpin d)]
  unfold finiteCascadeCrossContinuationMarkedLaw anisotropicCrossVertexMarkedLaw
    finiteCascadeCrossVertexMarkedLaw
  congr 1
  unfold finiteCascadeCrossContinuationKernel finiteCascadeCrossVertexPairKernel
    finiteCascadeContinuationVertexKernel
    finiteCascadeContinuationKernel
  rw [finiteCascadeObservationLinearKernel_spin _ _ (anisotropicSchemeMass_nonneg s),
    finiteCascadeObservationLinearKernel_spin _ _ (anisotropicSchemeMass_nonneg s)]
  rfl

end QuantitativeFollowup
