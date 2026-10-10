module
public import FourPapersCommon.FiniteCascadeFutureVertexGraft
public import QuantitativeFollowup.FollowupCavityFutureMarks

@[expose] public section

/-! The physical future pair is the pushforward of an actual enlarged
recorded cavity tree, at every prescribed overlap. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem anisotropicFutureVertexMarkedLaw_eq_graft (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap) :
    (anisotropicTrimmedRecordedTreeLaw D s a
      (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)))).map
      (fun z=>((z.1,(finiteCascadeFutureGraftExtract v (cavityFiniteFutureDepth s v.depth q) z.2).1),
        (finiteCascadeFutureGraftExtract v (cavityFiniteFutureDepth s v.depth q) z.2).2))=
      anisotropicFutureVertexMarkedLaw D s a T v q := by
  exact finiteCascadeGaussianJointLaw_future_graft _ _ (anisotropicSchemeMass_nonneg s) _ a v
    (cavityFiniteFutureDepth s v.depth q) (cavityFiniteFutureDepth_le s v.depth q) _ _

end QuantitativeFollowup
