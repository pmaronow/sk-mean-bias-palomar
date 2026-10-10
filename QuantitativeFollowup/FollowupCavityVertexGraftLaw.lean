module
public import FourPapersCommon.FiniteCascadeGaussianGraft
public import FourPapersCommon.FiniteCascadeGraftSpins
public import QuantitativeFollowup.FollowupCavityOriginalVertexMarks
public import QuantitativeFollowup.FollowupCavityVertexMarks

@[expose] public section

/-! Physical anisotropic single and cross-vertex mark laws are the exact
pushforwards of genuine enlarged cavity genealogies. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem anisotropicSingleVertexMarkedLaw_eq_graft (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeVertexGraft v))).map
      (fun z => ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
        (finiteCascadeGraftRecordExtract v z.2).2)) =
      anisotropicSingleVertexMarkedLaw D s a T v := by
  exact finiteCascadeGaussianJointLaw_single_graft _ _ (anisotropicSchemeMass_nonneg s) _ a v _ _

theorem anisotropicCrossVertexMarkedLaw_eq_graft (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossVertexGraft v w))).map
      (fun z => ((z.1,(finiteCascadeCrossGraftExtract v w z.2).1),
        (finiteCascadeCrossGraftExtract v w z.2).2)) =
      anisotropicCrossVertexMarkedLaw D s a T v w := by
  exact finiteCascadeGaussianJointLaw_cross_graft _ _ (anisotropicSchemeMass_nonneg s) _ a v w _ _

end QuantitativeFollowup
