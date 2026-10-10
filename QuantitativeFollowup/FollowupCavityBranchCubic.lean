module
public import QuantitativeFollowup.FollowupCavityPairCubic
public import FourPapersCommon.FiniteObservationPairLevels

@[expose] public section

/-! Actual three-defect recorded moments are controlled by cubic moments
at the literal branch levels of that genealogy. This applies directly
to enlarged graft trees and retains their inherited branch marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 700000

theorem cavityRecorded_threeDefects_le_branch_cubic
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hzero : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=0) (hq : ∀l,l<j→q (l+1)≤q l)
    (i k : Fin 3→ObservationLeaf T) (hik : ∀r,i r≠k r) :
    (∫z,|cavitySpinOverlapDefect n (q (observationCommonLevel T (i 0) (k 0)))
      (observationLeafSpin T (i 0) z.2) (observationLeafSpin T (k 0) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 1) (k 1)))
      (observationLeafSpin T (i 1) z.2) (observationLeafSpin T (k 1) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 2) (k 2)))
      (observationLeafSpin T (i 2) z.2) (observationLeafSpin T (k 2) z.2)|
      ∂anisotropicRecordedProfileTreeLaw D μ a q T)≤
      finiteCascadeUnweightedBranchSum (fun l=>cavityCubicPairMoment D μ a (q l)) T := by
  have hh:=cavityRecorded_threeDefects_le_cubic_pair_moments D μ a q hzero T hroot hq i k hik
  have hb (r : Fin 3) := observationPair_level_le_branchSum
    (fun l=>cavityCubicPairMoment D μ a (q l))
    (fun l=>(cavityCubicPairMoment_bounds D μ a (q l)).1) T (i r) (k r) (hik r)
  exact hh.trans (by linarith [hb 0,hb 1,hb 2])

end QuantitativeFollowup
