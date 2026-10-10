module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairKernelDiagonal
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservationIndices

@[expose] public section

/-! A genuine antitone physical clock fixes the order of distinct marks.
Coincident times collapse by the actual identity transition, so no
index-order assumption is needed in the native law projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingEdgePairObservedKernel_physical_order (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (e f : NativeStreamingEdge T) (p k : ℕ) (r l : Paper.Overlap)
    (hpr : Q (observationRefinementDepth d e.depth+p+1)=r)
    (hkl : Q (observationRefinementDepth d f.depth+k+1)=l) :
    nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k) T e f r l=
      nativeStreamingEdgePairObservedKernel D μ q
        (nativeStreamingEdgeIndexOrder (nativeStreamingPairObservationIndex e.depth f.depth r l)
          (nativeStreamingPairObservationIndex f.depth e.depth l r)) T e f r l := by
  by_cases he : e=f
  · subst f
    by_cases hrl : r=l
    · rw [←hrl]
      exact nativeStreamingEdgePairObservedKernel_order_equal_time D μ q _ _ T e e r
    · have hpkne : p≠k := by
        intro h
        subst k
        exact hrl (hpr.symm.trans hkl)
      by_cases hpk : p<k
      · have hlr : l≤r := by
          rw [←hpr,←hkl]
          exact hQ (by omega)
        have hlt : l<r := lt_of_le_of_ne hlr (Ne.symm hrl)
        simp only [nativeStreamingEdgeIndexOrder,nativeStreamingPairObservationIndex,
          ite_true,if_neg hpkne,if_pos hpk,if_neg (not_lt_of_ge hlr),if_pos hlt]
        rfl
      · have hkp : k<p := by omega
        have hrle : r≤l := by
          rw [←hpr,←hkl]
          exact hQ (by omega)
        have hlt : r<l := lt_of_le_of_ne hrle hrl
        simp only [nativeStreamingEdgeIndexOrder,nativeStreamingPairObservationIndex,
          ite_true,if_neg hpkne,if_neg hpk,if_pos hlt,if_neg (not_lt_of_ge hrle)]
        rfl
  · exact nativeStreamingEdgePairObservedKernel_order_independent D μ q _ _ T e f he r l

end QuantitativeFollowup
