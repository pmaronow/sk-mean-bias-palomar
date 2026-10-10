module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservationSchedule

@[expose] public section

/-! Exact indices of the two requested native observations in the fixed
refinement. Coincident times use the same vertex and retain the actual
conditional product of terminal marks. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1200000

 def nativeStreamingPairObservationIndex (de df : ℕ) (r l : Paper.Overlap) : ℕ :=
  if de=df then if r<l then 1 else 0 else 0

 theorem nativeStreamingPairObservationIndex_lt (de df : ℕ) (r l : Paper.Overlap) :
    nativeStreamingPairObservationIndex de df r l<2 := by
  unfold nativeStreamingPairObservationIndex
  split_ifs <;> omega

 theorem nativeStreamingPairObservationIndex_level (q : ℕ→Paper.Overlap)
    (de df : ℕ) (r l : Paper.Overlap) :
    nativeStreamingPairObservationSchedule q de df r l
      (observationRefinementDepth nativeStreamingPairObservationSubdivision de+
        nativeStreamingPairObservationIndex de df r l+1)=r := by
  rw [nativeStreamingPairObservationSubdivision_depth]
  by_cases he : de=df
  · subst df
    by_cases hr : r<l
    · have hdiv : (3*de+1+1)/3=de := by omega
      have hmod : (3*de+1+1)%3=2 := by omega
      simp only [nativeStreamingPairObservationIndex,if_pos rfl,if_pos hr,
        nativeStreamingPairObservationSchedule,hdiv,hmod,
        if_neg (by decide : ¬(2=0)),if_neg (by decide : ¬(2=1)),
        nativeStreamingPairObservationTimes,ite_true,ite_false]
      simp only [if_pos rfl,min_eq_left hr.le,ite_true,ite_false]
    · have hdiv : (3*de+0+1)/3=de := by omega
      have hmod : (3*de+0+1)%3=1 := by omega
      simp only [nativeStreamingPairObservationIndex,if_pos rfl,if_neg hr,
        nativeStreamingPairObservationSchedule,hdiv,hmod,
        if_neg (by decide : ¬(1=0)),if_pos rfl,nativeStreamingPairObservationTimes,
        ite_true,ite_false]
      simp only [if_pos rfl,max_eq_left (le_of_not_gt hr),ite_true,ite_false]
  · have hn : ¬df=de := Ne.symm he
    have hdiv : (3*de+0+1)/3=de := by omega
    have hmod : (3*de+0+1)%3=1 := by omega
    simp only [nativeStreamingPairObservationIndex,if_neg he,
      nativeStreamingPairObservationSchedule,hdiv,hmod,
      if_neg (by decide : ¬(1=0)),if_pos rfl,nativeStreamingPairObservationTimes,
      if_neg hn,ite_true,ite_false]

 theorem nativeStreamingPairObservationTimes_swap (q : ℕ→Paper.Overlap)
    (de df j : ℕ) (r l : Paper.Overlap) :
    nativeStreamingPairObservationTimes q de df j r l=
      nativeStreamingPairObservationTimes q df de j l r := by
  unfold nativeStreamingPairObservationTimes
  split_ifs <;> simp_all only [max_comm,min_comm]

 theorem nativeStreamingPairObservationSchedule_swap (q : ℕ→Paper.Overlap)
    (de df : ℕ) (r l : Paper.Overlap) :
    nativeStreamingPairObservationSchedule q de df r l=
      nativeStreamingPairObservationSchedule q df de l r := by
  funext k
  unfold nativeStreamingPairObservationSchedule
  rw [nativeStreamingPairObservationTimes_swap]

 theorem nativeStreamingPairObservationIndex_second_level (q : ℕ→Paper.Overlap)
    (de df : ℕ) (r l : Paper.Overlap) :
    nativeStreamingPairObservationSchedule q de df r l
      (observationRefinementDepth nativeStreamingPairObservationSubdivision df+
        nativeStreamingPairObservationIndex df de l r+1)=l := by
  rw [nativeStreamingPairObservationSchedule_swap]
  exact nativeStreamingPairObservationIndex_level q df de l r

end QuantitativeFollowup
