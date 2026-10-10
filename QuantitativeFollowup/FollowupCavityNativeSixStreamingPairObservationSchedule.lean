module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedKernel
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! A fixed two-slot observation refinement realizes both ancestral
observations. Empty slots duplicate an original field; two selected
observations at one depth use their actual minimum and maximum times.
This fixed tree is suitable for genuine moving-profile weak limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

 def nativeStreamingPairObservationSubdivision (_ : ℕ) : ℕ := 2

 theorem nativeStreamingPairObservationSubdivision_depth (j : ℕ) :
    observationRefinementDepth nativeStreamingPairObservationSubdivision j=3*j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [observationRefinementDepth,ih]
      unfold nativeStreamingPairObservationSubdivision
      omega

 def nativeStreamingPairObservationTimes (q : ℕ→Paper.Overlap) (de df j : ℕ)
    (r l : Paper.Overlap) : Paper.Overlap × Paper.Overlap :=
  if de=j then if df=j then (max r l,min r l) else (r,r)
  else if df=j then (l,l) else (q j,q j)

 def nativeStreamingPairObservationSchedule (q : ℕ→Paper.Overlap) (de df : ℕ)
    (r l : Paper.Overlap) (k : ℕ) : Paper.Overlap :=
  if k%3=0 then q (k/3)
  else if k%3=1 then (nativeStreamingPairObservationTimes q de df (k/3) r l).1
  else (nativeStreamingPairObservationTimes q de df (k/3) r l).2

 theorem nativeStreamingPairObservationSchedule_refinement (q : ℕ→Paper.Overlap)
    (de df : ℕ) (r l : Paper.Overlap) (j : ℕ) :
    nativeStreamingPairObservationSchedule q de df r l
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j)=q j := by
  rw [nativeStreamingPairObservationSubdivision_depth]
  simp [nativeStreamingPairObservationSchedule]

 theorem nativeStreamingPairObservationTimes_bounds (q : ℕ→Paper.Overlap)
    (hq : Antitone q) (de df j : ℕ) (r l : Paper.Overlap)
    (hr : q (de+1)≤r ∧ r≤q de) (hl : q (df+1)≤l ∧ l≤q df) :
    q (j+1)≤(nativeStreamingPairObservationTimes q de df j r l).2 ∧
    (nativeStreamingPairObservationTimes q de df j r l).2≤
      (nativeStreamingPairObservationTimes q de df j r l).1 ∧
    (nativeStreamingPairObservationTimes q de df j r l).1≤q j := by
  unfold nativeStreamingPairObservationTimes
  split_ifs with he hf hf
  · subst de
    subst df
    exact ⟨le_min hr.1 hl.1,(min_le_left r l).trans (le_max_left r l),max_le hr.2 hl.2⟩
  · subst de
    exact ⟨hr.1,le_rfl,hr.2⟩
  · subst df
    exact ⟨hl.1,le_rfl,hl.2⟩
  · exact ⟨hq (Nat.le_succ j),le_rfl,le_rfl⟩

 theorem nativeStreamingPairObservationSchedule_antitone (q : ℕ→Paper.Overlap)
    (hq : Antitone q) (de df : ℕ) (r l : Paper.Overlap)
    (hr : q (de+1)≤r ∧ r≤q de) (hl : q (df+1)≤l ∧ l≤q df) :
    Antitone (nativeStreamingPairObservationSchedule q de df r l) := by
  apply antitone_nat_of_succ_le
  intro k
  have hm : k%3<3 := Nat.mod_lt k (by decide)
  have hk := Nat.mod_add_div k 3
  have hb := nativeStreamingPairObservationTimes_bounds q hq de df (k/3) r l hr hl
  rcases (show k%3=0 ∨ k%3=1 ∨ k%3=2 by omega) with h0|h1|h2
  · have hd : (k+1)/3=k/3 := by omega
    have hnext : (k+1)%3=1 := by omega
    simpa only [nativeStreamingPairObservationSchedule,h0,hnext,hd,
      if_neg (by decide : ¬(1=0)),if_pos rfl,ite_true,ite_false] using hb.2.2
  · have hd : (k+1)/3=k/3 := by omega
    have hnext : (k+1)%3=2 := by omega
    simpa only [nativeStreamingPairObservationSchedule,h1,hnext,hd,
      if_neg (by decide : ¬(1=0)),if_neg (by decide : ¬(2=0)),
      if_neg (by decide : ¬(2=1)),if_pos rfl,ite_true,ite_false] using hb.2.1
  · have hd : (k+1)/3=k/3+1 := by omega
    have hnext : (k+1)%3=0 := by omega
    simpa only [nativeStreamingPairObservationSchedule,h2,hnext,hd,
      if_neg (by decide : ¬(2=0)),if_neg (by decide : ¬(2=1)),if_pos rfl,ite_true,ite_false] using hb.1

 theorem tendsto_nativeStreamingPairObservationSchedule {L : Type*} {f : Filter L}
    (q : ℕ→Paper.Overlap) (de df k : ℕ) {rj lj : L→Paper.Overlap} {r l : Paper.Overlap}
    (hr : Tendsto rj f (𝓝 r)) (hl : Tendsto lj f (𝓝 l)) :
    Tendsto (fun N=>nativeStreamingPairObservationSchedule q de df (rj N) (lj N) k) f
      (𝓝 (nativeStreamingPairObservationSchedule q de df r l k)) := by
  unfold nativeStreamingPairObservationSchedule nativeStreamingPairObservationTimes
  split_ifs
  · exact tendsto_const_nhds
  · exact hr.max hl
  · exact hr
  · exact hl
  · exact tendsto_const_nhds
  · exact hr.min hl
  · exact hr
  · exact hl
  · exact tendsto_const_nhds

end QuantitativeFollowup
