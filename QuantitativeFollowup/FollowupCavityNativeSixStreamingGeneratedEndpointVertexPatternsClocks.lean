module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsResults

@[expose] public section

/-! Genuine endpoint padding keeps the two fixed endpoint labels and
copies every old physical clock one slot inward. Its added terminal and
initial observations have duplicated physical time 1 and 0. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedEndpointLabels (W : CavityGeneratedConstructedComponent m)
    (j : Fin (W.depth+3)) : CavityGeneratedClockLabel m :=
  if j.val=0 then .terminal else cavityGeneratedFiniteClockLabels W.label (j.val-1)

theorem nativeStreamingGeneratedEndpointLabels_terminal
    (W : CavityGeneratedConstructedComponent m) :
    nativeStreamingGeneratedEndpointLabels W 0 = .terminal := by
  rfl

theorem nativeStreamingGeneratedEndpointLabels_initial
    (W : CavityGeneratedConstructedComponent m) :
    nativeStreamingGeneratedEndpointLabels W (Fin.last (W.depth+2)) = .initial := by
  unfold nativeStreamingGeneratedEndpointLabels
  rw [if_neg (by change W.depth+2 ≠ 0; omega)]
  change cavityGeneratedFiniteClockLabels W.label (W.depth+2-1) = _
  rw [show W.depth+2-1=W.depth+1 by omega]
  unfold cavityGeneratedFiniteClockLabels
  rw [dif_neg (by omega)]

theorem nativeStreamingGeneratedEndpointLabels_global_zero
    (W : CavityGeneratedConstructedComponent m) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) 0 = .terminal := by
  simp only [cavityGeneratedFiniteClockLabels,Nat.zero_le,dif_pos]
  rfl

theorem nativeStreamingGeneratedEndpointLabels_global_succ
    (W : CavityGeneratedConstructedComponent m) (j : ℕ) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (j+1) =
      cavityGeneratedFiniteClockLabels W.label j := by
  by_cases hj : j+1 ≤ W.depth+2
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj]
    change (if j+1=0 then .terminal else cavityGeneratedFiniteClockLabels W.label (j+1-1)) = _
    rw [if_neg (by omega),Nat.add_sub_cancel]
    all_goals rfl
  · have hjo : ¬j ≤ W.depth := by omega
    simp only [cavityGeneratedFiniteClockLabels,dif_neg hj,dif_neg hjo]

def nativeStreamingGeneratedEndpointClock (W : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℕ → Paper.Overlap :=
  cavityGeneratedClippedClock (fun j =>
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) j).value h)

theorem nativeStreamingGeneratedEndpointClock_zero
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedEndpointClock W h 0 = 1 := by
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) 0).value h = 1
  rw [nativeStreamingGeneratedEndpointLabels_global_zero]
  rfl

theorem nativeStreamingGeneratedEndpointClock_succ
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (j : ℕ) :
    nativeStreamingGeneratedEndpointClock W h (j+1) = nativeStreamingGeneratedComponentClock W h j := by
  induction j with
  | zero =>
      change min (nativeStreamingGeneratedEndpointClock W h 0)
        ((cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) 1).value h) = _
      rw [nativeStreamingGeneratedEndpointClock_zero,nativeStreamingGeneratedEndpointLabels_global_succ]
      change min 1 (nativeStreamingGeneratedComponentClock W h 0) = _
      rw [nativeStreamingGeneratedComponentClock_terminal,min_self]
  | succ j ih =>
      change min (nativeStreamingGeneratedEndpointClock W h (j+1))
        ((cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (j+1+1)).value h) =
          min (nativeStreamingGeneratedComponentClock W h j)
            ((cavityGeneratedFiniteClockLabels W.label (j+1)).value h)
      rw [ih,nativeStreamingGeneratedEndpointLabels_global_succ]

theorem nativeStreamingGeneratedComponentClock_after_initial
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (j : ℕ) (hj : W.depth ≤ j) :
    nativeStreamingGeneratedComponentClock W h j = 0 := by
  apply le_antisymm
  · simpa only [nativeStreamingGeneratedComponentClock_initial] using
      nativeStreamingGeneratedComponentClock_antitone W h hj
  · exact (nativeStreamingGeneratedComponentClock W h j).property.1

theorem nativeStreamingGeneratedEndpointClock_duplicate_initial
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedEndpointClock W h (W.depth+2) =
      nativeStreamingGeneratedEndpointClock W h (W.depth+1) := by
  rw [nativeStreamingGeneratedEndpointClock_succ,nativeStreamingGeneratedEndpointClock_succ,
    nativeStreamingGeneratedComponentClock_after_initial W h (W.depth+1) (by omega),
    nativeStreamingGeneratedComponentClock_initial]

theorem nativeStreamingGeneratedEndpointClock_duplicate_terminal
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedEndpointClock W h 1 = nativeStreamingGeneratedEndpointClock W h 0 := by
  rw [nativeStreamingGeneratedEndpointClock_succ,nativeStreamingGeneratedComponentClock_terminal,
    nativeStreamingGeneratedEndpointClock_zero]

end QuantitativeFollowup
