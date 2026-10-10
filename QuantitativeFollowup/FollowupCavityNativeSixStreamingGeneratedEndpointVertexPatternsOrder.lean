module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsGeometry

@[expose] public section

/-! The genuine endpoint observations impose no additional ordering event.
The selected old root or terminal atom remains the actual constant atom
under the copied endpoint labels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

private theorem endpoint_atom_congr
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (q Q : CavityGeneratedHistory Paper.Overlap m → Paper.Overlap)
    (hq : Measurable q) (hQ : Measurable Q) (he : q=Q) :
    CavityGeneratedMarkProgram.atom P q hq = CavityGeneratedMarkProgram.atom P Q hQ := by
  subst Q
  rfl

theorem nativeStreamingGeneratedEndpointComponent_orderSet
    (W : CavityGeneratedConstructedComponent m) :
    nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent W) =
      nativeStreamingGeneratedComponentOrderSet W := by
  ext h
  change (∀j : Fin (W.depth+2),
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (j+1)).value h ≤
      (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) j).value h) ↔
    (∀j : Fin W.depth, (cavityGeneratedFiniteClockLabels W.label (j+1)).value h ≤
      (cavityGeneratedFiniteClockLabels W.label j).value h)
  constructor
  · intro hh j
    have H := hh ⟨j.val+1,by omega⟩
    simpa only [nativeStreamingGeneratedEndpointLabels_global_succ] using H
  · intro hh j
    rcases j with ⟨j,hj⟩
    cases j with
    | zero =>
        change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) 1).value h ≤
          (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) 0).value h
        rw [nativeStreamingGeneratedEndpointLabels_global_succ,nativeStreamingGeneratedEndpointLabels_global_zero]
        change (cavityGeneratedFiniteClockLabels W.label 0).value h ≤ 1
        exact ((cavityGeneratedFiniteClockLabels W.label 0).value h).property.2
    | succ j =>
        change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (j+1+1)).value h ≤
          (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (j+1)).value h
        rw [nativeStreamingGeneratedEndpointLabels_global_succ,nativeStreamingGeneratedEndpointLabels_global_succ]
        by_cases hjo : j < W.depth
        · exact hh ⟨j,hjo⟩
        · have he : j=W.depth := by omega
          subst j
          have hi : cavityGeneratedFiniteClockLabels W.label W.depth = .initial := by
            unfold cavityGeneratedFiniteClockLabels
            rw [dif_pos le_rfl]
            exact W.initial_label
          have ho : cavityGeneratedFiniteClockLabels W.label (W.depth+1) = .initial := by
            unfold cavityGeneratedFiniteClockLabels
            rw [dif_neg (by omega)]
          rw [ho,hi]

theorem nativeStreamingGeneratedEndpointVertex_clock
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h
      (nativeStreamingGeneratedEndpointVertex W v).depth =
        nativeStreamingGeneratedComponentClock W h v.depth := by
  rw [nativeStreamingGeneratedEndpointComponent_clock,nativeStreamingGeneratedEndpointVertex_depth,
    nativeStreamingGeneratedEndpointClock_succ]

def nativeStreamingGeneratedEndpointAtomProgram
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) : CavityGeneratedMarkProgram Paper.Overlap (m+1) :=
  nativeStreamingGeneratedVertexAtomProgram (P.restrict (nativeStreamingGeneratedComponentOrderSet W))
    (nativeStreamingGeneratedEndpointComponent W) (nativeStreamingGeneratedEndpointVertex W v)

theorem nativeStreamingGeneratedEndpointAtomProgram_root
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m) :
    nativeStreamingGeneratedEndpointAtomProgram P W (.root W.tree) =
      .atom (P.restrict (nativeStreamingGeneratedComponentOrderSet W))
        (fun _ => (0 : Paper.Overlap)) measurable_const := by
  unfold nativeStreamingGeneratedEndpointAtomProgram nativeStreamingGeneratedVertexAtomProgram
    cavityGeneratedVertexAtomProgram
  apply endpoint_atom_congr
  funext h
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W) (W.depth+1)).value h = 0
  rw [nativeStreamingGeneratedEndpointLabels_global_succ]
  have hi : cavityGeneratedFiniteClockLabels W.label W.depth = .initial := by
    unfold cavityGeneratedFiniteClockLabels
    rw [dif_pos le_rfl]
    exact W.initial_label
  rw [hi]
  rfl

theorem nativeStreamingGeneratedEndpointAtomProgram_terminal
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (i : ObservationLeaf W.tree) :
    nativeStreamingGeneratedEndpointAtomProgram P W (observationLeafVertex W.tree i) =
      .atom (P.restrict (nativeStreamingGeneratedComponentOrderSet W))
        (fun _ => (1 : Paper.Overlap)) measurable_const := by
  unfold nativeStreamingGeneratedEndpointAtomProgram nativeStreamingGeneratedVertexAtomProgram
    cavityGeneratedVertexAtomProgram
  apply endpoint_atom_congr
  funext h
  change
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEndpointLabels W)
      (nativeStreamingGeneratedEndpointVertex W (observationLeafVertex W.tree i)).depth).value h = 1
  rw [nativeStreamingGeneratedEndpointVertex_depth,observationLeafVertex_depth,
    nativeStreamingGeneratedEndpointLabels_global_succ]
  have ht : cavityGeneratedFiniteClockLabels W.label 0 = .terminal := by
    unfold cavityGeneratedFiniteClockLabels
    rw [dif_pos (Nat.zero_le _)]
    exact W.terminal_label
  rw [ht]
  rfl

end QuantitativeFollowup
