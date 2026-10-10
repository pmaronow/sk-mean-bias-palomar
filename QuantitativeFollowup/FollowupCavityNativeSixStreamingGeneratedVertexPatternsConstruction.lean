module
public import QuantitativeFollowup.FollowupCavityGeneratedVertexAtomGraft
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponents
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFiniteTreeAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherence

@[expose] public section

/-! Concrete generated receivers for atom attachments at retained interior
vertices. The old observations remain fixed, and the new continuation is
an actual one- or two-descendant genealogy. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

inductive NativeStreamingGeneratedVertexKind
  | single
  | current

namespace NativeStreamingGeneratedVertexKind

def continuation : NativeStreamingGeneratedVertexKind → (j : ℕ) → FiniteTerminalGenealogy j
  | .single => observationLinearTree
  | .current => nativeStreamingCurrentPairTree

theorem continuation_constructed (k : NativeStreamingGeneratedVertexKind)
    {M : ℕ} (labels : ℕ → CavityGeneratedClockLabel M) (j : ℕ) (i : Fin M)
    (hi : labels j=.mark i) :
    CavityGeneratedGenealogyConstruction labels (k.continuation j) := by
  have hl (d : ℕ) : CavityGeneratedGenealogyConstruction labels (observationLinearTree d) := by
    rw [nativeStreamingLinearTree_eq_finite_linear]
    exact .linear d
  cases k with
  | single => exact hl j
  | current => exact .fork i hi (hl j) (hl j)

end NativeStreamingGeneratedVertexKind

def nativeStreamingGeneratedComponentClock (W : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℕ → Paper.Overlap :=
  cavityGeneratedClippedClock (fun j => (cavityGeneratedFiniteClockLabels W.label j).value h)

def nativeStreamingGeneratedComponentForest (W : CavityGeneratedConstructedComponent m) :
    CavityGeneratedConstructedForest m :=
  cavityGeneratedForestOfComponents (fun _ : Fin 1 => W)

theorem nativeStreamingGeneratedComponentClock_eq_forest
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock W h =
      (nativeStreamingGeneratedComponentForest W).clockTemplate.clock h (0 : Fin 1) := by
  apply congrArg cavityGeneratedClippedClock
  funext j
  change (cavityGeneratedFiniteClockLabels W.label j).value h=
    (if hj : j≤W.depth then (W.label ⟨j,by omega⟩).value h else 0)
  by_cases hj : j≤W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj]
  · simp only [cavityGeneratedFiniteClockLabels,dif_neg hj,CavityGeneratedClockLabel.value]

theorem nativeStreamingGeneratedComponentClock_initial
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock W h W.depth=0 := by
  rw [nativeStreamingGeneratedComponentClock_eq_forest]
  exact (nativeStreamingGeneratedComponentForest W).clockTemplate.clock_initial h (0 : Fin 1)

theorem nativeStreamingGeneratedComponentClock_continuous
    (W : CavityGeneratedConstructedComponent m) (j : ℕ) :
    Continuous (fun h => nativeStreamingGeneratedComponentClock W h j) := by
  exact cavityGeneratedClippedClock_continuous _
    (fun p => (cavityGeneratedFiniteClockLabels W.label p).continuous_value) j

theorem nativeStreamingGeneratedComponentClock_antitone
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    Antitone (nativeStreamingGeneratedComponentClock W h) :=
  antitone_nat_of_succ_le (fun j => cavityGeneratedClippedClock_step_le _ j)

theorem nativeStreamingGeneratedComponentClock_terminal
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock W h 0=1 := by
  change (cavityGeneratedFiniteClockLabels W.label 0).value h=1
  simp only [cavityGeneratedFiniteClockLabels, Nat.zero_le, dif_pos]
  change (W.label 0).value h=1
  rw [W.terminal_label]
  rfl

def nativeStreamingGeneratedComponentOrderSet (W : CavityGeneratedConstructedComponent m) :
    Set (CavityGeneratedHistory Paper.Overlap m) :=
  {h | ∀j : Fin W.depth,
    (cavityGeneratedFiniteClockLabels W.label (j+1)).value h ≤
      (cavityGeneratedFiniteClockLabels W.label j).value h}

theorem isClosed_nativeStreamingGeneratedComponentOrderSet
    (W : CavityGeneratedConstructedComponent m) :
    IsClosed (nativeStreamingGeneratedComponentOrderSet W) := by
  change IsClosed {h | ∀j : Fin W.depth, _}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_le (cavityGeneratedFiniteClockLabels W.label (j+1)).continuous_value
    (cavityGeneratedFiniteClockLabels W.label j).continuous_value

theorem nativeStreamingGeneratedComponentClock_eq_label_of_mem
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W) (j : ℕ) (hj : j≤W.depth) :
    nativeStreamingGeneratedComponentClock W h j=
      (cavityGeneratedFiniteClockLabels W.label j).value h := by
  apply cavityGeneratedClippedClock_eq _ W.depth _ j hj
  intro p hp
  exact hh ⟨p,hp⟩

def nativeStreamingGeneratedVertexLabels (W : CavityGeneratedConstructedComponent m)
    (d : ℕ) (j : Fin (W.depth+1)) : CavityGeneratedClockLabel (m+1) :=
  if j.val=d then .mark (Fin.last m) else (W.label j).reindex Fin.castSucc

theorem nativeStreamingGeneratedVertexLabels_global
    (W : CavityGeneratedConstructedComponent m) (d : ℕ) (hd : d≤W.depth) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels W d) =
      cavityGeneratedAttachedClockLabels (cavityGeneratedFiniteClockLabels W.label) d := by
  funext j
  by_cases hj : j≤W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj,
      nativeStreamingGeneratedVertexLabels,cavityGeneratedAttachedClockLabels]
  · have hne : j≠d := by intro he; subst j; exact hj hd
    simp only [cavityGeneratedFiniteClockLabels,dif_neg hj,
      cavityGeneratedAttachedClockLabels,if_neg hne,CavityGeneratedClockLabel.reindex]

def nativeStreamingGeneratedVertexComponent
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedConstructedComponent (m+1) where
  depth := W.depth
  tree := finiteCascadeContinuationGraft k.continuation v
  label := nativeStreamingGeneratedVertexLabels W v.depth
  terminal_label := by
    unfold nativeStreamingGeneratedVertexLabels
    rw [if_neg (by change ¬0=v.depth; omega),W.terminal_label]
    rfl
  initial_label := by
    unfold nativeStreamingGeneratedVertexLabels
    rw [if_neg (by change W.depth≠v.depth; omega),W.initial_label]
    rfl
  construction := by
    rw [nativeStreamingGeneratedVertexLabels_global W v.depth hvJ.le]
    let labels := cavityGeneratedAttachedClockLabels (cavityGeneratedFiniteClockLabels W.label) v.depth
    have hat : labels v.depth=.mark (Fin.last m) :=
      cavityGeneratedAttachedClockLabels_at_depth _ _
    exact .graft k.continuation v (Fin.last m) hat
      (W.construction.attached_clock_relabel v.depth)
      (k.continuation_constructed labels v.depth (Fin.last m) hat)

def nativeStreamingGeneratedVertexAtomProgram
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) : CavityGeneratedMarkProgram Paper.Overlap (m+1) :=
  cavityGeneratedVertexAtomProgram P (cavityGeneratedFiniteClockLabels W.label) v.depth

theorem nativeStreamingGeneratedVertexAtomProgram_budget
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingGeneratedVertexAtomProgram P W v).budget=P.budget := rfl

theorem nativeStreamingGeneratedVertexComponent_clock_consistent
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) (k : NativeStreamingGeneratedVertexKind) :
    ∀ᵐ H ∂(nativeStreamingGeneratedVertexAtomProgram P W v).measure ν,
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H =
        nativeStreamingGeneratedComponentClock W (cavityGeneratedHistoryPrefix H) := by
  have he := cavityGeneratedAttachedClockLabels_consistent ν P
    (cavityGeneratedFiniteClockLabels W.label) v.depth
  apply he.mono
  intro H hh
  unfold nativeStreamingGeneratedComponentClock
  change cavityGeneratedClippedClock
    (fun j => (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels W v.depth) j).value H)=_
  rw [nativeStreamingGeneratedVertexLabels_global W v.depth hvJ.le]
  exact congrArg cavityGeneratedClippedClock (funext hh)

theorem nativeStreamingGeneratedVertexAtomProgram_prefix_law
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree) :
    ((nativeStreamingGeneratedVertexAtomProgram P W v).measure ν).map cavityGeneratedHistoryPrefix =
      (P.measure ν).withDensity (fun h=>ν {(cavityGeneratedFiniteClockLabels W.label v.depth).value h}) :=
  cavityGeneratedAtom_prefix_law ν P _ _

end QuantitativeFollowup
