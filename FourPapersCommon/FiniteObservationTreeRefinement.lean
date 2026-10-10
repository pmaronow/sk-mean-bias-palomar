module
public import FourPapersCommon.FiniteObservationTreeTopology

@[expose] public section

/-! Explicit subdivision of every advance, preserving each original field
and every terminal spin while discarding only the added observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 128

@[reducible] def observationTreePad {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (d : ℕ)→FiniteTerminalGenealogy (j+d)
  | 0 => T
  | d+1 => .advance (observationTreePad T d)

@[reducible] def observationBlockCollapse {E S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) : (d : ℕ)→
      Records E S (.advance (observationTreePad T d))→E×Records E S T
  | 0 => id
  | d+1 => observationBlockCollapse T d ∘ Prod.snd

theorem measurable_observationBlockCollapse {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d : ℕ) :
    Measurable (observationBlockCollapse (E:=E) (S:=S) T d) := by
  induction d with
  | zero => exact measurable_id
  | succ d ih => exact ih.comp measurable_snd

theorem continuous_observationBlockCollapse {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d : ℕ) :
    Continuous (observationBlockCollapse (E:=E) (S:=S) T d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact ih.comp continuous_snd

def observationRefinementDepth (d : ℕ→ℕ) : ℕ→ℕ
  | 0 => 0
  | j+1 => observationRefinementDepth d j+d j+1

@[reducible] def observationRefineTree (d : ℕ→ℕ) : {j : ℕ}→
    FiniteTerminalGenealogy j→FiniteTerminalGenealogy (observationRefinementDepth d j)
  | _, .leaf => .leaf
  | _, @FiniteTerminalGenealogy.advance j T => .advance (observationTreePad (observationRefineTree d T) (d j))
  | _, .fork T U => .fork (observationRefineTree d T) (observationRefineTree d U)

@[reducible] def observationRefinementProject {E S : Type} (d : ℕ→ℕ) : {j : ℕ}→
    (T : FiniteTerminalGenealogy j)→Records E S (observationRefineTree d T)→Records E S T
  | _, .leaf => id
  | _, @FiniteTerminalGenealogy.advance j T =>
      Prod.map id (observationRefinementProject d T) ∘
        observationBlockCollapse (observationRefineTree d T) (d j)
  | _, .fork T U => Prod.map (observationRefinementProject d T) (observationRefinementProject d U)

theorem measurable_observationRefinementProject {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    (d : ℕ→ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (observationRefinementProject (E:=E) (S:=S) d T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact (measurable_id.prodMap ih).comp (measurable_observationBlockCollapse _ _)
  | fork T U ihT ihU => exact ihT.prodMap ihU

theorem continuous_observationRefinementProject {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (d : ℕ→ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Continuous (observationRefinementProject (E:=E) (S:=S) d T) := by
  induction T with
  | leaf => exact continuous_id
  | advance T ih => exact (continuous_id.prodMap ih).comp (continuous_observationBlockCollapse _ _)
  | fork T U ihT ihU => exact ihT.prodMap ihU

theorem observationRefinementDepth_strictMono (d : ℕ→ℕ) : StrictMono (observationRefinementDepth d) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [observationRefinementDepth]
  omega

end FourPapersCommon
