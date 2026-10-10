module
public import FourPapersCommon.FiniteObservationRefinementTransport
public import FourPapersCommon.FiniteObservationLeafGeometry
public import FourPapersCommon.FiniteCascadeChargeLevels

@[expose] public section

/-! Genuine terminal-leaf and branch geometry under observation refinement.
Added unary observations preserve every spin and create no new branch. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

@[reducible] def observationPadLeafEmbed {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (d : ℕ)→ObservationLeaf T→ObservationLeaf (observationTreePad T d)
  | 0 => id
  | d+1 => observationPadLeafEmbed T d

@[reducible] def observationPadRecordProject {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (d : ℕ)→Records E S (observationTreePad T d)→Records E S T
  | 0 => id
  | d+1 => observationPadRecordProject T d ∘ Prod.snd

theorem observationBlockCollapse_snd {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d : ℕ) (z : Records E S (.advance (observationTreePad T d))) :
    (observationBlockCollapse T d z).2=observationPadRecordProject T d z.2 := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

theorem observationPadLeafEmbed_spin {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d : ℕ) (i : ObservationLeaf T) (z : Records E S (observationTreePad T d)) :
    observationLeafSpin (observationTreePad T d) (observationPadLeafEmbed T d i) z=
      observationLeafSpin T i (observationPadRecordProject T d z) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

theorem observationPadLeafEmbed_commonLevel {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d : ℕ) (i k : ObservationLeaf T) :
    observationCommonLevel (observationTreePad T d) (observationPadLeafEmbed T d i)
      (observationPadLeafEmbed T d k)=observationCommonLevel T i k := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem observationPadLeafEmbed_injective {j : ℕ} (T : FiniteTerminalGenealogy j) (d : ℕ) :
    Function.Injective (observationPadLeafEmbed T d) := by
  induction d with
  | zero => exact Function.injective_id
  | succ d ih => exact ih

@[reducible] def observationRefinementLeafEmbed (d : ℕ→ℕ) : {j : ℕ}→
    (T : FiniteTerminalGenealogy j)→ObservationLeaf T→ObservationLeaf (observationRefineTree d T)
  | _, .leaf => id
  | _, @FiniteTerminalGenealogy.advance j T =>
      observationPadLeafEmbed (observationRefineTree d T) (d j) ∘ observationRefinementLeafEmbed d T
  | _, .fork T U => Sum.map (observationRefinementLeafEmbed d T) (observationRefinementLeafEmbed d U)

theorem observationRefinementLeafEmbed_spin {E S : Type} (d : ℕ→ℕ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T)
    (z : Records E S (observationRefineTree d T)) :
    observationLeafSpin (observationRefineTree d T) (observationRefinementLeafEmbed d T i) z=
      observationLeafSpin T i (observationRefinementProject d T z) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
    change observationLeafSpin (observationTreePad (observationRefineTree d T) (d j))
      (observationPadLeafEmbed _ _ (observationRefinementLeafEmbed d T i)) z.2=_
    rw [observationPadLeafEmbed_spin,ih,←observationBlockCollapse_snd]
    rfl
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

theorem observationRefinementLeafEmbed_commonLevel (d : ℕ→ℕ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i k : ObservationLeaf T) :
    observationCommonLevel (observationRefineTree d T) (observationRefinementLeafEmbed d T i)
      (observationRefinementLeafEmbed d T k)=observationRefinementDepth d (observationCommonLevel T i k) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
    change observationCommonLevel (observationTreePad (observationRefineTree d T) (d j))
      (observationPadLeafEmbed _ _ (observationRefinementLeafEmbed d T i))
      (observationPadLeafEmbed _ _ (observationRefinementLeafEmbed d T k))=_
    rw [observationPadLeafEmbed_commonLevel]
    exact ih i k
  | fork T U ihT ihU => cases i with
    | inl i => cases k with
      | inl k => exact ihT i k
      | inr k => rfl
    | inr i => cases k with
      | inl k => rfl
      | inr k => exact ihU i k

theorem observationRefinementLeafEmbed_injective (d : ℕ→ℕ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) : Function.Injective (observationRefinementLeafEmbed d T) := by
  induction T with
  | leaf => exact Function.injective_id
  | @advance j T ih => exact (observationPadLeafEmbed_injective _ (d j)).comp ih
  | fork T U ihT ihU => exact Sum.map_injective.mpr ⟨ihT,ihU⟩

theorem finiteCascadeUnweightedBranchSum_pad (χ : ℕ→ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d : ℕ) :
    finiteCascadeUnweightedBranchSum χ (observationTreePad T d)=finiteCascadeUnweightedBranchSum χ T := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem finiteCascadeUnweightedBranchSum_observationRefinement (χ : ℕ→ℝ) (d : ℕ→ℕ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeUnweightedBranchSum χ (observationRefineTree d T)=
      finiteCascadeUnweightedBranchSum (fun l=>χ (observationRefinementDepth d l)) T := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
    change finiteCascadeUnweightedBranchSum χ (observationTreePad (observationRefineTree d T) (d j))=_
    rw [finiteCascadeUnweightedBranchSum_pad]
    exact ih
  | fork T U ihT ihU =>
    change finiteCascadeUnweightedBranchSum χ (observationRefineTree d T)+
      finiteCascadeUnweightedBranchSum χ (observationRefineTree d U)+_=_
    rw [ihT,ihU]

@[reducible] def observationRefinementDepthLeafEmbed (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    ObservationLeaf T→ObservationLeaf (observationTreeDepthCast h (observationRefineTree d T)) := by
  subst l
  exact observationRefinementLeafEmbed d T

theorem observationRefinementDepthLeafEmbed_spin {E S : Type} (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l)
    (i : ObservationLeaf T) (z : Records E S (observationTreeDepthCast h (observationRefineTree d T))) :
    observationLeafSpin _ (observationRefinementDepthLeafEmbed d T h i) z=
      observationLeafSpin T i (observationRefinementDepthProject d T h z) := by
  subst l
  exact observationRefinementLeafEmbed_spin d T i z

theorem observationRefinementDepthLeafEmbed_commonLevel (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) (i k : ObservationLeaf T) :
    observationCommonLevel _ (observationRefinementDepthLeafEmbed d T h i)
      (observationRefinementDepthLeafEmbed d T h k)=
      observationRefinementDepth d (observationCommonLevel T i k) := by
  subst l
  exact observationRefinementLeafEmbed_commonLevel d T i k

theorem finiteCascadeUnweightedBranchSum_observationRefinementDepth (χ : ℕ→ℝ) (d : ℕ→ℕ)
    {j l : ℕ} (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    finiteCascadeUnweightedBranchSum χ (observationTreeDepthCast h (observationRefineTree d T))=
      finiteCascadeUnweightedBranchSum (fun m=>χ (observationRefinementDepth d m)) T := by
  subst l
  exact finiteCascadeUnweightedBranchSum_observationRefinement χ d T

end FourPapersCommon
