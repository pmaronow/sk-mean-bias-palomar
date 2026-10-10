module
public import FourPapersCommon.FiniteObservationTreePairPruning
public import FourPapersCommon.FiniteCascadeChargeLevels

@[expose] public section

/-! The common split of two distinct terminal descendants is an actual
branch level. Its nonnegative test value is bounded by the literal sum
of branch-level test values in the genealogy. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 500000

 theorem observationPair_level_le_branchSum (χ : ℕ→ℝ) (hχ : ∀j,0≤χ j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (i k : ObservationLeaf T) (hik : i≠k) :
    χ (observationCommonLevel T i k)≤finiteCascadeUnweightedBranchSum χ T := by
  induction T with
  | leaf => exact (hik (Subsingleton.elim i k)).elim
  | advance T ih => exact ih i k hik
  | @fork j T U ihT ihU =>
      have hT:=finiteCascadeUnweightedBranchSum_nonneg χ hχ T
      have hU:=finiteCascadeUnweightedBranchSum_nonneg χ hχ U
      cases i with
      | inl i =>
          cases k with
          | inl k =>
              have hh:=ihT i k (fun h=>hik (congrArg Sum.inl h))
              change χ (observationCommonLevel T i k)≤
                finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j
              linarith [hχ j]
          | inr k =>
              change χ j≤finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j
              linarith
      | inr i =>
          cases k with
          | inl k =>
              change χ j≤finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j
              linarith
          | inr k =>
              have hh:=ihU i k (fun h=>hik (congrArg Sum.inr h))
              change χ (observationCommonLevel U i k)≤
                finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j
              linarith [hχ j]

end FourPapersCommon
