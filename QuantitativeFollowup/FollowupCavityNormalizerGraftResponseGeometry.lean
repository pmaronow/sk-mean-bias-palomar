module
public import QuantitativeFollowup.FollowupCavityFinitePairCubic
public import QuantitativeFollowup.FollowupCavityFutureGraftResponse
public import QuantitativeFollowup.FollowupCavityTerminalObservable

@[expose] public section

/-! Each actual free-measure atom has a binary spin tree on the original
finite profile mesh. Its terminal pair has the genuine native fresh law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityNormalizerGraftAtomDepth {k : ℕ} (i : vectorPosteriorFeatureIndex k) : ℕ :=
  k+2-vectorPosteriorFeatureTime i

theorem cavityNormalizerGraftAtomDepth_le {k : ℕ} (i : vectorPosteriorFeatureIndex k) :
    cavityNormalizerGraftAtomDepth i ≤ k+1 := by
  cases i <;> dsimp [cavityNormalizerGraftAtomDepth,vectorPosteriorFeatureTime] <;> omega

theorem cavityProfileLevel_normalizerGraftAtomDepth (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k) :
    cavityProfileLevel s (cavityNormalizerGraftAtomDepth i)=vectorProfileAtom s i := by
  apply Subtype.ext
  have ht : vectorPosteriorFeatureTime i ≤ k+2 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  rw [cavityProfileLevel,scalarSchemeTransportNode_coe s _ (by omega)]
  change s.q (k+2-(k+2-vectorPosteriorFeatureTime i))=s.q (vectorPosteriorFeatureTime i)
  rw [Nat.sub_sub_self ht]

def cavityNormalizerGraftPairTree {k : ℕ} (i : vectorPosteriorFeatureIndex k) :
    ObservationPairTree (k+1) := finiteCascadeFuturePairTree (cavityNormalizerGraftAtomDepth i) (k+1)

def cavityNormalizerGraftTree {k : ℕ} (i : vectorPosteriorFeatureIndex k) :
    FiniteTerminalGenealogy (k+2) := .advance (cavityNormalizerGraftPairTree i).tree

theorem cavityNormalizerGraftPair_commonLevel (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k) :
    cavityProfileLevel s (observationCommonLevel (cavityNormalizerGraftTree i)
      (observationPairFirstLeaf (cavityNormalizerGraftPairTree i))
      (observationPairSecondLeaf (cavityNormalizerGraftPairTree i)))=vectorProfileAtom s i := by
  change cavityProfileLevel s (observationCommonLevel (cavityNormalizerGraftPairTree i).tree _ _)=_
  rw [observationPair_commonLevel,cavityNormalizerGraftPairTree,
    finiteCascadeFuturePairTree_split _ _ (cavityNormalizerGraftAtomDepth_le i),
    cavityProfileLevel_normalizerGraftAtomDepth]

theorem cavityNormalizerGraftPair_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : vectorPosteriorFeatureIndex k) :
    (anisotropicFiniteRecordedTreeLaw D s a (cavityNormalizerGraftTree i)).map
      (fun z=>(observationLeafSpin (cavityNormalizerGraftTree i)
        (observationPairFirstLeaf (cavityNormalizerGraftPairTree i)) z.2,
        observationLeafSpin (cavityNormalizerGraftTree i)
          (observationPairSecondLeaf (cavityNormalizerGraftPairTree i)) z.2))=
      (anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a (vectorProfileAtom s i)).snd := by
  rw [cavityFiniteRecorded_leafPair_law D s a (cavityNormalizerGraftTree i) _ _
    (observationPair_first_ne_second _),cavityNormalizerGraftPair_commonLevel,
    anisotropicBinarySpinProbability_eq_fresh_pair]

end QuantitativeFollowup
