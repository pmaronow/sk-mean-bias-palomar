module
public import QuantitativeFollowup.FollowupCavityFutureGraftResponseCharged
public import QuantitativeFollowup.FollowupCavityDominatedSixCubic

@[expose] public section

/-! The old defect and the strict-future defect are actual leaf pairs of
the enlarged genealogy. A bounded terminal prefactor is retained literally. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFutureSecondPairFirst (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (p : ℕ)
    (i : ObservationLeaf (trimRoot T)) :
    Fin 2 → ObservationLeaf (finiteCascadeFutureVertexGraft v p) :=
  ![finiteCascadeContinuationOldLeaf (fun d => (finiteCascadeFuturePairTree p d).tree) v i,
    finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree p d).tree) v
      (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth))]

def cavityFutureSecondPairLast (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (p : ℕ)
    (l : ObservationLeaf (trimRoot T)) :
    Fin 2 → ObservationLeaf (finiteCascadeFutureVertexGraft v p) :=
  ![finiteCascadeContinuationOldLeaf (fun d => (finiteCascadeFuturePairTree p d).tree) v l,
    finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree p d).tree) v
      (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth))]

theorem cavityFutureSecondPairProduct_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (p : ℕ) (hp : p ≤ v.depth) (i l : ObservationLeaf (trimRoot T))
    (r : CavityPathRecordSpace (finiteCascadeFutureVertexGraft v p) (n+1)) :
    cavityRecordedPairProduct s (finiteCascadeFutureVertexGraft v p)
      (cavityFutureSecondPairFirst T v p i) (cavityFutureSecondPairLast T v p l) r =
      cavityRecordedLeafPairDefect s (trimRoot T) i l
        (finiteCascadeFutureGraftExtract v p r.2).1 *
      cavitySpinOverlapDefect n (cavityProfileLevel s p)
        (finiteCascadeFutureGraftExtract v p r.2).2.1
        (finiteCascadeFutureGraftExtract v p r.2).2.2 := by
  simp only [cavityRecordedPairProduct,cavityFutureSecondPairFirst,cavityFutureSecondPairLast,
    Matrix.cons_val_zero,Matrix.cons_val_one,cavityRecordedLeafPairDefect,
    finiteCascadeContinuationOldLeaf_commonLevel,finiteCascadeContinuationOldLeaf_spin,
    finiteCascadeContinuationNewLeaf_commonLevel,finiteCascadeContinuationNewLeaf_spin,
    observationPair_commonLevel,finiteCascadeFuturePairTree_split p v.depth hp,
    finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records,
    observationPair_spins_eq_leaf_pair]

theorem cavityFutureGraftSecondResponse_dominatedPair (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (i l : ObservationLeaf (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)| ≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (hlevel : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth q)=q)
    (r : CavityPathRecordSpace
      (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)) (n+1)) :
    |cavityFutureGraftResponseTerminalObservable T v (cavityFiniteFutureDepth s v.depth q) q F
      (finiteCascadeRecordTerminalSpins _ r.2)| ≤
      |cavityRecordedPairProduct s
        (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
        (cavityFutureSecondPairFirst T v (cavityFiniteFutureDepth s v.depth q) i)
        (cavityFutureSecondPairLast T v (cavityFiniteFutureDepth s v.depth q) l) r| := by
  rw [cavityFutureSecondPairProduct_record s T v _ (cavityFiniteFutureDepth_le s v.depth q),hlevel]
  simp only [cavityFutureGraftResponseTerminalObservable,cavityFutureGraftTerminalExtract_record,
    abs_mul]
  exact mul_le_mul_of_nonneg_right
    (hF (r.1,(finiteCascadeFutureGraftExtract v (cavityFiniteFutureDepth s v.depth q) r.2).1))
    (abs_nonneg _)

theorem cavityFutureGraftSecondResponse_profile_atom_dominatedPair (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (z : vectorPosteriorFeatureIndex k)
    (hz : anisotropicVertexOverlap s v < vectorProfileAtom s z)
    (i l : ObservationLeaf (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)| ≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    ∀r, |cavityFutureGraftResponseTerminalObservable T v
      (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)) (vectorProfileAtom s z) F
      (finiteCascadeRecordTerminalSpins _ r.2)| ≤
      |cavityRecordedPairProduct s
        (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)))
        (cavityFutureSecondPairFirst T v (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)) i)
        (cavityFutureSecondPairLast T v (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)) l) r| := by
  apply cavityFutureGraftSecondResponse_dominatedPair s T v _ i l F hF
  exact cavityFiniteFutureDepth_level_profile_atom s v.depth (v.depth_le.trans (by omega)) z hz

end QuantitativeFollowup
