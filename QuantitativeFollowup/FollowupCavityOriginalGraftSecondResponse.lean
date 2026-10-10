module
public import QuantitativeFollowup.FollowupCavityChargedOriginalResponse
public import QuantitativeFollowup.FollowupCavityDominatedSixCubic
public import QuantitativeFollowup.FollowupCavityGraftCubicBudget
public import FourPapersCommon.FiniteCascadeVertexGraftLeafGeometry
public import FourPapersCommon.FiniteObservationTerminalProjection

@[expose] public section

/-! The original--fresh response splits into fixed genuine two-pair
terminal tests on the single-graft tree. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOriginalLeafGraftObservable (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (b : ObservationLeaf (trimRoot T))
    (z : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))×Configuration (n+1)) : ℝ :=
  F z.1*cavitySpinOverlapDefect n
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) b) v))
    (observationTerminalSpin (trimRoot T) b ((terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm z.1)) z.2

theorem cavityOriginalLeafGraftObservable_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (b : ObservationLeaf (trimRoot T))
    (z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)) :
    cavityOriginalLeafGraftObservable s T v F b (spins (trimRoot T) z.1.2,z.2)=
      F (spins (trimRoot T) z.1.2)*cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) b) v))
        (observationLeafSpin (trimRoot T) b z.1.2) z.2 := by
  unfold cavityOriginalLeafGraftObservable
  rw [←terminalSampleEquiv_recordSpins,
    (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm_apply_apply,
    observationTerminalSpin_record]

theorem cavityOriginalGraftPairObservable_split_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)) :
    followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)) r=
      ((observationLeaves (trimRoot T)).map (fun b=>
        followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
          (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) r)).sum := by
  rw [cavitySingleGraftSampleObservable_record]
  let z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1):=
    ((r.1,(finiteCascadeGraftRecordExtract v r.2).1),(finiteCascadeGraftRecordExtract v r.2).2)
  change cavityOriginalGraftPairObservable s T v F (spins (trimRoot T) z.1.2,z.2)=_
  rw [cavityOriginalGraftPairObservable_record,cavityOriginalVertexOverlapSum_eq_leaves,←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [cavitySingleGraftSampleObservable_record]
  exact (cavityOriginalLeafGraftObservable_record s T v F b z).symm

def cavityOriginalGraftPairLeft (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (i b : ObservationLeaf (trimRoot T)) :
    Fin 2→ObservationLeaf (finiteCascadeVertexGraft v) :=
  ![finiteCascadeVertexGraftOldLeaf v i,finiteCascadeVertexGraftOldLeaf v b]

def cavityOriginalGraftPairRight (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (l : ObservationLeaf (trimRoot T)) :
    Fin 2→ObservationLeaf (finiteCascadeVertexGraft v) :=
  ![finiteCascadeVertexGraftOldLeaf v l,finiteCascadeVertexGraftNewLeaf v]

theorem cavityOriginalLeafGraftObservable_dominated (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l b : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)) :
    |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) r| ≤ 
      |cavityRecordedPairProduct s (finiteCascadeVertexGraft v)
        (cavityOriginalGraftPairLeft T v i b) (cavityOriginalGraftPairRight T v l) r| := by
  rw [cavitySingleGraftSampleObservable_record]
  let z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1):=
    ((r.1,(finiteCascadeGraftRecordExtract v r.2).1),(finiteCascadeGraftRecordExtract v r.2).2)
  change |cavityOriginalLeafGraftObservable s T v F b (spins (trimRoot T) z.1.2,z.2)| ≤ _
  rw [cavityOriginalLeafGraftObservable_record,abs_mul]
  simp only [cavityRecordedPairProduct,cavityOriginalGraftPairLeft,cavityOriginalGraftPairRight,
    Matrix.cons_val_zero,Matrix.cons_val_one,cavityRecordedLeafPairDefect,
    finiteCascadeVertexGraftOldLeaf_commonLevel,finiteCascadeVertexGraftOldNewLeaf_commonLevel,
    finiteCascadeVertexGraftOldLeaf_spin,finiteCascadeVertexGraftNewLeaf_spin,abs_mul]
  exact mul_le_mul_of_nonneg_right (hF z.1) (abs_nonneg _)

theorem cavityOriginalLeafGraftObservable_six_cubic (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l b : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    |cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)))| ≤ 
      15*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
              (finiteCascadeVertexGraft v)) := by
  have h:=cavityMarkedSix_dominatedPair_cubic_le hn D s a ha has hq
    (.advance (finiteCascadeVertexGraft v)) (cavityOriginalGraftPairLeft T v i b)
    (cavityOriginalGraftPairRight T v l) _
    (measurable_followupCavityPhysicalRecordObservable _ _)
    (cavityOriginalLeafGraftObservable_dominated s T v F i l b hF)
  simpa only [trimRoot,asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeVertexGraft_leafCount,
    leafCount_trimRoot,Nat.cast_add,Nat.cast_one] using h

end QuantitativeFollowup
