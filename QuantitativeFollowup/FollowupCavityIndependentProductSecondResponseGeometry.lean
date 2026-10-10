module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseLinearity
public import QuantitativeFollowup.FollowupCavityOriginalOriginalSecondResponseCubic
public import QuantitativeFollowup.FollowupCavityFutureGraftSecondResponseGeometry
public import QuantitativeFollowup.FollowupCavityCrossPairDomination
public import QuantitativeFollowup.FollowupCavitySixthSecondResponseCubicMarked

@[expose] public section

/-! With a bounded old prefactor, every first insertion is one genuine
leaf pair of the enlarged tree. An independent external pair is retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem product_sum_constant {A : Type*} (xs : List A) (C : ℝ) :
    (xs.map (fun _=>C)).sum=(xs.length:ℝ)*C := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one];ring

theorem cavityIndependent_originalLeaf_onePair (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (b : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)) :
    |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) r|≤
      |cavityRecordedLeafPairDefect s (finiteCascadeVertexGraft v)
        (finiteCascadeVertexGraftOldLeaf v b) (finiteCascadeVertexGraftNewLeaf v) r.2| := by
  rw [cavitySingleGraftSampleObservable_record]
  let z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1):=
    ((r.1,(finiteCascadeGraftRecordExtract v r.2).1),(finiteCascadeGraftRecordExtract v r.2).2)
  change |cavityOriginalLeafGraftObservable s T v F b (spins (trimRoot T) z.1.2,z.2)|≤_
  rw [cavityOriginalLeafGraftObservable_record,abs_mul]
  simp only [cavityRecordedLeafPairDefect,finiteCascadeVertexGraftOldNewLeaf_commonLevel,
    finiteCascadeVertexGraftOldLeaf_spin,finiteCascadeVertexGraftNewLeaf_spin]
  exact (mul_le_mul_of_nonneg_right (hF z.1) (abs_nonneg _)).trans_eq (one_mul _)

theorem cavityIndependent_cross_onePair (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)) :
    |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
      (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
        (finiteCascadeCommonPathDepth (trimRoot T) v w)) F) r|≤
      |cavityRecordedLeafPairDefect s (finiteCascadeCrossVertexGraft v w)
        (finiteCascadeCrossGraftFirstLeaf v w) (finiteCascadeCrossGraftSecondLeaf v w) r.2| := by
  rw [cavityCrossGraftSampleObservable_record,abs_mul]
  simp only [cavityRecordedLeafPairDefect,finiteCascadeCrossGraftFresh_commonLevel,
    finiteCascadeCrossGraftFirstLeaf_spin,finiteCascadeCrossGraftSecondLeaf_spin]
  exact (mul_le_mul_of_nonneg_right (hF (r.1,(finiteCascadeCrossGraftExtract v w r.2).1))
    (abs_nonneg _)).trans_eq (one_mul _)

theorem cavityIndependent_future_onePair (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap)
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤1)
    (hlevel : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth q)=q)
    (r : CavityPathRecordSpace (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)) (n+1)) :
    |cavityFutureGraftResponseTerminalObservable T v (cavityFiniteFutureDepth s v.depth q) q F
      (finiteCascadeRecordTerminalSpins _ r.2)|≤
      |cavityRecordedLeafPairDefect s
        (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
        (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree
          (cavityFiniteFutureDepth s v.depth q) d).tree) v
          (observationPairFirstLeaf (finiteCascadeFuturePairTree (cavityFiniteFutureDepth s v.depth q) v.depth)))
        (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree
          (cavityFiniteFutureDepth s v.depth q) d).tree) v
          (observationPairSecondLeaf (finiteCascadeFuturePairTree (cavityFiniteFutureDepth s v.depth q) v.depth))) r.2| := by
  simp only [cavityRecordedLeafPairDefect,finiteCascadeContinuationNewLeaf_commonLevel,
    finiteCascadeContinuationNewLeaf_spin,observationPair_commonLevel,
    finiteCascadeFuturePairTree_split _ _ (cavityFiniteFutureDepth_le s v.depth q),hlevel,
    observationPair_spins_eq_leaf_pair,cavityFutureGraftResponseTerminalObservable,
    cavityFutureGraftTerminalExtract_record,abs_mul]
  simpa only [one_mul,finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records,observationPair_spins_eq_leaf_pair] using
    mul_le_mul_of_nonneg_right
      (hF (r.1,(finiteCascadeFutureGraftExtract v (cavityFiniteFutureDepth s v.depth q) r.2).1)) (abs_nonneg _)

theorem cavityIndependent_originalOriginal_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤1)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2) :
    |cavityMarkedSixExpectation D s a T
      (fun r=>F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*cavityOriginalDistinctLeafDefect n s T r)*(∫r,z r∂P)|≤
      60*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^4*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          (∫r,|z r|^3∂P)) := by
  rw [cavityOriginalOriginalSecondResponse_six_split hn D s a ha.1 has hq T F]
  simp_rw [←List.sum_map_mul_right]
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let C:=60*L^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
    (∫r,|z r|^3∂P))
  have hb (j h : ObservationLeaf (trimRoot T)) :
      |cavityMarkedSixExpectation D s a T
        (fun r=>cavityOriginalOriginalSecondLeafTest s T F j h
          (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))*(∫r,z r∂P)|≤C := by
    apply cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq T j h _
      ((measurable_of_finite (cavityOriginalOriginalSecondLeafTest s T F j h)).comp
        ((measurable_finiteCascadeRecordTerminalSpins (trimRoot T)).comp measurable_snd)) _ P z hz hzb
    intro r
    dsimp only [Function.comp_def]
    rw [cavityOriginalOriginalSecondLeafTest_record,abs_mul]
    exact (mul_le_mul_of_nonneg_right (hF r) (abs_nonneg _)).trans_eq (one_mul _)
  have hh := abs_list_sum_le (observationLeaves (trimRoot T)) _
    (fun _=>(observationLeaves (trimRoot T)).length*C)
    (fun j _=>by
      have hj:=abs_list_sum_le (observationLeaves (trimRoot T)) _ (fun _=>C) (fun h _=>hb j h)
      simpa only [product_sum_constant] using hj)
  simp only [product_sum_constant,observationLeaves_length,leafCount_trimRoot] at hh
  exact hh.trans_eq (by dsimp only [L,C];ring)

end QuantitativeFollowup
