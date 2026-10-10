module
public import QuantitativeFollowup.FollowupCavityOriginalGraftSecondResponse

@[expose] public section

/-! Actual closed-endpoint original--fresh second response bounds, obtained
by differentiating the finite fixed-test split and summing genuine charges. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem graft_sum_constant {A : Type*} (xs : List A) (B : ℝ) :
    (xs.map (fun _=>B)).sum=(xs.length:ℝ)*B := by
  induction xs with
  | nil=>simp
  | cons b xs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one];ring

private theorem derivative_list {A : Type*} (xs : List A)
    (f : A→ℝ→ℝ) (df : A→ℝ) (S : Set ℝ) (u : ℝ)
    (hf : ∀b,HasDerivWithinAt (f b) (df b) S u) :
    HasDerivWithinAt (fun z=>(xs.map (fun b=>f b z)).sum) (xs.map df).sum S u := by
  induction xs with
  | nil=>simpa only [List.map_nil,List.sum_nil] using hasDerivWithinAt_const u S (0:ℝ)
  | cons b xs ih=>convert! (hf b).add ih using 1 <;>simp only [List.map_cons,List.sum_cons,Pi.add_apply]

theorem followupCavityOriginalGraft_vertex_expectation_split
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)) u=
      ((observationLeaves (trimRoot T)).map (fun b=>followupCavityPhysicalExpectation n β ρ hβ hρ s a
        (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) u)).sum := by
  let U : FiniteTerminalGenealogy (k+2):=.advance (finiteCascadeVertexGraft v)
  let P : Measure (CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)):=anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a U
  letI : IsProbabilityMeasure P := anisotropicTrimmedRecordedTreeLaw_probability
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a U
  let H:=fun b=>followupCavityPhysicalRecordObservable n U
    (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))
  have hi (b : ObservationLeaf (trimRoot T)) : Integrable (H b) P := by
    apply (integrable_const (μ:=P) (4:ℝ)).mono'
      (measurable_followupCavityPhysicalRecordObservable U
        (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))).aestronglyMeasurable
    apply Eventually.of_forall
    intro r
    change ‖H b r‖ ≤ 4
    rw [Real.norm_eq_abs]
    exact (cavityOriginalLeafGraftObservable_dominated s T v F i l b hF r).trans
      (cavityRecordedPairProduct_abs_le_four s _ _ _ r)
  rw [followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq U _ u hu]
  change (∫r,followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
    (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)) r ∂P)=_
  simp_rw [cavityOriginalGraftPairObservable_split_record]
  rw [integral_list_map_sum_real P (observationLeaves (trimRoot T)) H hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact (followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq U _ u hu).symm

theorem followupCavityOriginalGraft_vertex_derivative_split (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))=
      ((observationLeaves (trimRoot T)).map (fun b=>followupCavityAlpha n β ρ/2*
        cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
          (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
            (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))))).sum := by
  dsimp only
  let f:=followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft v))
    (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F))
  let fs:=fun b=>followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft v))
    (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))
  have hs:=derivative_list (observationLeaves (trimRoot T)) fs _ (Icc (0:ℝ) 1) u
    (fun b=>hasDerivWithinAt_followupCavitySingleGraftExpectation hn β ρ hβ hρ s a ha has hq T v _ u hu)
  have he : f=ᶠ[𝓝[Icc (0:ℝ) 1] u] (fun z=>((observationLeaves (trimRoot T)).map (fun b=>fs b z)).sum) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact followupCavityOriginalGraft_vertex_expectation_split β ρ hβ hρ s a hq T v F i l hF z hz
  have hs':=hs.congr_of_eventuallyEq_of_mem he hu
  have hm:=hasDerivWithinAt_followupCavitySingleGraftExpectation hn β ρ hβ hρ s a ha has hq T v
    (cavityOriginalGraftPairObservable s T v F) u hu
  exact (hm.derivWithin (uniqueDiffOn_Icc_zero_one u hu)).symm.trans
    (hs'.derivWithin (uniqueDiffOn_Icc_zero_one u hu))

theorem followupCavityOriginalGraft_vertex_response_le (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))| ≤
      followupCavityAlpha n β ρ/2*15*L*(L+1)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
              (finiteCascadeVertexGraft v)) := by
  dsimp only
  rw [followupCavityOriginalGraft_vertex_derivative_split hn β ρ hβ hρ s a ha has hq T v F i l hF u hu]
  have hα : 0 ≤ followupCavityAlpha n β ρ/2:=div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)
  have hh:=abs_list_sum_le (observationLeaves (trimRoot T))
    (fun b=>followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))))
    (fun _=>followupCavityAlpha n β ρ/2*(15*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)^2*
      (cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum (fun d=>cavityCubicPairMoment
          (followupCavitySpinModel n β ρ hβ hρ u hu) (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
          (finiteCascadeVertexGraft v)))) (fun b _=>by
            rw [abs_mul,abs_of_nonneg hα]
            exact mul_le_mul_of_nonneg_left
              (cavityOriginalLeafGraftObservable_six_cubic hn _ s a ha has hq T v F i l b hF) hα)
  simp only [graft_sum_constant,observationLeaves_length,leafCount_trimRoot] at hh
  exact hh.trans_eq (by ring)

theorem followupCavityOriginalGraftDerivative_cubic_le (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)| ≤ |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T F u hu| ≤
      followupCavityAlpha n β ρ/2*(30*L^2*(L+1)^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let f:=fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum f (trimRoot T)
  let C:=followupCavityAlpha n β ρ/2*15*L*(L+1)^2
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hL:0 ≤ L:=by dsimp only [L];positivity
  have hC:0 ≤ C:=by dsimp only [C];exact mul_nonneg (mul_nonneg (mul_nonneg
    (div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)) (by norm_num)) hL) (sq_nonneg _)
  have hM:0 ≤ M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1
  have hB:0 ≤ B:=finiteCascadeUnweightedBranchSum_nonneg f
    (fun d=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a _).1) _
  have hW:(cs.map Prod.fst).sum=L-a:=by
    dsimp only [cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hbudget:=cavityChargedGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1)
  have hh:=abs_weighted_list_sum_le cs
    (fun v=>followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a
      (.advance (finiteCascadeVertexGraft v)) (followupCavityPhysicalRecordObservable n
        (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F))))
    (fun v=>C*(M+finiteCascadeUnweightedBranchSum f (finiteCascadeVertexGraft v)))
    (fun c hc=>anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    (fun v=>followupCavityOriginalGraft_vertex_response_le hn β ρ hβ hρ s a ha has hq T v F i l hF u hu)
  have he : (cs.map (fun c=>c.1*(C*(M+finiteCascadeUnweightedBranchSum f (finiteCascadeVertexGraft c.2))))).sum=
      C*((L-a)*M+cavityChargedGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)) := by
    have ht (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
        c.1*(C*(M+finiteCascadeUnweightedBranchSum f (finiteCascadeVertexGraft c.2)))=
        C*(c.1*M+c.1*finiteCascadeUnweightedBranchSum f (finiteCascadeVertexGraft c.2)):=by ring
    simp_rw [ht]
    rw [List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right,hW]
    rfl
  rw [he] at hh
  change |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T F u hu| ≤ _ at hh
  apply hh.trans
  have hb : (L-a)*M+cavityChargedGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) ≤
      2*L*(M+B) := by
    change cavityChargedGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) ≤ L*(M+2*B) at hbudget
    nlinarith [mul_nonneg ha.1 hM]
  exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (by dsimp only [C,L,M,B,D,f];ring)

end QuantitativeFollowup
