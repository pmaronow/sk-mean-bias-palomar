module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseGeometry

@[expose] public section

/-! Original--fresh insertions split into genuine leaf pairs before
multiplication by the external independent defect mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem independent_original_sum_constant {A : Type*} (xs : List A) (C : ℝ) :
    (xs.map (fun _=>C)).sum=(xs.length:ℝ)*C := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one];ring

theorem cavityIndependent_originalVertex_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))*(∫r,z r∂P)|≤
      60*L*(L+1)^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)+
        (∫r,|z r|^3∂P)) := by
  dsimp only
  rw [cavityIndependent_originalGraft_vertex_six_split hn D s a ha.1 has hq T v F,←List.sum_map_mul_right]
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let C:=60*(L+1)^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)+
    (∫r,|z r|^3∂P))
  have hb (b : ObservationLeaf (trimRoot T)) :
      |cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
          (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)))*(∫r,z r∂P)|≤C := by
    have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq
      (.advance (finiteCascadeVertexGraft v))
      (finiteCascadeVertexGraftOldLeaf v b) (finiteCascadeVertexGraftNewLeaf v) _
      (measurable_followupCavityPhysicalRecordObservable _ _) (cavityIndependent_originalLeaf_onePair s T v F b hF)
      P z hz hzb
    simpa only [trimRoot,asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeVertexGraft_leafCount,
      leafCount_trimRoot,Nat.cast_add,Nat.cast_one,L,C] using hh
  have hh:=abs_list_sum_le (observationLeaves (trimRoot T)) _ (fun _=>C) (fun b _=>hb b)
  simp only [independent_original_sum_constant,observationLeaves_length,leafCount_trimRoot] at hh
  exact hh.trans_eq (by dsimp only [L,C];ring)

theorem cavityIndependent_originalDerivative_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂P)|≤
      followupCavityAlpha n β ρ/2*(120*L^2*(L+1)^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          (∫r,|z r|^3∂P)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let C:=∫r,|z r|^3∂P
  let Z:=∫r,z r∂P
  let H:=followupCavityAlpha n β ρ/2
  let K:=H*60*L*(L+1)^2
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hH : 0≤H:=div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)
  have hL : 0≤L:=Nat.cast_nonneg _
  have hK : 0≤K:=by dsimp only [K];positivity
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hW : (cs.map Prod.fst).sum=L-a:=by dsimp only [cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
      |H*cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
          (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))*Z|≤
        K*((M+C)+finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)) := by
    rw [mul_assoc,abs_mul,abs_of_nonneg hH]
    have hh:=cavityIndependent_originalVertex_external_cubic_le hn D s a ha has hq T v F hF P z hz hzb
    exact (mul_le_mul_of_nonneg_left hh hH).trans_eq (by dsimp only [K,M,C,f,L];ring)
  have hh : |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T F u hu*Z|≤
      (cs.map (fun c=>c.1*(K*((M+C)+finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2))))).sum := by
    unfold followupCavityOriginalGraftDerivative
    rw [←List.sum_map_mul_right]
    apply abs_list_sum_le;intro c hc
    rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
    exact mul_le_mul_of_nonneg_left (hv c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  have he : (cs.map (fun c=>c.1*(K*((M+C)+finiteCascadeUnweightedBranchSum
      (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2))))).sum=
      K*((L-a)*(M+C)+cavityChargedGraftBranchBudget s a T f) := by
    have ht (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
      c.1*(K*((M+C)+finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)))=
      K*(c.1*(M+C)+c.1*finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)):=by ring
    simp_rw [ht]
    rw [List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right,hW]
    rfl
  rw [he] at hh
  have hg:=cavityChargedGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hb : (L-a)*(M+C)+cavityChargedGraftBranchBudget s a T f≤2*L*(M+B+C) := by
    change _≤L*(M+2*B) at hg
    nlinarith only [hg,mul_nonneg ha.1 (add_nonneg hM hC),mul_nonneg hL (add_nonneg hM hC),mul_nonneg hL hC]
  exact hh.trans ((mul_le_mul_of_nonneg_left hb hK).trans_eq (by dsimp only [K,H];ring))

end QuantitativeFollowup
