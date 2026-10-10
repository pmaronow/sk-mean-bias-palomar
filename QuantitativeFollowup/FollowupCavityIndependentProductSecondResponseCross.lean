module
public import QuantitativeFollowup.FollowupCavityChargedCrossResponse
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseGeometry
public import QuantitativeFollowup.FollowupCavityCurrentGraftCubicBudget

@[expose] public section

/-! Genuine second streaming responses of the charged cross/current
branches retain the actual inherited and newly introduced cubic budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem product_cross_weighted_affine {A : Type*} (xs : List (ℝ×A))
    (f : A→ℝ) (P B : ℝ) :
    (xs.map (fun c=>c.1*(P*(B+f c.2)))).sum=
      P*((xs.map Prod.fst).sum*B+(xs.map (fun c=>c.1*f c.2)).sum) := by
  have he : (fun c : ℝ×A=>c.1*(P*(B+f c.2)))=
      fun c=>P*(c.1*B+c.1*f c.2) := funext (fun _=>by ring)
  rw [he,List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right]

theorem cavityIndependent_crossDerivative_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (Q : Measure X) [IsProbabilityMeasure Q] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂Q)| ≤
      followupCavityAlpha n β ρ/2*(180*(L+2)^2*L^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+(∫r,|z r|^3∂Q)) := by
  dsimp only
  let Z:=∫r,z r∂Q
  let C:=∫r,|z r|^3∂Q
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let P:=followupCavityAlpha n β ρ/2*(60*(L+2)^2)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  let G:=fun (v w : FiniteCascadeRecordVertex (trimRoot T))=>finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d))
    (finiteCascadeCrossVertexGraft v w)
  have hP : 0≤P:=by dsimp only [P]; positivity [followupCavityAlpha_nonneg n β ρ hρ.2]
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hM : 0≤M:=integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun _=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hL : 0≤L:=Nat.cast_nonneg _
  have hW0 : 0≤W:=List.sum_nonneg (by
    intro z hz
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hz
    exact anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  have hWL : W≤L:=by
    have hh : W=L-a:=by dsimp only [W,cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
    linarith [ha.1]
  have hb (v w : FiniteCascadeRecordVertex (trimRoot T)) :
      |followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeCrossVertexGraft v w))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
          (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
            (finiteCascadeCommonPathDepth (trimRoot T) v w)) F))*Z|≤P*((M+C)+G v w) := by
    rw [mul_assoc,abs_mul,abs_of_nonneg (by positivity [followupCavityAlpha_nonneg n β ρ hρ.2] : 0≤followupCavityAlpha n β ρ/2)]
    have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq
      (.advance (finiteCascadeCrossVertexGraft v w))
      (finiteCascadeCrossGraftFirstLeaf v w) (finiteCascadeCrossGraftSecondLeaf v w) _
      (measurable_followupCavityPhysicalRecordObservable _ _) (cavityIndependent_cross_onePair s T v w F hF) Q z hz hzb
    have hlc : (FiniteCascadeGenealogy.leafCount (asGenealogy (.advance (finiteCascadeCrossVertexGraft v w))):ℝ)=L+2:=by
      simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeCrossVertexGraft_leafCount,
        leafCount_trimRoot,Nat.cast_add,Nat.cast_ofNat,L]
    rw [hlc] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity [followupCavityAlpha_nonneg n β ρ hρ.2])).trans_eq (by dsimp only [P,M,G,f,C];ring)
  have hsum : |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂Q)| ≤
      (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(P*((M+C)+G c.2 d.2)))).sum)).sum := by
    unfold followupCavityCrossGraftDerivative
    rw [←List.sum_map_mul_right]
    apply abs_list_sum_le
    intro c hc
    rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    rw [←List.sum_map_mul_right]
    apply abs_list_sum_le
    intro d hd
    rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)]
    exact mul_le_mul_of_nonneg_left (hb c.2 d.2) (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)
  have he : (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(P*((M+C)+G c.2 d.2)))).sum)).sum=
      P*(W^2*(M+C)+cavityChargedCrossGraftBranchBudget s a T f) := by
    simp_rw [product_cross_weighted_affine]
    change (cs.map (fun c=>c.1*(P*(W*(M+C)+(cs.map (fun d=>d.1*G c.2 d.2)).sum)))).sum=_
    rw [product_cross_weighted_affine cs (fun v=>(cs.map (fun d=>d.1*G v d.2)).sum) P (W*(M+C))]
    change P*(W*(W*(M+C))+cavityChargedCrossGraftBranchBudget s a T f)=_
    ring
  rw [he] at hsum
  have hG:=cavityChargedCrossGraftBranchBudget_le s a ha has hq T f
    (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hWM : W^2*(M+C)≤L^2*(M+C):=mul_le_mul_of_nonneg_right ((sq_le_sq₀ hW0 hL).mpr hWL) (add_nonneg hM hC)
  apply hsum.trans
  change P*(W^2*(M+C)+cavityChargedCrossGraftBranchBudget s a T f)≤
    followupCavityAlpha n β ρ/2*(180*(L+2)^2*L^2)*(M+B+C)
  have hh : W^2*(M+C)+cavityChargedCrossGraftBranchBudget s a T f≤3*L^2*(M+B+C):=by
    change _≤L^2*(2*M+3*B) at hG
    nlinarith only [hG,hWM,mul_nonneg (sq_nonneg L) hC]
  exact (mul_le_mul_of_nonneg_left hh hP).trans_eq (by dsimp only [P];ring)

theorem cavityIndependent_currentDerivative_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),|F (spins (trimRoot T) r.2)|≤1)
    (Q : Measure X) [IsProbabilityMeasure Q] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂Q)| ≤
      followupCavityAlpha n β ρ/2*(180*(L+2)^2*L)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+(∫r,|z r|^3∂Q)) := by
  dsimp only
  let Z:=∫r,z r∂Q
  let C:=∫r,|z r|^3∂Q
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let P:=followupCavityAlpha n β ρ/2*(60*(L+2)^2)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  let G:=fun (v : FiniteCascadeRecordVertex (trimRoot T))=>
    finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft v v)
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hP : 0≤P:=by dsimp only [P]; positivity
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hM : 0≤M:=integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun _=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hL : 0≤L:=Nat.cast_nonneg _
  have hWL : W≤L:=by
    have hh : W=L-a:=by dsimp only [W,cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
    linarith [ha.1]
  have hb (v : FiniteCascadeRecordVertex (trimRoot T)) :
      |followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeCrossVertexGraft v v))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v v))
          (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F))*Z|≤P*((M+C)+G v) := by
    rw [mul_assoc,abs_mul,abs_of_nonneg (by positivity : 0≤followupCavityAlpha n β ρ/2)]
    have hdom (r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v v) (n+1)) :
        |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v v))
          (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F) r|≤
        |cavityRecordedLeafPairDefect s (finiteCascadeCrossVertexGraft v v)
          (finiteCascadeCrossGraftFirstLeaf v v) (finiteCascadeCrossGraftSecondLeaf v v) r.2|:=by
      rw [anisotropicVertexOverlap_eq_cross_self]
      exact cavityIndependent_cross_onePair s T v v F hF r
    have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq
      (.advance (finiteCascadeCrossVertexGraft v v))
      (finiteCascadeCrossGraftFirstLeaf v v) (finiteCascadeCrossGraftSecondLeaf v v) _
      (measurable_followupCavityPhysicalRecordObservable _ _) hdom Q z hz hzb
    have hlc : (FiniteCascadeGenealogy.leafCount (asGenealogy (.advance (finiteCascadeCrossVertexGraft v v))):ℝ)=L+2:=by
      simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeCrossVertexGraft_leafCount,
        leafCount_trimRoot,Nat.cast_add,Nat.cast_ofNat,L]
    rw [hlc] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by dsimp only [P,M,G,f,C];ring)
  have hsum : |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂Q)| ≤
      (cs.map (fun c=>c.1*(P*((M+C)+G c.2)))).sum := by
    unfold followupCavityCurrentGraftDerivative
    rw [←List.sum_map_mul_right]
    apply abs_list_sum_le
    intro c hc
    have hc0:=anisotropicTrimmedVertexCharges_nonneg s a has T c hc
    rw [mul_assoc,abs_mul,abs_mul,abs_of_nonneg hc0,abs_of_nonneg (Paper.parisiCDF_nonneg _ _)]
    calc
      _≤c.1*1*|followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
          (cavityCrossGraftSampleObservable T c.2 c.2 (anisotropicVertexOverlap s c.2) F))*Z| := by
            gcongr
            exact Paper.parisiCDF_le_one _ _
      _≤_ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb c.2) hc0
  rw [product_cross_weighted_affine cs G P (M+C)] at hsum
  change |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu*(∫r,z r∂Q)|≤
    P*(W*(M+C)+cavityChargedCurrentGraftBranchBudget s a T f) at hsum
  have hG:=cavityChargedCurrentGraftBranchBudget_le s a ha has hq T f
    (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hWM : W*(M+C)≤L*(M+C):=mul_le_mul_of_nonneg_right hWL (add_nonneg hM hC)
  apply hsum.trans
  change P*(W*(M+C)+cavityChargedCurrentGraftBranchBudget s a T f)≤
    followupCavityAlpha n β ρ/2*(180*(L+2)^2*L)*(M+B+C)
  have hh : W*(M+C)+cavityChargedCurrentGraftBranchBudget s a T f≤3*L*(M+B+C):=by
    change _≤L*(2*M+3*B) at hG
    nlinarith only [hG,hWM,mul_nonneg hL hC]
  exact (mul_le_mul_of_nonneg_left hh hP).trans_eq (by dsimp only [P];ring)

end QuantitativeFollowup
