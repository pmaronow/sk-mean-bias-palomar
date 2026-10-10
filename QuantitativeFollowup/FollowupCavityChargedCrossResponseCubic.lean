module
public import QuantitativeFollowup.FollowupCavityChargedCrossResponse
public import QuantitativeFollowup.FollowupCavityDominatedSixCubic
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

private theorem weighted_affine_list_sum {A : Type*} (xs : List (ℝ×A))
    (f : A→ℝ) (P B : ℝ) :
    (xs.map (fun c=>c.1*(P*(B+f c.2)))).sum=
      P*((xs.map Prod.fst).sum*B+(xs.map (fun c=>c.1*f c.2)).sum) := by
  have he : (fun c : ℝ×A=>c.1*(P*(B+f c.2)))=
      fun c=>P*(c.1*B+c.1*f c.2) := funext (fun _=>by ring)
  rw [he,List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right]

theorem followupCavityCrossGraftDerivative_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (i l : (v w : FiniteCascadeRecordVertex (trimRoot T))→Fin 2→ObservationLeaf (finiteCascadeCrossVertexGraft v w))
    (hdom : ∀v w r, |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
      (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
        (finiteCascadeCommonPathDepth (trimRoot T) v w)) F) r| ≤
      |cavityRecordedPairProduct s (finiteCascadeCrossVertexGraft v w) (i v w) (l v w) r|)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu| ≤
      followupCavityAlpha n β ρ/2*(45*(L+2)^2*L^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let P:=followupCavityAlpha n β ρ/2*(15*(L+2)^2)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  let G:=fun (v w : FiniteCascadeRecordVertex (trimRoot T))=>finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d))
    (finiteCascadeCrossVertexGraft v w)
  have hP : 0≤P:=by dsimp only [P]; positivity [followupCavityAlpha_nonneg n β ρ hρ.2]
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
            (finiteCascadeCommonPathDepth (trimRoot T) v w)) F))|≤P*(M+G v w) := by
    rw [abs_mul,abs_of_nonneg (by positivity [followupCavityAlpha_nonneg n β ρ hρ.2] : 0≤followupCavityAlpha n β ρ/2)]
    have hh:=cavityMarkedSix_dominatedPair_cubic_le hn D s a ha has hq
      (.advance (finiteCascadeCrossVertexGraft v w)) (i v w) (l v w) _
      (measurable_followupCavityPhysicalRecordObservable _ _) (hdom v w)
    have hlc : (FiniteCascadeGenealogy.leafCount (asGenealogy (.advance (finiteCascadeCrossVertexGraft v w))):ℝ)=L+2:=by
      simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeCrossVertexGraft_leafCount,
        leafCount_trimRoot,Nat.cast_add,Nat.cast_ofNat,L]
    rw [hlc] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity [followupCavityAlpha_nonneg n β ρ hρ.2])).trans_eq (by dsimp only [P,M,G,f];ring)
  have hsum : |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu| ≤
      (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(P*(M+G c.2 d.2)))).sum)).sum := by
    unfold followupCavityCrossGraftDerivative
    apply abs_list_sum_le
    intro c hc
    rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    apply abs_list_sum_le
    intro d hd
    rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)]
    exact mul_le_mul_of_nonneg_left (hb c.2 d.2) (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)
  have he : (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(P*(M+G c.2 d.2)))).sum)).sum=
      P*(W^2*M+cavityChargedCrossGraftBranchBudget s a T f) := by
    simp_rw [weighted_affine_list_sum]
    change (cs.map (fun c=>c.1*(P*(W*M+(cs.map (fun d=>d.1*G c.2 d.2)).sum)))).sum=_
    rw [weighted_affine_list_sum cs (fun v=>(cs.map (fun d=>d.1*G v d.2)).sum) P (W*M)]
    change P*(W*(W*M)+cavityChargedCrossGraftBranchBudget s a T f)=_
    ring
  rw [he] at hsum
  have hG:=cavityChargedCrossGraftBranchBudget_le s a ha has hq T f
    (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hWM : W^2*M≤L^2*M:=mul_le_mul_of_nonneg_right ((sq_le_sq₀ hW0 hL).mpr hWL) hM
  apply hsum.trans
  change P*(W^2*M+cavityChargedCrossGraftBranchBudget s a T f)≤
    followupCavityAlpha n β ρ/2*(45*(L+2)^2*L^2)*(M+B)
  have hh : W^2*M+cavityChargedCrossGraftBranchBudget s a T f≤3*L^2*(M+B):=by
    change _≤L^2*(2*M+3*B) at hG
    nlinarith only [hG,hWM]
  exact (mul_le_mul_of_nonneg_left hh hP).trans_eq (by dsimp only [P];ring)

theorem followupCavityCurrentGraftDerivative_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (i l : (v : FiniteCascadeRecordVertex (trimRoot T))→Fin 2→ObservationLeaf (finiteCascadeCrossVertexGraft v v))
    (hdom : ∀v r, |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v v))
      (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F) r| ≤
      |cavityRecordedPairProduct s (finiteCascadeCrossVertexGraft v v) (i v) (l v) r|)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu| ≤
      followupCavityAlpha n β ρ/2*(45*(L+2)^2*L)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let P:=followupCavityAlpha n β ρ/2*(15*(L+2)^2)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  let G:=fun (v : FiniteCascadeRecordVertex (trimRoot T))=>
    finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft v v)
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hP : 0≤P:=by dsimp only [P]; positivity
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
          (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F))|≤P*(M+G v) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤followupCavityAlpha n β ρ/2)]
    have hh:=cavityMarkedSix_dominatedPair_cubic_le hn D s a ha has hq
      (.advance (finiteCascadeCrossVertexGraft v v)) (i v) (l v) _
      (measurable_followupCavityPhysicalRecordObservable _ _) (hdom v)
    have hlc : (FiniteCascadeGenealogy.leafCount (asGenealogy (.advance (finiteCascadeCrossVertexGraft v v))):ℝ)=L+2:=by
      simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeCrossVertexGraft_leafCount,
        leafCount_trimRoot,Nat.cast_add,Nat.cast_ofNat,L]
    rw [hlc] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by dsimp only [P,M,G,f];ring)
  have hsum : |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu| ≤
      (cs.map (fun c=>c.1*(P*(M+G c.2)))).sum := by
    unfold followupCavityCurrentGraftDerivative
    apply abs_list_sum_le
    intro c hc
    have hc0:=anisotropicTrimmedVertexCharges_nonneg s a has T c hc
    rw [abs_mul,abs_mul,abs_of_nonneg hc0,abs_of_nonneg (Paper.parisiCDF_nonneg _ _)]
    calc
      _≤c.1*1*|followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
          (cavityCrossGraftSampleObservable T c.2 c.2 (anisotropicVertexOverlap s c.2) F))| := by
            gcongr
            exact Paper.parisiCDF_le_one _ _
      _≤_ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb c.2) hc0
  rw [weighted_affine_list_sum] at hsum
  change |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu|≤
    P*(W*M+cavityChargedCurrentGraftBranchBudget s a T f) at hsum
  have hG:=cavityChargedCurrentGraftBranchBudget_le s a ha has hq T f
    (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hWM : W*M≤L*M:=mul_le_mul_of_nonneg_right hWL hM
  apply hsum.trans
  change P*(W*M+cavityChargedCurrentGraftBranchBudget s a T f)≤
    followupCavityAlpha n β ρ/2*(45*(L+2)^2*L)*(M+B)
  have hh : W*M+cavityChargedCurrentGraftBranchBudget s a T f≤3*L*(M+B):=by
    change _≤L*(2*M+3*B) at hG
    nlinarith only [hG,hWM]
  exact (mul_le_mul_of_nonneg_left hh hP).trans_eq (by dsimp only [P];ring)

end QuantitativeFollowup
