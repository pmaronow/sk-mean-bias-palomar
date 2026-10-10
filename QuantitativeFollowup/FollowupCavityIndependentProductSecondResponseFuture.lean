module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseGeometry
public import QuantitativeFollowup.FollowupCavityFutureGraftCubicBudget

@[expose] public section

/-! The actual strict-future second streaming response has a cubic
budget uniform in the scheme depth. Free Stieltjes atoms, vertex charges,
and the two added ancestral levels are all retained in the proof. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem product_future_weighted_sum {A : Type*} (xs : List (ℝ×A))
    (g : A→ℝ) (K M : ℝ) :
    (xs.map (fun c=>c.1*(K*(M+g c.2)))).sum =
      K*((xs.map Prod.fst).sum*M+(xs.map (fun c=>c.1*g c.2)).sum) := by
  have he : (fun c : ℝ×A=>c.1*(K*(M+g c.2)))=
      fun c=>K*(c.1*M+c.1*g c.2) := funext fun c=>by ring
  rw [he,List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right]

theorem cavityIndependent_futureResponse_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)| ≤1)
    (Q : Measure X) [IsProbabilityMeasure Q] (zfun : X→ℝ) (hz0 : Measurable zfun) (hzb : ∀r,|zfun r|≤2) :
    let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityFutureGraftStreamingResponse D s a T F*(∫r,zfun r∂Q)| ≤
      180*(L+2)^2*L*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
          (trimRoot T)+(∫r,|zfun r|^3∂Q)) := by
  classical
  dsimp only
  let Z:=∫r,zfun r∂Q
  let C:=∫r,|zfun r|^3∂Q
  let ν := parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let f := cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let M := cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B := finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let K := 60*(L+2)^2
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W := (cs.map Prod.fst).sum
  let G := fun (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap) =>
    finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d))
      (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
  let H := fun v => ∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then G v q else 0∂ν
  have hK : 0≤K := by dsimp only [K]; positivity
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hM : 0≤M := integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hB : 0≤B := finiteCascadeUnweightedBranchSum_nonneg _
    (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hi (g : Paper.Overlap→ℝ) : Integrable g ν := by
    dsimp only [ν]
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hm : ν.real univ=1-a := by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hW : W=L-a := by
    dsimp only [W,cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hWL : W≤L := by rw [hW];linarith [ha.1]
  have hb (v : FiniteCascadeRecordVertex (trimRoot T)) :
      |followupCavityFutureGraftStieltjesResponse D s a T v F*Z| ≤ K*((M+C)+H v) := by
    let R := fun q : Paper.Overlap => if anisotropicVertexOverlap s v<q then
      cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)))
        (fun r=>cavityFutureGraftResponseTerminalObservable T v (cavityFiniteFutureDepth s v.depth q)
          q F (finiteCascadeRecordTerminalSpins _ r.2)) else 0
    have he : followupCavityFutureGraftStieltjesResponse D s a T v F=∫q,R q∂ν := by
      dsimp only [ν]
      rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq,
        integral_vectorProfileFreeMeasure s a has]
      rfl
    rw [he,←integral_mul_const]
    have hbound : (∫q,|R q*Z|∂ν)≤∫q,K*((M+C)+(if cavityProfileLevel s v.depth<q then G v q else 0))∂ν := by
      apply integral_mono_ae (hi _) (hi _)
      filter_upwards [ae_parisiFreeMeasure_profile_atom s a ha.1 has hq] with q hqatom
      obtain ⟨z,rfl⟩ := hqatom
      by_cases hz : anisotropicVertexOverlap s v<vectorProfileAtom s z
      · dsimp only [R]
        rw [if_pos hz,if_pos (show cavityProfileLevel s v.depth<vectorProfileAtom s z from hz)]
        let p:=cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)
        have hlev:=cavityFiniteFutureDepth_level_profile_atom s v.depth (v.depth_le.trans (by omega)) z hz
        have hh := cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq
          (.advance (finiteCascadeFutureVertexGraft v p))
          (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree p d).tree) v
            (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth)))
          (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree p d).tree) v
            (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth)))
          (fun r=>cavityFutureGraftResponseTerminalObservable T v p (vectorProfileAtom s z) F
            (finiteCascadeRecordTerminalSpins _ r.2))
          ((measurable_of_finite (cavityFutureGraftResponseTerminalObservable T v p (vectorProfileAtom s z) F)).comp
            ((measurable_finiteCascadeRecordTerminalSpins (finiteCascadeFutureVertexGraft v p)).comp measurable_snd))
          (cavityIndependent_future_onePair s T v (vectorProfileAtom s z) F hF hlev) Q zfun hz0 hzb
        have hlc : (FiniteCascadeGenealogy.leafCount (asGenealogy
            (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z))))):ℝ)=L+2 := by
          simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeFutureVertexGraft_leafCount,
            leafCount_trimRoot,Nat.cast_add,Nat.cast_ofNat,L]
        change |cavityMarkedSixExpectation D s a (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s z)))) _*Z|≤_ at hh
        rw [hlc] at hh
        exact hh.trans_eq (by dsimp only [K,M,C,G,f,p];ring)
      · dsimp only [R]
        rw [if_neg hz,if_neg (show ¬cavityProfileLevel s v.depth<vectorProfileAtom s z from hz),zero_mul,abs_zero]
        positivity
    have heint : (∫q,K*((M+C)+(if cavityProfileLevel s v.depth<q then G v q else 0))∂ν)=
        K*((1-a)*(M+C)+H v) := by
      rw [integral_const_mul,integral_add (hi _) (hi _),integral_const,hm]
      rfl
    rw [heint] at hbound
    exact abs_integral_le_integral_abs.trans (hbound.trans
      (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg ha.1 (add_nonneg hM hC)]) hK))
  have hsum : |followupCavityFutureGraftStreamingResponse D s a T F*(∫r,zfun r∂Q)|≤
      (cs.map (fun c=>c.1*(K*((M+C)+H c.2)))).sum := by
    unfold followupCavityFutureGraftStreamingResponse
    rw [←List.sum_map_mul_right]
    apply abs_list_sum_le
    intro c hc
    rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
    exact mul_le_mul_of_nonneg_left (hb c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  rw [product_future_weighted_sum cs H K (M+C)] at hsum
  change |followupCavityFutureGraftStreamingResponse D s a T F*(∫r,zfun r∂Q)|≤
    K*(W*(M+C)+cavityChargedFutureGraftBranchBudget s a T f) at hsum
  have hG := cavityChargedFutureGraftBranchBudget_le s a ha has hq T f
    (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
  have hWM : W*(M+C)≤L*(M+C) := mul_le_mul_of_nonneg_right hWL (add_nonneg hM hC)
  have hg : W*(M+C)+cavityChargedFutureGraftBranchBudget s a T f≤3*L*(M+B+C) := by
    change _≤2*L*(M+B) at hG
    nlinarith only [hG,hWM,mul_nonneg (show (0:ℝ)≤L by dsimp only [L]; positivity) hB,mul_nonneg (show (0:ℝ)≤L by dsimp only [L];positivity) hC]
  exact hsum.trans ((mul_le_mul_of_nonneg_left hg hK).trans_eq (by dsimp only [K];ring))

end QuantitativeFollowup
