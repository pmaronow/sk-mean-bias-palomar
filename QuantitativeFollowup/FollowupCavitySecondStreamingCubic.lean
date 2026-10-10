module
public import QuantitativeFollowup.FollowupCavitySecondStreaming
public import QuantitativeFollowup.FollowupCavityCrossPairDomination
public import QuantitativeFollowup.FollowupCavityOriginalGraftSecondResponseBound
public import QuantitativeFollowup.FollowupCavityOriginalOriginalSecondResponseCubic
public import QuantitativeFollowup.FollowupCavityFutureGraftSecondResponseBound
public import QuantitativeFollowup.FollowupCavitySixthSecondResponseCubicBound

@[expose] public section

/-! The complete genuine second streaming response retains cubic order.
The test is dominated by one actual old terminal overlap defect. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavitySecondStreamingCost (L : ℝ) : ℝ :=
  15*L^4+60*L^2*(L+1)^2+45*(L+2)^2*L^2+90*(L+2)^2*L+600*L^2

theorem cavitySecondStreamingCost_nonneg (L : ℝ) (hL : 0≤L) :
    0≤cavitySecondStreamingCost L := by unfold cavitySecondStreamingCost; positivity

theorem followupCavitySecondStreamingResponse_singlePair_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |followupCavityPhysicalRecordObservable n T F r|≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavitySecondStreamingResponse n β ρ hβ hρ s a T F u hu|≤
      followupCavityAlpha n β ρ/2*cavitySecondStreamingCost L*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let B:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let H:=followupCavityAlpha n β ρ/2
  have hH : 0≤H:=div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)
  have hL : 0≤L:=Nat.cast_nonneg _
  have hB : 0≤B:=add_nonneg (integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D _ a q).1))
    (finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _)
  have hFt (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
      |cavityFullTestToTrim T F (spins (trimRoot T) r.2)|≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|:=hF r
  have hFterm (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
      |cavityFullTestToTerminal T F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|:=by
    rw [cavityFullTestToTerminal_record];exact hF r
  have hOO : |H*cavityMarkedSixExpectation D s a T
      (fun r=>followupCavityPhysicalRecordObservable n T F r*cavityOriginalDistinctLeafDefect n s T r)|≤
      H*(15*L^4)*B := by
    rw [abs_mul,abs_of_nonneg hH]
    have hh:=cavityOriginalOriginalSecondResponse_six_cubic_le hn D s a ha has hq T i l
      (cavityFullTestToTerminal T F) hFterm
    simp only [cavityFullTestToTerminal_record] at hh
    exact (mul_le_mul_of_nonneg_left hh hH).trans_eq (by ring)
  have hOF:=followupCavityOriginalGraftDerivative_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) i l hFt u hu
  have hFF:=followupCavityCrossGraftDerivative_singlePair_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) i l hFt u hu
  have hCF:=followupCavityCurrentGraftDerivative_singlePair_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) i l hFt u hu
  have hFU:=followupCavityFutureGraftSecondDerivative_cubic_le hn β ρ hβ hρ s a ha has hq T i l
    (cavityFullTestToTerminal T F) hFterm u hu
  have hR:=cavitySixth_second_response_cubic_le hn D s a ha has hq T i l
    (followupCavityPhysicalRecordObservable n T F)
    (measurable_followupCavityPhysicalRecordObservable T F) hF
  change |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu|≤
    H*(30*L^2*(L+1)^2)*B at hOF
  change |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu|≤
    H*(45*(L+2)^2*L^2)*B at hFF
  change |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu|≤
    H*(45*(L+2)^2*L)*B at hCF
  change |H*followupCavityFutureGraftStreamingResponse D s a T (cavityFullTestToTerminal T F)|≤
    H*(45*(L+2)^2*L)*B at hFU
  change |cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
        cavityNormalizerGraftStreamingResponse D s a|≤600*L^2*B at hR
  have hR' : |a*H*(cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
        cavityNormalizerGraftStreamingResponse D s a)|≤H*(600*L^2)*B := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg ha.1 hH)]
    apply (mul_le_mul_of_nonneg_left hR (mul_nonneg ha.1 hH)).trans
    have h0 : 0≤H*(600*L^2)*B:=by positivity
    calc
      _=a*(H*(600*L^2)*B):=by ring
      _≤1*(H*(600*L^2)*B):=mul_le_mul_of_nonneg_right ha.2 h0
      _=_:=one_mul _
  let x:=H*cavityMarkedSixExpectation D s a T
    (fun r=>followupCavityPhysicalRecordObservable n T F r*cavityOriginalDistinctLeafDefect n s T r)
  let y:=followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu
  let z:=followupCavityCrossGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu
  let w:=followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu
  let v:=H*followupCavityFutureGraftStreamingResponse D s a T (cavityFullTestToTerminal T F)
  let r:=a*H*(cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
    cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
    (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      cavityNormalizerGraftStreamingResponse D s a)
  have htriangle : |x-2*y+z+w+v+r|≤|x|+2*|y|+|z|+|w|+|v|+|r|:=by
    calc
      _≤|x-2*y+z+w+v|+|r|:=abs_add_le _ _
      _≤(|x-2*y+z+w|+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤((|x-2*y+z|+|w|)+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤(((|x-2*y|+|z|)+|w|)+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤((((|x|+|2*y|)+|z|)+|w|)+|v|)+|r|:=by gcongr;exact abs_sub _ _
      _=_:=by simp only [abs_mul,show |(2:ℝ)|=2 by norm_num]
  change |x-2*y+z+w+v+r|≤H*cavitySecondStreamingCost L*B
  apply htriangle.trans
  have hs:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hOO
    (mul_le_mul_of_nonneg_left hOF (by norm_num : (0:ℝ)≤2))) hFF) hCF) hFU) hR'
  exact hs.trans_eq (by unfold cavitySecondStreamingCost;ring)

theorem abs_followupCavityPhysicalExpectation_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |followupCavityPhysicalRecordObservable n T F r|≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |derivWithin (derivWithin (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1))
        (Icc (0:ℝ) 1) u|≤
      (followupCavityAlpha n β ρ/2)^2*cavitySecondStreamingCost L*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  rw [(hasDerivWithinAt_followupCavityPhysicalExpectation_derivWithin hn β ρ hβ hρ s a ha has hq T F u hu).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu),abs_mul,
    abs_of_nonneg (div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num))]
  exact (mul_le_mul_of_nonneg_left
    (followupCavitySecondStreamingResponse_singlePair_cubic_le hn β ρ hβ hρ s a ha has hq T F i l hF u hu)
    (div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num))).trans_eq (by ring)

end QuantitativeFollowup
