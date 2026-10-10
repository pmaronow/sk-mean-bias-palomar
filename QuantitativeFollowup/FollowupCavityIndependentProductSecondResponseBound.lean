module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseOriginal
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseCross
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseFuture
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseSixth

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

def cavityIndependentSecondStreamingCost (L : ℝ) : ℝ :=
  60*L^4+240*L^2*(L+1)^2+180*(L+2)^2*L^2+360*(L+2)^2*L+510*L^2

theorem cavityIndependentSecondStreamingCost_nonneg (L : ℝ) (hL : 0≤L) :
    0≤cavityIndependentSecondStreamingCost L := by unfold cavityIndependentSecondStreamingCost; positivity

theorem followupCavitySecondStreamingResponse_bounded_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |followupCavityPhysicalRecordObservable n T F r|≤1)
    (Q : Measure X) [IsProbabilityMeasure Q] (zfun : X→ℝ)
    (hz : Measurable zfun) (hzb : ∀r,|zfun r|≤2)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavitySecondStreamingResponse n β ρ hβ hρ s a T F u hu*(∫r,zfun r∂Q)|≤
      followupCavityAlpha n β ρ/2*cavityIndependentSecondStreamingCost L*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+(∫r,|zfun r|^3∂Q)) := by
  dsimp only
  let Z:=∫r,zfun r∂Q
  let C:=∫r,|zfun r|^3∂Q
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let B:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+C
  let H:=followupCavityAlpha n β ρ/2
  have hH : 0≤H:=div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)
  have hL : 0≤L:=Nat.cast_nonneg _
  have hB : 0≤B:=add_nonneg (add_nonneg (integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D _ a q).1))
    (finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _))
    (integral_nonneg fun _=>by positivity)
  have hFt (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
      |cavityFullTestToTrim T F (spins (trimRoot T) r.2)|≤1:=hF r
  have hFterm (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
      |cavityFullTestToTerminal T F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤1:=by
    rw [cavityFullTestToTerminal_record];exact hF r
  have hOO : |H*cavityMarkedSixExpectation D s a T
      (fun r=>followupCavityPhysicalRecordObservable n T F r*cavityOriginalDistinctLeafDefect n s T r)*Z|≤
      H*(60*L^4)*B := by
    rw [mul_assoc,abs_mul,abs_of_nonneg hH]
    have hh:=cavityIndependent_originalOriginal_external_cubic_le hn D s a ha has hq T
      (cavityFullTestToTerminal T F) hFterm Q zfun hz hzb
    simp only [cavityFullTestToTerminal_record] at hh
    exact (mul_le_mul_of_nonneg_left hh hH).trans_eq (by ring)
  have hOF:=cavityIndependent_originalDerivative_external_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) hFt Q zfun hz hzb u hu
  have hFF:=cavityIndependent_crossDerivative_external_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) hFt Q zfun hz hzb u hu
  have hCF:=cavityIndependent_currentDerivative_external_cubic_le hn β ρ hβ hρ s a ha has hq T
    (cavityFullTestToTrim T F) hFt Q zfun hz hzb u hu
  have hFU0:=cavityIndependent_futureResponse_external_cubic_le hn D s a ha has hq T
    (cavityFullTestToTerminal T F) hFterm Q zfun hz hzb
  have hFU : |H*followupCavityFutureGraftStreamingResponse D s a T (cavityFullTestToTerminal T F)*Z|≤
      H*(180*(L+2)^2*L)*B:=by
    rw [mul_assoc,abs_mul,abs_of_nonneg hH]
    exact (mul_le_mul_of_nonneg_left hFU0 hH).trans_eq (by dsimp only [H,B,C];ring)
  have hR:=cavityIndependent_sixth_bounded_external_cubic_le hn D s a ha has hq T
    (followupCavityPhysicalRecordObservable n T F)
    (measurable_followupCavityPhysicalRecordObservable T F) hF Q zfun hz hzb
  change |followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z|≤
    H*(120*L^2*(L+1)^2)*B at hOF
  change |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z|≤
    H*(180*(L+2)^2*L^2)*B at hFF
  change |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z|≤
    H*(180*(L+2)^2*L)*B at hCF
  change |(cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
        cavityNormalizerGraftStreamingResponse D s a)*(∫r,zfun r∂Q)|≤510*L^2*B at hR
  have hR' : |a*H*(cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
        cavityNormalizerGraftStreamingResponse D s a)*Z|≤H*(510*L^2)*B := by
    rw [mul_assoc,abs_mul,abs_of_nonneg (mul_nonneg ha.1 hH)]
    apply (mul_le_mul_of_nonneg_left hR (mul_nonneg ha.1 hH)).trans
    have h0 : 0≤H*(510*L^2)*B:=by positivity
    calc
      _=a*(H*(510*L^2)*B):=by ring
      _≤1*(H*(510*L^2)*B):=mul_le_mul_of_nonneg_right ha.2 h0
      _=_:=one_mul _
  let x:=H*cavityMarkedSixExpectation D s a T
    (fun r=>followupCavityPhysicalRecordObservable n T F r*cavityOriginalDistinctLeafDefect n s T r)*Z
  let y:=followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z
  let z:=followupCavityCrossGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z
  let w:=followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu*Z
  let v:=H*followupCavityFutureGraftStreamingResponse D s a T (cavityFullTestToTerminal T F)*Z
  let r:=a*H*(cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
    cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
    (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      cavityNormalizerGraftStreamingResponse D s a)*Z
  have htriangle : |x-2*y+z+w+v+r|≤|x|+2*|y|+|z|+|w|+|v|+|r|:=by
    calc
      _≤|x-2*y+z+w+v|+|r|:=abs_add_le _ _
      _≤(|x-2*y+z+w|+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤((|x-2*y+z|+|w|)+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤(((|x-2*y|+|z|)+|w|)+|v|)+|r|:=by gcongr;exact abs_add_le _ _
      _≤((((|x|+|2*y|)+|z|)+|w|)+|v|)+|r|:=by gcongr;exact abs_sub _ _
      _=_:=by simp only [abs_mul,show |(2:ℝ)|=2 by norm_num]
  have he : followupCavitySecondStreamingResponse n β ρ hβ hρ s a T F u hu*Z=x-2*y+z+w+v+r := by
    unfold followupCavitySecondStreamingResponse
    dsimp only [x,y,z,w,v,r,H,D,Z]
    ring
  rw [he]
  change |x-2*y+z+w+v+r|≤H*cavityIndependentSecondStreamingCost L*B
  apply htriangle.trans
  have hs:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hOO
    (mul_le_mul_of_nonneg_left hOF (by norm_num : (0:ℝ)≤2))) hFF) hCF) hFU) hR'
  exact hs.trans_eq (by unfold cavityIndependentSecondStreamingCost;ring)

theorem abs_followupCavityPhysicalExpectation_secondWithinJet_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |followupCavityPhysicalRecordObservable n T F r|≤1)
    (Q : Measure X) [IsProbabilityMeasure Q] (zfun : X→ℝ)
    (hz : Measurable zfun) (hzb : ∀r,|zfun r|≤2)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |derivWithin (derivWithin (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1))
        (Icc (0:ℝ) 1) u*(∫r,zfun r∂Q)|≤
      (followupCavityAlpha n β ρ/2)^2*cavityIndependentSecondStreamingCost L*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+(∫r,|zfun r|^3∂Q)) := by
  dsimp only
  rw [(hasDerivWithinAt_followupCavityPhysicalExpectation_derivWithin hn β ρ hβ hρ s a ha has hq T F u hu).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu),mul_assoc,abs_mul,
    abs_of_nonneg (div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num))]
  exact (mul_le_mul_of_nonneg_left
    (followupCavitySecondStreamingResponse_bounded_external_cubic_le hn β ρ hβ hρ s a ha has hq T F hF Q zfun hz hzb u hu)
    (div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num))).trans_eq (by ring)

end QuantitativeFollowup
