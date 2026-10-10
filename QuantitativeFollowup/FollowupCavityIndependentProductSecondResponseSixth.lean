module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseMultiplier

@[expose] public section

/-! The sixth differentiated branch under a bounded old test and an
external independent defect retains all three cubic factors. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityIndependent_six_bounded_normalizer_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F) (hFb : ∀r,|F r|≤1)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2) :
    |cavityMarkedSixExpectation D s a T F*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*(∫r,z r∂P)|≤
      30*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          (∫r,|z r|^3∂P)) := by
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let C:=∫r,|z r|^3∂P
  let H:=fun q : Paper.Overlap=>cavityMarkedSixExpectation D s a T F*
    (∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)*(∫r,z r∂P)
  have hb (q : Paper.Overlap) : |H q|≤15*L^2*(M+B+cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q+C):=by
    let Q:=(anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q).snd
    let y:=fun r : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q r.1 r.2
    have hy : Measurable y:=measurable_of_finite _
    have hh:=cavityIndependent_six_bounded_twoMeans_cubic_le hn D s a ha has hq T F hF hFb
      Q P y z hy hz (fun r=>cavitySpinOverlapDefect_abs_le_two n q q.property r.1 r.2) hzb
    have he : (∫r,y r∂Q)=∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q:=
      integral_map measurable_snd.aemeasurable hy.aestronglyMeasurable
    have hc : (∫r,|y r|^3∂Q)=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q:=by
      rw [cavityCubicPairMoment_eq_fresh];simp only [Q,y,cavitySpinOverlapDefect_abs_eq_rest]
    rw [he,hc] at hh
    exact hh
  have hi (g : Paper.Overlap→ℝ) : Integrable g ν:=by
    dsimp only [ν];rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hm : ν.real univ=1-a:=by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hh:=abs_integral_le_integral_abs.trans (integral_mono (hi _) (hi _) hb)
  have he : (∫q,H q∂ν)=cavityMarkedSixExpectation D s a T F*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*(∫r,z r∂P):=by
    dsimp only [H,cavityNormalizerFreshDefect]
    rw [integral_mul_const,integral_const_mul]
  rw [he,integral_const_mul,integral_add (hi _) (hi _),integral_add (hi _) (hi _),integral_const,integral_const,hm] at hh
  change _≤15*L^2*((1-a)*(M+B)+M+(1-a)*C) at hh
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun _=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  exact hh.trans (by
    change 15*L^2*((1-a)*(M+B)+M+(1-a)*C)≤30*L^2*(M+B+C)
    have hb : (1-a)*(M+B)+M+(1-a)*C≤2*(M+B+C):=by
      nlinarith only [mul_nonneg ha.1 (add_nonneg hM hB),mul_nonneg ha.1 hC,hB,hC]
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring))

theorem cavityIndependent_sixth_bounded_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F) (hFb : ∀r,|F r|≤1)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ) (hz : Measurable z) (hzb : ∀r,|z r|≤2) :
    |(cavityMarkedSixExpectation D s a T F*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerGraftStreamingResponse D s a)*(∫r,z r∂P)|≤
      510*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          (∫r,|z r|^3∂P)) := by
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let C:=∫r,|z r|^3∂P
  let E:=∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T
  have hE : |E|≤1:=by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=anisotropicTrimmedRecordedTreeLaw D s a T) (f:=F) (C:=1)
        (.of_forall fun r=>by simpa only [Real.norm_eq_abs] using hFb r)
  have h1:=cavityIndependent_six_bounded_normalizer_external_cubic_le hn D s a ha has hq T F hF hFb P z hz hzb
  have h2:=cavityIndependent_normalizerResponse_external_cubic_le hn D s a ha has hq P z hz hzb
  have h2' : |E*cavityNormalizerGraftStreamingResponse D s a*(∫r,z r∂P)|≤480*(M+C):=by
    rw [mul_assoc,abs_mul,mul_comm (cavityNormalizerGraftStreamingResponse D s a)]
    exact (mul_le_mul_of_nonneg_right hE (abs_nonneg _)).trans (by simpa only [one_mul] using h2)
  rw [add_mul]
  apply (abs_add_le _ _).trans
  have hL : 1≤L:=by dsimp only [L];exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun _=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have he:=mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) (show 0≤M+C by positivity)
  have hb:=mul_nonneg (sq_nonneg L) hB
  change _≤510*L^2*(M+B+C)
  nlinarith only [h1,h2',he,hb]

end QuantitativeFollowup
