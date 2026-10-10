module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseBasic

@[expose] public section

/-! Independent normalizer factors keep a genuine third-defect budget
when multiplied by an external independently sampled pair observable. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem independent_three_means {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (P : Measure X) (Q : Measure Y) (R : Measure Z)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (x : X→ℝ) (y : Y→ℝ) (z : Z→ℝ)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hxb : ∀r,|x r|≤2) (hyb : ∀r,|y r|≤2) (hzb : ∀r,|z r|≤2) :
    |(∫r,x r∂P)*(∫r,y r∂Q)*(∫r,z r∂ R)|≤
      (∫r,|x r|^3∂P)+(∫r,|y r|^3∂Q)+(∫r,|z r|^3∂ R) := by
  have hh:=independent_pair_product_cubic_bound (P.prod Q) R
    (fun w=>x w.1) (fun w=>y w.2) z (hx.comp measurable_fst) (hy.comp measurable_snd) hz
    (fun w=>hxb w.1) (fun w=>hyb w.2) hzb
  rw [integral_prod_mul] at hh
  have hx3 : (∫w : X×Y,|x w.1|^3∂ P.prod Q)=∫r,|x r|^3∂P:=by
    simpa only [probReal_univ,one_smul] using integral_fun_fst (μ:=P) (ν:=Q) (fun r=>|x r|^3)
  have hy3 : (∫w : X×Y,|y w.2|^3∂ P.prod Q)=∫r,|y r|^3∂Q:=by
    simpa only [probReal_univ,one_smul] using integral_fun_snd (μ:=P) (ν:=Q) (fun r=>|y r|^3)
  rw [hx3,hy3] at hh
  have hx0 : 0≤∫r,|x r|^3∂P:=integral_nonneg fun _=>by positivity
  have hy0 : 0≤∫r,|y r|^3∂Q:=integral_nonneg fun _=>by positivity
  have hz0 : 0≤∫r,|z r|^3∂ R:=integral_nonneg fun _=>by positivity
  exact hh.trans (by linarith)

theorem cavityIndependent_normalizer_twoMeans_cubic_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (y : X→ℝ) (z : Y→ℝ) (hy : Measurable y) (hz : Measurable z)
    (hyb : ∀r,|y r|≤2) (hzb : ∀r,|z r|≤2) :
    |cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*(∫r,y r∂P)*(∫r,z r∂Q)|≤
      cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        (∫r,|y r|^3∂P)+(∫r,|z r|^3∂Q) := by
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let C:=∫r,|y r|^3∂P
  let B:=∫r,|z r|^3∂Q
  let H:=fun q : Paper.Overlap=>
    (∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)*(∫r,y r∂P)*(∫r,z r∂Q)
  have hb (q : Paper.Overlap) : |H q|≤cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q+C+B:=by
    let R:=(anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q).snd
    let x:=fun r : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q r.1 r.2
    have hx : Measurable x:=measurable_of_finite _
    have hh:=independent_three_means R P Q x y z hx hy hz
      (fun r=>cavitySpinOverlapDefect_abs_le_two n q q.property r.1 r.2) hyb hzb
    have he : (∫r,x r∂ R)=∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q:=
      integral_map measurable_snd.aemeasurable hx.aestronglyMeasurable
    have hc : (∫r,|x r|^3∂ R)=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q:=by
      rw [cavityCubicPairMoment_eq_fresh];simp only [R,x,cavitySpinOverlapDefect_abs_eq_rest]
    rw [he,hc] at hh
    exact hh
  have hi (g : Paper.Overlap→ℝ) : Integrable g ν:=by
    dsimp only [ν];rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hm : ν.real univ=1-a:=by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hh:=abs_integral_le_integral_abs.trans (integral_mono (hi _) (hi _) hb)
  have he : (∫q,H q∂ν)=cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*(∫r,y r∂P)*(∫r,z r∂Q):=by
    dsimp only [H,cavityNormalizerFreshDefect];rw [integral_mul_const,integral_mul_const]
  rw [he,integral_add (hi _) (hi _),integral_add (hi _) (hi _),integral_const,integral_const,hm] at hh
  change _≤cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+(1-a)*C+(1-a)*B at hh
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hB : 0≤B:=integral_nonneg fun _=>by positivity
  exact hh.trans (by nlinarith [mul_nonneg ha.1 hC,mul_nonneg ha.1 hB])

theorem cavityIndependent_normalizerResponse_external_cubic_le {X : Type*} [MeasurableSpace X]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (P : Measure X) [IsProbabilityMeasure P] (z : X→ℝ)
    (hz : Measurable z) (hzb : ∀r,|z r|≤2) :
    |(∫r,z r∂P)*cavityNormalizerGraftStreamingResponse D s a|≤
      480*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+(∫r,|z r|^3∂P)) := by
  let E:=∫r,z r∂P
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let C:=∫r,|z r|^3∂P
  let B:=C
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=integral_nonneg fun _=>by positivity
  have hb (j : vectorPosteriorFeatureIndex k) :
      |cavityNormalizerGraftPairResponse D s a j*E|≤240*(M+f (vectorProfileAtom s j)+B):=by
    let U:=cavityNormalizerGraftTree j
    let G:=fun r : CavityPathRecordSpace (trimRoot U) (n+1)=>cavityNormalizerGraftTerminalTest s j
      (finiteCascadeRecordTerminalSpins (cavityNormalizerGraftPairTree j).tree r.2)
    let terminal := fun r : CavityPathRecordSpace (trimRoot U) (n+1)=>
      finiteCascadeRecordTerminalSpins (cavityNormalizerGraftPairTree j).tree r.2
    have hterminal : Measurable terminal :=
      (measurable_finiteCascadeRecordTerminalSpins (E:=FiniteStateField (Configuration (n+1)))
        (S:=Configuration (n+1)) (cavityNormalizerGraftPairTree j).tree).comp measurable_snd
    have hGt : Measurable (cavityNormalizerGraftTerminalTest (n:=n) s j) := measurable_of_finite _
    have hG0 : Measurable ((cavityNormalizerGraftTerminalTest (n:=n) s j)∘terminal) := hGt.comp hterminal
    have hG : Measurable G := hG0
    have hd (r) : |G r|≤|cavityRecordedLeafPairDefect s (trimRoot U)
        (observationPairFirstLeaf (cavityNormalizerGraftPairTree j))
        (observationPairSecondLeaf (cavityNormalizerGraftPairTree j)) r.2|:=by
      apply le_of_eq
      dsimp only [G,cavityNormalizerGraftTerminalTest,cavityRecordedLeafPairDefect,U,cavityNormalizerGraftTree,trimRoot]
      rw [observationTerminalSpin_record,observationTerminalSpin_record]
      rw [←cavityNormalizerGraftPair_commonLevel s j]
      rfl
    have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq U
      (observationPairFirstLeaf (cavityNormalizerGraftPairTree j))
      (observationPairSecondLeaf (cavityNormalizerGraftPairTree j)) G hG hd P z hz hzb
    have hL : FiniteCascadeGenealogy.leafCount (asGenealogy U)=2:=by
      exact observationPairTree_leafCount (cavityNormalizerGraftPairTree j)
    have hBU : finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot U)=f (vectorProfileAtom s j):=by
      rw [show trimRoot U=(cavityNormalizerGraftPairTree j).tree by rfl,
        observationPairTree_branchSum,cavityNormalizerGraftPairTree,
        finiteCascadeFuturePairTree_split _ _ (cavityNormalizerGraftAtomDepth_le j),
        cavityProfileLevel_normalizerGraftAtomDepth]
    change |cavityNormalizerGraftPairResponse D s a j*E|≤
      60*(FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2*(M+_+C) at hh
    rw [hL,hBU] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hh : |E*cavityNormalizerGraftStreamingResponse D s a|≤
      ∑j,vectorPosteriorFeatureWeight s a j*(240*(M+f (vectorProfileAtom s j)+B)):=by
    unfold cavityNormalizerGraftStreamingResponse
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum;intro j _
    rw [show E*(vectorPosteriorFeatureWeight s a j*cavityNormalizerGraftPairResponse D s a j)=
      vectorPosteriorFeatureWeight s a j*(cavityNormalizerGraftPairResponse D s a j*E) by ring,
      abs_mul,abs_of_nonneg (vectorPosteriorFeatureWeight_nonneg s a has j)]
    exact mul_le_mul_of_nonneg_left (hb j) (vectorPosteriorFeatureWeight_nonneg s a has j)
  have hsum : (∑j,vectorPosteriorFeatureWeight s a j*(240*(M+f (vectorProfileAtom s j)+B)))=
      ∫q,240*(M+f q+B)∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq,integral_vectorProfileFreeMeasure s a has]
  rw [hsum,integral_const_mul] at hh
  have hi (g : Paper.Overlap→ℝ) : Integrable g (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a):=by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  rw [integral_add (hi _) (hi _),integral_add (hi _) (hi _),integral_const,integral_const,
    show (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ=1-a by
      rw [measureReal_def,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]] at hh
  change |E*cavityNormalizerGraftStreamingResponse D s a|≤240*((1-a)*M+M+(1-a)*B) at hh
  change _≤480*(M+B)
  exact hh.trans (by nlinarith [mul_nonneg ha.1 hM,mul_nonneg ha.1 hB])

end QuantitativeFollowup
