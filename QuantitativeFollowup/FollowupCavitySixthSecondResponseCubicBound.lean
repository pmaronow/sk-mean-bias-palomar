module
public import QuantitativeFollowup.FollowupCavitySixthSecondResponseCubicMarked
public import QuantitativeFollowup.FollowupCavityNormalizerGraftResponseStieltjes

@[expose] public section

/-! Both independent products in the actual normalizer streaming
derivative have a genuine cubic branch budget. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavitySixth_six_mul_normalizer_cubic_le
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a T F*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a|≤
      120*L^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let E:=cavityMarkedSixExpectation D s a T F
  have hi (g : Paper.Overlap→ℝ) : Integrable g ν:=by
    dsimp only [ν];rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hmass : ν.real univ=1-a:=by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _
    (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  let H:=fun q : Paper.Overlap=>E*(∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2
    ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)
  have hH (q : Paper.Overlap) : |H q|≤60*L^2*(M+B+cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q):=by
    let P:=(anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q).snd
    let z:=fun r : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q r.1 r.2
    have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq T i l F hF hdom P z
      (measurable_of_finite _) (fun r=>cavitySpinOverlapDefect_abs_le_two n q q.property r.1 r.2)
    have he : (∫r,z r∂P)=∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q:=
      integral_map measurable_snd.aemeasurable (measurable_of_finite z).aestronglyMeasurable
    have hc : (∫r,|z r|^3∂P)=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q:=by
      rw [cavityCubicPairMoment_eq_fresh]
      simp only [P,z,cavitySpinOverlapDefect_abs_eq_rest]
    rw [he,hc] at hh
    exact hh
  have hh:=abs_integral_le_integral_abs.trans (integral_mono (hi _) (hi _) hH)
  have he : (∫q,H q∂ν)=E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a:=by
    dsimp only [H,cavityNormalizerFreshDefect];rw [integral_const_mul]
  rw [he,integral_const_mul,integral_add (hi _) (hi _),integral_const,hmass] at hh
  change |E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a|≤
    60*L^2*((1-a)*(M+B)+M) at hh
  change _≤120*L^2*(M+B)
  exact hh.trans (by
    have hs : (1-a)*(M+B)+M≤2*(M+B):=by nlinarith [mul_nonneg ha.1 (add_nonneg hM hB)]
    nlinarith only [mul_le_mul_of_nonneg_left hs (show 0≤60*L^2 by positivity)])

theorem cavitySixth_mean_mul_normalizer_response_cubic_le
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    |(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      cavityNormalizerGraftStreamingResponse D s a|≤
      480*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  classical
  let P:=anisotropicTrimmedRecordedTreeLaw D s a T
  let E:=∫r,F r∂P
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let C:=∫r,|F r|^3∂P
  have hFb (r) : |F r|≤2:=(hdom r).trans (cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) i l r.2)
  have hiF : Integrable (fun r=>|F r|^3) P:=by
    apply (integrable_const (8:ℝ)).mono' (hF.abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun r=>by
      have hb:=pow_le_pow_left₀ (abs_nonneg _) (hFb r) 3
      norm_num at hb
      simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hb
  let x:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>cavityRecordedLeafPairDefect s (trimRoot T) i l r.2
  have hx : Measurable x:=(measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1)))
    s (trimRoot T) i l).comp measurable_snd
  have hix : Integrable (fun r=>|x r|^3) P:=by
    apply (integrable_const (8:ℝ)).mono' (hx.abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun r=>by
      have hb:=pow_le_pow_left₀ (abs_nonneg _) (cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) i l r.2) 3
      norm_num at hb
      simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hb
  have hCB : C≤B:=(integral_mono hiF hix fun r=>pow_le_pow_left₀ (abs_nonneg _) (hdom r) 3).trans
    (cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T i l)
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
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
      (observationPairSecondLeaf (cavityNormalizerGraftPairTree j)) G hG hd P F hF hFb
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
    exact hh.trans (by nlinarith)
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

theorem cavitySixth_second_response_cubic_le
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a T F*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
      (∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerGraftStreamingResponse D s a|≤
      600*L^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let B:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  have hL : 1≤L:=by dsimp only [L]; exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hB : 0≤B:=add_nonneg (integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    (finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _)
  have h1:=cavitySixth_six_mul_normalizer_cubic_le hn D s a ha has hq T i l F hF hdom
  have h2:=cavitySixth_mean_mul_normalizer_response_cubic_le hn D s a ha has hq T i l F hF hdom
  have ht:=abs_add_le
    (cavityMarkedSixExpectation D s a T F*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a)
    ((∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerGraftStreamingResponse D s a)
  have hb : B≤L^2*B:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) hB
  change _≤600*L^2*B
  nlinarith only [ht,h1,h2,hb]

theorem derivWithin_followupCavitySixthGraftExpectation_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (hdom : ∀r,|followupCavityPhysicalRecordObservable n T F r|≤
      |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |derivWithin (followupCavitySixthGraftExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1) u|≤
      a*(followupCavityAlpha n β ρ/2)*(600*L^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  rw [(hasDerivWithinAt_followupCavitySixthGraftExpectation hn β ρ hβ hρ s a ha has hq T F u hu).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu)]
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hp : 0≤a*(followupCavityAlpha n β ρ/2) :=
    mul_nonneg ha.1 (div_nonneg hα (by norm_num))
  rw [abs_mul,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left (cavitySixth_second_response_cubic_le hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a ha has hq T i l
    (followupCavityPhysicalRecordObservable n T F) (measurable_followupCavityPhysicalRecordObservable T F) hdom)
      hp).trans_eq (by ring)

end QuantitativeFollowup
