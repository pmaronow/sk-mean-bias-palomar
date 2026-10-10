module
public import QuantitativeFollowup.FollowupCavityOriginalStreamingCubic
public import QuantitativeFollowup.FollowupCavityFreshStreamingCubic

@[expose] public section

/-! The complete physical six-term streaming response for a two-pair
observable is bounded by actual free and inherited-branch cubic moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityMarkedSix_pairProduct_cubic_budget (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    let B:=finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
    |cavityMarkedSixExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      (4*L^2+4*L+1)*cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+(8*L^2+5*L+2)*B := by
  dsimp only
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let F:=cavityRecordedPairProduct (n:=n) s (trimRoot T) i l
  let OO:=∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂anisotropicTrimmedRecordedTreeLaw D s a T
  let OF:=cavityOriginalFreshExpectation D s a T F
  let FF:=cavityFreshFreshExpectation D s a T F
  let CF:=cavityCurrentFreshExpectation D s a T F
  let FU:=cavityFutureFreshExpectation D s a T F
  let R:=a*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a
  have hOO:|OO|≤L^2*B:=(cavityOriginalOriginal_pairProduct_abs_le_moment hn D s a T i l).trans
    (cavityOriginalLeafTripleMoment_le hn D s a hq T i l)
  have hOF:|OF|≤L^2*(M+2*B):=(cavityOriginalFresh_pairProduct_abs_le_moment D s a has T i l).trans
    (cavityChargedOriginalFreshTripleMoment_le hn D s a ha has hq T i l)
  have hFF:|FF|≤L^2*(2*M+3*B):=(cavityFreshFresh_pairProduct_abs_le_moment D s a has T i l).trans
    (cavityChargedCrossMarkedTripleMoment_le hn D s a ha has hq T i l)
  have hCF:|CF|≤L*(2*M+3*B):=(cavityCurrentFresh_pairProduct_abs_le_moment D s a has T i l).trans
    (cavityChargedCurrentMarkedTripleMoment_le hn D s a ha has hq T i l)
  have hFU:|FU|≤2*L*(M+B):=(cavityFutureFresh_pairProduct_abs_le_moment D s a ha.1 has hq T i l).trans
    (cavityChargedFutureMarkedTripleMoment_le hn D s a ha has hq T i l)
  have hB:0≤B:=finiteCascadeUnweightedBranchSum_nonneg _
    (fun d=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a _).1) _
  have hM:0≤M:=integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1)
  have hR:|R|≤2*B+M:=by
    dsimp only [R]
    rw [mul_assoc]
    rw [abs_mul,abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_left (cavityNormalizer_leaf_cubic_budget hn D s a ha has hq T i l) ha.1).trans
      ((mul_le_mul_of_nonneg_right ha.2 (by positivity)).trans_eq (one_mul _))
  have h1:=abs_sub OO (2*OF)
  rw [abs_mul,show |(2:ℝ)|=2 by norm_num] at h1
  have h2:=abs_add_le (OO-2*OF) FF
  have h3:=abs_add_le (OO-2*OF+FF) CF
  have h4:=abs_add_le (OO-2*OF+FF+CF) FU
  have h5:=abs_add_le (OO-2*OF+FF+CF+FU) R
  change |OO-2*OF+FF+CF+FU+R|≤(4*L^2+4*L+1)*M+(8*L^2+5*L+2)*B
  nlinarith only [h1,h2,h3,h4,h5,hOO,hOF,hFF,hCF,hFU,hR]

theorem cavityMarkedSix_pairProduct_cubic_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |cavityMarkedSixExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      15*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  have hh:=cavityMarkedSix_pairProduct_cubic_budget hn D s a ha has hq T i l
  dsimp only at hh
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  have hL:1≤L:=by
    dsimp only [L]
    exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hB:0≤B:=finiteCascadeUnweightedBranchSum_nonneg _
    (fun d=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a _).1) _
  have hM:0≤M:=integral_nonneg (fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1)
  have hLM:L≤L^2:=by nlinarith
  have h1:4*L^2+4*L+1≤15*L^2:=by nlinarith
  have h2:8*L^2+5*L+2≤15*L^2:=by nlinarith
  have hm:=mul_le_mul_of_nonneg_right h1 hM
  have hb:=mul_le_mul_of_nonneg_right h2 hB
  exact hh.trans (by change (4*L^2+4*L+1)*M+(8*L^2+5*L+2)*B≤15*L^2*(M+B);nlinarith only [hm,hb])

end QuantitativeFollowup
