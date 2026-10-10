module
public import QuantitativeFollowup.FollowupCavitySixthSecondResponseCubicCheckpoint

@[expose] public section

/-! Independent recorded roots are retained when a one-pair response is
multiplied by a pair-dominated mean on another genuine observation tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityIndependent_onePair_cube_le_branch
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    (∫r,|F r|^3∂anisotropicTrimmedRecordedTreeLaw D s a T)≤
      finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) := by
  let P:=anisotropicTrimmedRecordedTreeLaw D s a T
  let x:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>
    cavityRecordedLeafPairDefect s (trimRoot T) i l r.2
  have hx : Measurable x:=(measurable_cavityRecordedLeafPairDefect (n:=n)
    (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) i l).comp measurable_snd
  have hxb (r) : |x r|≤2:=cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) i l r.2
  have hFb (r) : |F r|≤2:=(hdom r).trans (hxb r)
  have hiF : Integrable (fun r=>|F r|^3) P:=by
    apply (integrable_const (8:ℝ)).mono' (hF.abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun r=>by
      have hb:=pow_le_pow_left₀ (abs_nonneg _) (hFb r) 3
      norm_num at hb
      simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hb
  have hix : Integrable (fun r=>|x r|^3) P:=by
    apply (integrable_const (8:ℝ)).mono' (hx.abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun r=>by
      have hb:=pow_le_pow_left₀ (abs_nonneg _) (hxb r) 3
      norm_num at hb
      simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hb
  exact (integral_mono hiF hix fun r=>pow_le_pow_left₀ (abs_nonneg _) (hdom r) 3).trans
    (cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T i l)

theorem cavityIndependent_onePair_six_pairMean_cubic_le
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T U : FiniteTerminalGenealogy (k+2))
    (i l : ObservationLeaf (trimRoot T)) (j h : ObservationLeaf (trimRoot U))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdomF : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (G : CavityPathRecordSpace (trimRoot U) (n+1)→ℝ) (hG : Measurable G)
    (hdomG : ∀r,|G r|≤|cavityRecordedLeafPairDefect s (trimRoot U) j h r.2|) :
    |cavityMarkedSixExpectation D s a T F*(∫r,G r∂anisotropicTrimmedRecordedTreeLaw D s a U)|≤
      60*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot U)) := by
  have hGb (r) : |G r|≤2:=(hdomG r).trans (cavityRecordedLeafPairDefect_abs_le_two s (trimRoot U) j h r.2)
  have hh:=cavityMarkedSix_onePair_independent_cubic_le hn D s a ha has hq T i l F hF hdomF
    (anisotropicTrimmedRecordedTreeLaw D s a U) G hG hGb
  have hc:=cavityIndependent_onePair_cube_le_branch hn D s a hq U j h G hG hdomG
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hc]) (by positivity))

end QuantitativeFollowup
