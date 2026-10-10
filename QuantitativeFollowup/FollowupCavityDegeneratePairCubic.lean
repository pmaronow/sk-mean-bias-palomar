module
public import QuantitativeFollowup.FollowupCavityBranchCubic
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! Repeated terminal leaves contribute zero physical defect. Therefore
cubic branch domination includes every three-pair choice from the actual
streaming sums, without imposing distinctness of those pairs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 800000

theorem cavityRestOverlap_self (hn : 0<n) (σ : Configuration (n+1)) :
    cavityRestOverlap n σ σ=1 := by
  have hs (b : Bool) : Paper.spinSign b*Paper.spinSign b=1 := by
    cases b <;> norm_num [Paper.spinSign]
  simp only [cavityRestOverlap,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast hn.ne')

theorem cavityRecorded_threeDefects_le_branch_cubic_all_pairs
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hzero : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=0) (hq : ∀l,l<j→q (l+1)≤q l)
    (i k : Fin 3→ObservationLeaf T) :
    (∫z,|cavitySpinOverlapDefect n (q (observationCommonLevel T (i 0) (k 0)))
      (observationLeafSpin T (i 0) z.2) (observationLeafSpin T (k 0) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 1) (k 1)))
      (observationLeafSpin T (i 1) z.2) (observationLeafSpin T (k 1) z.2)*
      cavitySpinOverlapDefect n (q (observationCommonLevel T (i 2) (k 2)))
      (observationLeafSpin T (i 2) z.2) (observationLeafSpin T (k 2) z.2)|
      ∂anisotropicRecordedProfileTreeLaw D μ a q T)≤
      finiteCascadeUnweightedBranchSum (fun l=>cavityCubicPairMoment D μ a (q l)) T := by
  by_cases h0 : i 0=k 0
  · simp only [←h0,observationCommonLevel_self,hzero,Set.Icc.coe_one,cavitySpinOverlapDefect_self n hn,
      zero_mul,abs_zero,integral_zero]
    exact finiteCascadeUnweightedBranchSum_nonneg _ (fun l=>(cavityCubicPairMoment_bounds D μ a (q l)).1) T
  by_cases h1 : i 1=k 1
  · simp only [←h1,observationCommonLevel_self,hzero,Set.Icc.coe_one,cavitySpinOverlapDefect_self n hn,
      mul_zero,zero_mul,abs_zero,integral_zero]
    exact finiteCascadeUnweightedBranchSum_nonneg _ (fun l=>(cavityCubicPairMoment_bounds D μ a (q l)).1) T
  by_cases h2 : i 2=k 2
  · simp only [←h2,observationCommonLevel_self,hzero,Set.Icc.coe_one,cavitySpinOverlapDefect_self n hn,
      mul_zero,abs_zero,integral_zero]
    exact finiteCascadeUnweightedBranchSum_nonneg _ (fun l=>(cavityCubicPairMoment_bounds D μ a (q l)).1) T
  exact cavityRecorded_threeDefects_le_branch_cubic D μ a q hzero T hroot hq i k (by
    intro r
    fin_cases r <;> assumption)

end QuantitativeFollowup
