module
public import QuantitativeFollowup.FollowupCavityNativeCppCrossFirst
public import QuantitativeFollowup.FollowupCavityNativeCppExternalSecond
public import QuantitativeFollowup.FollowupCavityCppNativeFactorJets
public import QuantitativeFollowup.FollowupCavityCppPairLaw

@[expose] public section

/-! The genuine native Cpp second derivative has a cubic budget. Independent
binary products are bounded using their actual separate sampling laws. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def cavityCppSecondStreamingCost : ℝ :=
  cavitySecondStreamingCost 4+cavityIndependentSecondStreamingCost 2+57600+cavitySecondStreamingCost 2

theorem cavityCppSecondStreamingCost_eq : cavityCppSecondStreamingCost=179160 := by
  norm_num [cavityCppSecondStreamingCost,cavitySecondStreamingCost,cavityIndependentSecondStreamingCost]

theorem abs_followupCavityCppFunction_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u|≤
      (followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost*
        (cavityThirdMoment D μ a+3*cavityCubicPairMoment D μ a p) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let M:=cavityThirdMoment D μ a
  let χ:=cavityCubicPairMoment D μ a p
  let H:=(followupCavityAlpha n β ρ/2)^2
  let f:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p)
  let g:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
  let h:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
  have hM : 0≤M:=cavityThirdMoment_nonneg D μ a
  have hχ : 0≤χ:=(cavityCubicPairMoment_bounds D μ a p).1
  have hH : 0≤H:=sq_nonneg _
  have he0 : |g u|≤1:=abs_followupCavityCppEpsilonExpectation_le_one β ρ hβ hρ μ a p u hu
  have h4 : |withinJet f (Icc 0 1) 2 u|≤H*cavitySecondStreamingCost 4*(M+3*χ):=
    abs_followupCavityCppFour_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu
  have he2 : |withinJet g (Icc 0 1) 2 u*h u|≤H*cavityIndependentSecondStreamingCost 2*(M+3*χ):=by
    have hh:=abs_followupCavityCppEpsilonSecondTau_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu
    exact hh.trans (mul_le_mul_of_nonneg_left (by dsimp only [M,χ,D];linarith [hχ])
      (mul_nonneg hH (by norm_num [cavityIndependentSecondStreamingCost])))
  have he1 : |withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u|≤H*28800*(M+3*χ):=by
    have hh:=abs_followupCavityCppCrossFirst_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu
    exact hh.trans (mul_le_mul_of_nonneg_left (by dsimp only [M,χ,D];linarith [hχ])
      (mul_nonneg hH (by norm_num)))
  have ht2 : |g u*withinJet h (Icc 0 1) 2 u|≤H*cavitySecondStreamingCost 2*(M+3*χ):=by
    rw [abs_mul]
    have hh:=abs_followupCavityCppTau_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu
    have hht : |withinJet h (Icc 0 1) 2 u|≤H*cavitySecondStreamingCost 2*(M+3*χ):=
      hh.trans (mul_le_mul_of_nonneg_left (by dsimp only [M,χ,D];linarith [hχ])
        (mul_nonneg hH (cavitySecondStreamingCost_nonneg 2 (by norm_num))))
    exact (mul_le_mul he0 hht (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have he1' : |2*withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u|≤2*(H*28800*(M+3*χ)) := by
    rw [mul_assoc,abs_mul,show |(2:ℝ)|=2 by norm_num]
    exact mul_le_mul_of_nonneg_left he1 (by norm_num)
  have h1:=(abs_sub (withinJet f (Icc 0 1) 2 u) (withinJet g (Icc 0 1) 2 u*h u)).trans
    (add_le_add h4 he2)
  have h2:=(abs_sub (withinJet f (Icc 0 1) 2 u-withinJet g (Icc 0 1) 2 u*h u)
    (2*withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u)).trans (add_le_add h1 he1')
  have h3:=(abs_sub (withinJet f (Icc 0 1) 2 u-withinJet g (Icc 0 1) 2 u*h u-
    2*withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u)
    (g u*withinJet h (Icc 0 1) 2 u)).trans (add_le_add h2 ht2)
  rw [followupCavityCppFunction_secondWithinJet_eq_factors hn β ρ hβ hρ μ a ha hfloor p u hu]
  exact h3.trans_eq (by dsimp only [H,M,χ,D,cavityCppSecondStreamingCost];ring)

end QuantitativeFollowup
