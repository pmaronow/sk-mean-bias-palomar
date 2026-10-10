module
public import QuantitativeFollowup.FoundationScalarTrialConstants
public import QuantitativePaper.UniformEnergyMeanPrebound
public import QuantitativePaper.UniformEnergyVarianceLower

@[expose] public section

/-! Follow-up Proposition 2.6 with its literal midpoint expression.
The convexity and both comparison-error signs are genuine model results. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

theorem foundation_mean_bias_midpoint (n : ℕ) (hn : 0< n) (β : ℝ) (hβ : 0<β)
    (lam : ℝ) (hlam : 0< lam) (hfrac : 2*lam/β∈Ioo (0:ℝ) 1) :
    0≤ energyMeanDeficit n β ∧
      energyMeanDeficit n β≤ scalarEnergyValue β 0-2*scalarEnergyValue β lam+
        scalarEnergyValue β (2*lam)+2*energyComparisonError n β lam := by
  refine ⟨energyMeanDeficit_nonneg n hn β hβ,?_⟩
  have hc:=(convexOn_scalarCenteredEnergyMoment n β hβ).2 (mem_univ 0) (mem_univ (2*lam))
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,mul_zero,zero_add] at hc
  rw [show (1/2:ℝ)*(2*lam)=lam by ring,scalarCenteredEnergyMoment_zero] at hc
  have he2:=energyComparisonError_nonneg n hn β hβ (2*lam) hfrac
  rw [energy_tail_moment_exact n hn β hlam.ne',
    energy_tail_moment_exact n hn β (show 2*lam≠0 by positivity)] at hc
  have hd:(2*lam)/(4*(n:ℝ))=2*(lam/(4*(n:ℝ))):=by ring
  rw [hd] at hc
  linarith

theorem foundation_mean_bias (β : ℝ) (hβ : 1<β) :
    ∃L lambda0 : ℝ,1≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ lambda0≤β/4 ∧
      ∀n : ℕ,0< n→∀lam∈Ioc (0:ℝ) lambda0,
        0≤ energyMeanDeficit n β ∧
        energyMeanDeficit n β≤ scalarEnergyValue β 0-2*scalarEnergyValue β lam+
          scalarEnergyValue β (2*lam)+2*energyComparisonError n β lam ∧
        scalarEnergyValue β 0-2*scalarEnergyValue β lam+scalarEnergyValue β (2*lam)+
          2*energyComparisonError n β lam≤32*L*lam^5+2*energyComparisonError n β lam := by
  obtain ⟨L,lambda0,hL,h0,h0β,htrial⟩:=foundation_scalar_trial_constants β hβ
  have hβp:0<β:=zero_lt_one.trans hβ
  obtain ⟨μ,hμ⟩:=FRSB.exists_parisi_minimizer β 0
  refine ⟨L,lambda0,hL,h0,h0β,?_⟩
  intro n hn lam hlam
  have hlp:0<lam:=hlam.1
  have hfrac:2*lam/β∈Ioo (0:ℝ) 1:=by
    constructor
    · positivity
    · apply (div_lt_one hβp).2
      have hh:=hlam.2.trans h0β
      linarith
  have hmid:=foundation_mean_bias_midpoint n hn β hβp lam hlam.1 hfrac
  obtain ⟨hs,hν,hzero,hcost,hbound⟩:=htrial μ hμ (2*lam)
    ⟨by positivity,mul_le_mul_of_nonneg_left hlam.2 (by norm_num)⟩
  have hzero1:=scalarEnergyValue_gap_nonneg β lam hβp
    (show lam/β∈Icc (0:ℝ) 1 by
      constructor
      · positivity
      · apply (div_le_one hβp).2
        have hh:=(div_lt_one hβp).1 hfrac.2
        linarith)
  refine ⟨hmid.1,hmid.2,?_⟩
  have hb:=hcost.trans hbound
  nlinarith [show L*(2*lam)^5=32*L*lam^5 by ring]

end QuantitativeFollowup
