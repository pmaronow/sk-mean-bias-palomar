module
public import QuantitativePaper.UniformScalarTrialFromGrowth
public import QuantitativePaper.UniformScalarRootGrowthLowerFamily

@[expose] public section

/-! The actual uniform fifth-order scalar trial budget. The lower root
growth, cutoff state laws, stochastic cost identity and universal smoothing
are all proved for the true model, rather than supplied to this endpoint. -/
noncomputable section
open Set Paper FRSB QuantitativeFollowup
namespace QuantitativePaper

theorem scalar_energy_trial_uniform_fifth_order (β₀ : ℝ) (hβ₀ : 1<β₀) :
    ∃C1 lamstar : ℝ,1≤C1 ∧ 0<lamstar ∧ lamstar≤1 ∧ lamstar≤β₀/2 ∧
      ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      ∀lam∈Icc (0:ℝ) lamstar,∃hs : lam/β∈Icc (0:ℝ) 1,
        0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤
          parisiPDEFunctional β 0 (scalarClippedTrialMeasure (lam/β) hs μ)/β-scalarEnergyValue β 0 ∧
        parisiPDEFunctional β 0 (scalarClippedTrialMeasure (lam/β) hs μ)/β-scalarEnergyValue β 0≤C1*lam^5 := by
  obtain ⟨k,T,hk,hT,hroot⟩:=scalar_minimizer_uniform_root_lower β₀ hβ₀
  obtain ⟨C1,L,hC1,hL,hL1,hLβ,_hLT,hcost⟩:=
    scalar_clipped_trial_uniform_fifth_order_of_root_growth β₀ hβ₀ k T hk hT hroot
  exact ⟨C1,L,hC1,hL,hL1,hLβ,hcost⟩

theorem scalar_floor_uniform_fifth_order (β₀ : ℝ) (hβ₀ : 1<β₀) :
    ∃C1 lamstar : ℝ,1≤C1 ∧ 0<lamstar ∧ lamstar≤1 ∧ lamstar≤β₀/2 ∧
      ∀β,β₀≤β→∀lam∈Icc (0:ℝ) lamstar,
        0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤C1*lam^5 := by
  obtain ⟨C1,L,hC1,hL,hL1,hLβ,hcost⟩:=scalar_energy_trial_uniform_fifth_order β₀ hβ₀
  refine ⟨C1,L,hC1,hL,hL1,hLβ,?_⟩
  intro β hβ lam hlam
  obtain ⟨hs,h0,htrial,hbound⟩:=hcost β hβ (parisiMinimizer β 0)
    (isParisiMinimizer_selected β 0) lam hlam
  exact ⟨h0,htrial.trans hbound⟩

end QuantitativePaper
