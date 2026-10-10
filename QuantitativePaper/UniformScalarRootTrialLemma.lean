module
public import QuantitativePaper.UniformScalarRootTrialAssembly
public import QuantitativePaper.UniformScalarRootGrowthUpperFamily

@[expose] public section

/-! Main Lemma 5.2, all literal uniform scalar root and trial clauses.
Every analytic, moment, support, Brownian, and variational input is
discharged for the actual scalar Parisi minimizer. -/
noncomputable section
namespace QuantitativePaper

theorem uniform_scalar_root_trial (β₀ : ℝ) (hβ₀ : 1<β₀) :
    UniformScalarRootTrialTarget β₀ := by
  obtain ⟨Cu,Cac,Tu,hCu,hCac,hTu,hupper⟩:=scalar_minimizer_uniform_root_upper_lipschitz β₀ hβ₀
  exact uniform_scalar_root_trial_of_upper_family β₀ hβ₀ Cu Cac Tu hCu hCac hTu hupper

end QuantitativePaper
