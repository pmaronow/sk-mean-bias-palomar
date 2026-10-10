module
public import QuantitativeFollowup.FollowupCavityCppFourDescendant
public import QuantitativeFollowup.FollowupCavityThreeDefectAlgebra

@[expose] public section

/-! Source Ψ, Ψε and Ψτ are literal genuine four- and two-descendant
moments, with rest overlap normalized by the number of retained spins. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 def cavityCppPsiFour (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p : Paper.Overlap) : ℝ:=
  ∫z,Paper.spinSign (z.2.1.1 (Fin.last n))*Paper.spinSign (z.2.1.2 (Fin.last n))*
    (cavityRestOverlap n z.2.2.1 z.2.2.2-(p:ℝ))∂cavityFourDescendantLaw D μ a p

 def cavityCppPsiEpsilon (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p : Paper.Overlap) : ℝ:=
  ∫z,Paper.spinSign (z.2.1 (Fin.last n))*Paper.spinSign (z.2.2 (Fin.last n))
    ∂anisotropicFreshTerminalPairLaw D μ a p

 def cavityCppPsiTau (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p : Paper.Overlap) : ℝ:=
  ∫z,cavityRestOverlap n z.2.1 z.2.2-(p:ℝ)∂anisotropicFreshTerminalPairLaw D μ a p

 theorem cavityCppSelectedOverlap_eq_rest (σ τ : Configuration (n+1)) :
    cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) σ τ=cavityRestOverlap n σ τ:=by
  unfold cavitySelectedSpinOverlap cavityRestOverlap
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (Fin.last n)),Finset.card_univ,
    Fintype.card_fin,Nat.add_sub_cancel]
  congr 1
  have h1:=Finset.sum_erase_add (Finset.univ:Finset (Fin (n+1)))
    (fun i=>Paper.spinSign (σ i)*Paper.spinSign (τ i)) (Finset.mem_univ (Fin.last n))
  have h2:=Fin.sum_univ_castSucc (fun i:Fin (n+1)=>Paper.spinSign (σ i)*Paper.spinSign (τ i))
  linarith

 theorem followupCavityCpp_eq_psi_four_sub_product (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure)
    (a u : ℝ) (hu : u∈Icc (0:ℝ) 1) (p : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a u hu p=
      cavityCppPsiFour (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p-
      cavityCppPsiEpsilon (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p*
      cavityCppPsiTau (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p := by
  rw [followupCavityCpp_eq_four_descendants]
  simp only [cavityCppPsiFour,cavityCppPsiEpsilon,cavityCppPsiTau,cavityCppSelectedOverlap_eq_rest]

end QuantitativeFollowup
