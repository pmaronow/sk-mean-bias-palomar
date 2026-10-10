module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceExpectation
public import FourPapersCommon.FiniteStateCascadeExpectationTransport

@[expose] public section

/-! Actual isolated-spin and rest observables at every retained field,
with the rest disorder and covariance held fixed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets OverlapPaper
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteEnergyFeatureMean_at_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (f : QuantitativePaper.Configuration n→ℝ) (P : AnisotropicParameter n) :
    cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) j (WithLp.toLp 2 f) (anisotropicEnergyMap D P)=
      anisotropicFiniteFeatureMean D s j f P :=by
  rw [cavityFiniteEnergyFeatureMean_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
  rfl

def cavityLastVarianceRestOverlap (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (P : AnisotropicParameter n) : ℝ :=
  (n:ℝ)⁻¹*∑i : Fin n,(anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ)
    s j (fun σ=>Paper.spinSign (σ i)) P)^2

theorem measurable_cavityLastVarianceRestOverlap (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) :
    Measurable (cavityLastVarianceRestOverlap s n β ρ hβ hρ j) :=by
  exact (Finset.measurable_sum Finset.univ (fun i _=>
    (measurable_anisotropicFiniteFeatureMean _ s j (fun σ=>Paper.spinSign (σ i))).pow_const 2)).const_mul _

theorem cavityLastVarianceLastFieldSquare_at_parameter (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (j : ℕ)
    (P : AnisotropicParameter (n+1)) :
    cavityFixedRowLastFieldSquare (cavityLastVarianceModel n β ρ hβ hρ b hb) s j
      (anisotropicEnergyMap (cavityLastVarianceModel n β ρ hβ hρ b hb) P)=
      (parisiFDeriv s (Real.sqrt b) j (P (Sum.inr (Fin.last n))))^2 :=by
  rw [cavityFixedRowLastFieldSquare,cavityFiniteEnergyFeatureMean_at_parameter,
    cavityLastVariance_finiteSpinFeature]

theorem cavityLastVarianceRestFieldSquare_at_parameter (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (j : ℕ)
    (P : AnisotropicParameter (n+1)) :
    cavityFixedRowRestFieldSquare (cavityLastVarianceModel n β ρ hβ hρ b hb) s j
      (anisotropicEnergyMap (cavityLastVarianceModel n β ρ hβ hρ b hb) P)=
      cavityLastVarianceRestOverlap s n β ρ hβ hρ j (cavityRestParameterProjection n P) :=by
  unfold cavityFixedRowRestFieldSquare cavityFiniteEnergyRestOverlap cavityLastVarianceRestOverlap
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cavityFiniteEnergyFeatureMean_at_parameter]
  have ht:=cavityLastVariance_finiteRestFeature s n β ρ hβ hρ b hb j
    (fun σ=>Paper.spinSign (σ i)) P
  simpa only [cavityRestConfiguration] using congrArg (fun x : ℝ=>x^2) ht

end QuantitativeFollowup
