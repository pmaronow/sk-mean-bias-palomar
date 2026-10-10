module
public import QuantitativeFollowup.FollowupCavityDecouplingProcess
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-! The literal native cavity covariance C_pp and its genuine zero-coupling
baseline. No differentiated response is assumed here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def followupCavityCpp (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a u : ℝ) (hu : u∈Icc (0:ℝ) 1) (p : Paper.Overlap) : ℝ :=
  covariance
    (fun ω=>anisotropicProcessMagnetization (followupCavitySpinModel n β ρ hβ hρ u hu) μ p ω (Fin.last n)^2)
    (fun ω=>anisotropicSelectedMeanSquare Finset.univ
      (cavityRestFieldProjection n (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ p ω)))
    (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a)

 theorem followupCavityCpp_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a 0 ⟨le_rfl,by norm_num⟩ p=0 := by
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  let X:=cavityRestSelfOverlap R μ p
  let Y:=fun W : Paper.BrownianSample=>
    cavityScalarMagnetization β0 (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p W^2
  have hX : Measurable X :=
    (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
      ((measurable_pi_apply p).comp (measurable_cavityRestMagnetizationCurve μ n β ρ hβ hρ))
  have hY : Measurable Y :=(measurable_cavityScalarMagnetization _ _ μ p).pow_const 2
  have hXL : MemLp X 2 (anisotropicMeasureSampleLaw R μ a) :=
    MemLp.of_bound hX.aestronglyMeasurable 1 (.of_forall (cavityRestSelfOverlap_norm_le R μ p))
  have hYL : MemLp Y 2 Paper.canonicalBrownianMeasure := by
    apply MemLp.of_bound hY.aestronglyMeasurable 1
    exact .of_forall fun W=>by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (cavityScalarMagnetization_norm_le _ _ μ p W) 2).trans_eq (by norm_num)
  have hcov:= (hasLaw_cavityZeroSampleSplit μ n β ρ hβ hρ a).covariance_comp
    (f:=fun z : AnisotropicDisorderBrownianSample n×Paper.BrownianSample=>Y z.2)
    (g:=fun z : AnisotropicDisorderBrownianSample n×Paper.BrownianSample=>X z.1)
    (hY.comp measurable_snd).aemeasurable (hX.comp measurable_fst).aemeasurable
  have hz : covariance (fun z : AnisotropicDisorderBrownianSample n×Paper.BrownianSample=>Y z.2)
      (fun z=>X z.1) ((anisotropicMeasureSampleLaw R μ a).prod Paper.canonicalBrownianMeasure)=0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hXL hYL
  rw [hz] at hcov
  have hlast : (fun ω=>anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ p ω (Fin.last n)^2)=
      (fun z : AnisotropicDisorderBrownianSample n×Paper.BrownianSample=>Y z.2) ∘ cavityZeroSampleSplit n := by
    funext ω
    exact congrArg (fun x : ℝ=>x^2) (cavityLastProcessMagnetization_zero μ n β ρ hβ hρ p ω)
  have hrest : (fun ω=>anisotropicSelectedMeanSquare Finset.univ
      (cavityRestFieldProjection n (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ p ω)))=
      (fun z : AnisotropicDisorderBrownianSample n×Paper.BrownianSample=>X z.1) ∘ cavityZeroSampleSplit n := by
    funext ω
    exact congrArg (anisotropicSelectedMeanSquare Finset.univ)
      (cavityRestProcessMagnetization_zero μ n β ρ hβ hρ p ω)
  unfold followupCavityCpp
  rw [hlast,hrest]
  exact hcov

end QuantitativeFollowup
