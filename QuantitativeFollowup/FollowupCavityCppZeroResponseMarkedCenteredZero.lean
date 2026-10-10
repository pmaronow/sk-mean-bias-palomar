module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap
public import QuantitativeFollowup.ScalarResponseRootCancellation

@[expose] public section

/-! The actual scalar/rest centered product has zero expectation under
the complete marked independent-endpoint law. This removes the constant
part of the normalized density response without any covariance premise. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

 theorem centeredZero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integral_cavityZeroMarked_centered_self_scalar_zero
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavitySignedResponseCenteredSelfOverlap D μ a p
      (cavityZeroMarkedSampleSplit n z).1.1 *
      scalarCenteredSquare B μ p (cavityZeroMarkedSampleSplit n z).2.1
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 centeredZero_mem) μ a)=0 :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
  have hF : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1) :=
    hcenter.comp measurable_fst
  have hG : Measurable (scalarCenteredSquare B μ p) :=
    ((FRSB.measurable_M B μ p p.property).pow_const 2).sub measurable_const
  have hprod:=integral_cavityZeroMarked_product μ n β ρ hβ hρ a
    (fun z=>cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
    (fun z=>scalarCenteredSquare B μ p z.1) hF (hG.comp measurable_fst)
  calc
    _ = (∫z,cavitySignedResponseCenteredSelfOverlap D μ a p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a)*
        (∫z,scalarCenteredSquare B μ p z.1
          ∂scalarMarkedSpinLaw B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ) := hprod
    _ = 0 :=by
      rw [integral_scalarMarkedSpinLaw_sample B
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ _ hG,
        integral_scalarCenteredSquare B μ p,mul_zero]

end QuantitativeFollowup
