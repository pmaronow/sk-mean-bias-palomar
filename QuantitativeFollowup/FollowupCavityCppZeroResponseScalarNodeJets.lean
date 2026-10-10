module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureAgreementScalar
public import QuantitativeFollowup.FollowupCavityDecouplingProcess
public import QuantitativeFollowup.ScalarProcessContinuity

@[expose] public section

/-! True finite scalar mean and curvature at the native original node,
including the root and repeated observations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteScalarHessian_eq_native (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (j : ℕ) (hj : j≤k+2) (x : ℝ) :
    parisiFSecond s β j x=
      Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),x) :=by
  have hd:=Paper.hasDerivAt_parisiGradient_spatial_all β (Paper.parisiSchemeMeasure s)
    (s.q (k+2-j)) x
  have he:(fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-j),y))=parisiFDeriv s β j:=
    funext (cavityFutureAgreement_scalar_gradient_node s β hβ j hj)
  rw [he] at hd
  exact ((parisiF_C2_props s β j).1.2.1 x).unique hd

theorem cavityZeroLastProcessParameter_eq_scalarState (μ : Paper.ParisiMeasure)
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample (n+1)) :
    anisotropicProcessParameter (followupCavitySpinModel n β ρ hβ hρ 0
      ⟨le_rfl,zero_le_one⟩) μ q sample (Sum.inr (Fin.last n))=
      parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
        (sample.2 (Fin.last n)) :=by
  have he:anisotropicProcessParameter (followupCavitySpinModel n β ρ hβ hρ 0
      ⟨le_rfl,zero_le_one⟩) μ q sample (Sum.inr (Fin.last n))=
      anisotropicMeasureState (followupCavitySpinModel n β ρ hβ hρ 0
        ⟨le_rfl,zero_le_one⟩) μ q sample (Fin.last n):=by
    change (0:ℝ)+anisotropicMeasureState
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample (Fin.last n)=_
    exact zero_add _
  rw [he,cavityLastMeasureState_zero μ n β ρ hβ hρ q q.property sample,
    parisiPhysicalSplitState_eq_selected _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ q]
  symm
  simpa only [Real.coe_toNNReal _ q.property.1] using
    Paper.selectedParisiItoState_eq (followupCavityScalarBeta n β ρ) 0
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ
      (t:=(q:ℝ).toNNReal) (by simpa using Real.toNNReal_le_toNNReal q.property.2)
      (sample.2 (Fin.last n))

theorem cavityFiniteScalarMean_at_native_scheme_node (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (j : ℕ) (hj : j≤k+2) (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let q:=anisotropicSchemeNode s (k+2-j) (by omega)
    parisiFDeriv s (followupCavityScalarBeta n β ρ) j
      (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q sample (Sum.inr (Fin.last n)))=
      M (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s) q
        (sample.2 (Fin.last n)) :=by
  dsimp only
  rw [cavityZeroLastProcessParameter_eq_scalarState,
    ←cavityFutureAgreement_scalar_gradient_node s _ (followupCavityScalarBeta_pos n β ρ hβ hρ) j hj]
  exact scalarGradient_physicalSplitState _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
    (Paper.parisiSchemeMeasure s) (anisotropicSchemeNode s (k+2-j) (by omega))
    (sample.2 (Fin.last n))

theorem cavityFiniteScalarHessian_at_native_scheme_node (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (j : ℕ) (hj : j≤k+2) (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let q:=anisotropicSchemeNode s (k+2-j) (by omega)
    parisiFSecond s (followupCavityScalarBeta n β ρ) j
      (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q sample (Sum.inr (Fin.last n)))=
      C (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s) q
        (sample.2 (Fin.last n)) :=by
  dsimp only
  rw [cavityZeroLastProcessParameter_eq_scalarState,
    cavityFiniteScalarHessian_eq_native s _ (followupCavityScalarBeta_pos n β ρ hβ hρ) j hj]
  exact scalarHessian_physicalSplitState _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
    (Paper.parisiSchemeMeasure s) (anisotropicSchemeNode s (k+2-j) (by omega))
    (sample.2 (Fin.last n))

end QuantitativeFollowup
