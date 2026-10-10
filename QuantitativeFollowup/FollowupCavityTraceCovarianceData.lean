module
public import QuantitativeFollowup.FollowupCavityRestTraceDiagonal
public import QuantitativeFollowup.FollowupCavityRemainderIntegral
public import QuantitativeFollowup.FollowupCavityDecouplingProcess

@[expose] public section

/-! The structural data of the printed integrated linear-response formula,
specialized to the actual rest model and its actual scalar variance d.
The covariance, trace and nonnegative penalty are constructed objects;
no differentiated Cpp identity is assumed or asserted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 abbrev followupCavityCovarianceMinus (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) :=
  cavityRestCovarianceFull (followupCavityRestSpinModel n β ρ hβ hρ) μ a

 abbrev followupCavityVarianceMinus (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) :=
  cavityRestVariance (followupCavityRestSpinModel n β ρ hβ hρ) μ a

 abbrev followupCavityTraceMinus (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :=
  cavityRestResponseTrace (followupCavityRestSpinModel n β ρ hβ hρ)
    (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
    μ a ha hμ

 abbrev followupCavityPenalty (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) :=
  cavityResidualPenalty (followupCavityScalarBeta n β ρ)
    (followupCavityRestSpinModel n β ρ hβ hρ) μ a

 theorem followup_cavity_covariance_trace_data (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    IsPositiveTraceClass (followupCavityCovarianceMinus n β ρ hβ hρ μ a) ∧
    HasFinitePositiveTrace (followupCavityCovarianceMinus n β ρ hβ hρ μ a)
      (followupCavityVarianceMinus n β ρ hβ hρ μ a) ∧
    (0≤followupCavityVarianceMinus n β ρ hβ hρ μ a ∧
      followupCavityVarianceMinus n β ρ hβ hρ μ a≤1) ∧
    (∀x : Lp ℝ 2 (parisiFreeMeasure μ a),
      followupCavityCovarianceMinus n β ρ hβ hρ μ a x∈endpointFixedL2 (parisiFreeMeasure μ a)) ∧
    followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ=
      (∫p : Paper.Overlap,scalarResponseOperator (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ a
        (cavityRestCovarianceColumn (followupCavityRestSpinModel n β ρ hβ hρ) μ a p) p
        ∂parisiFreeMeasure μ a) ∧
    0≤followupCavityPenalty n β ρ hβ hρ μ a ∧
    (1/2:ℝ)*(∫p,cavityResponseFutureRemainder (followupCavityScalarBeta n β ρ)
      (followupCavityRestSpinModel n β ρ hβ hρ) μ a p∂parisiFreeMeasure μ a)=
      -followupCavityPenalty n β ρ hβ hρ μ a/2 := by
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  have hb : β0≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  exact ⟨cavityRestCovarianceFull_isPositiveTraceClass D μ a,
    cavityRestCovarianceFull_trace D μ a hone,
    ⟨cavityRestVariance_nonneg D μ a,cavityRestVariance_le_one D μ a ha hone⟩,
    cavityRestCovarianceFull_range D μ a hone,
    cavityRestResponseTrace_eq_kernel_diagonal D β0 hb μ a ha hμ hone,
    cavityResidualPenalty_nonneg β0 D μ a,
    cavityResponseFutureRemainder_half_integral β0 hb D μ a⟩

end QuantitativeFollowup
