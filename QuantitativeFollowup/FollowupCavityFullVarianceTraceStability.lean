module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceOrder
public import QuantitativeFollowup.ScalarMinimizerStability

@[expose] public section

/-! The physical cavity scalar coefficient agrees with the completed
system coefficient, and the proved reference-error criterion gives the
source's actual quadratic operator-order hypothesis. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem followupCavityD_eq_completed_scalar_coefficient (n : ℕ) (β ρ : ℝ) :
    followupCavityD n β ρ = followupScalarCoefficient (n+1) β ρ := by
  rw [followupCavityD_identity]
  simp only [followupScalarCoefficient, Nat.cast_add, Nat.cast_one]

theorem followupCavity_quadratic_order_of_reference_error (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 1 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (hstable : scalarOperatorStabilityError β μ (followupScalarCoefficient (n+1) β ρ) ≤ ρ/4) :
    ∃ε ∈ Icc (0 : ℝ) (ρ/4), ∀f : endpointFixedL2 (parisiFreeMeasure μ a),
      inner ℝ f (scalarResponseL2Operator (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ (zero_lt_one.trans hβ) hρ).ne' μ a ha hμ f) ≤
          (1+ε)*‖f‖^2 := by
  let ε := scalarOperatorStabilityError β μ (followupCavityD n β ρ)
  have hε0 : 0 ≤ ε := scalarOperatorStabilityError_nonneg β (zero_lt_one.trans hβ) μ _
  have hε1 : ε ≤ ρ/4 := by
    simpa only [ε, followupCavityD_eq_completed_scalar_coefficient] using hstable
  refine ⟨ε, ⟨hε0, hε1⟩, ?_⟩
  intro f
  simpa only [followupCavityScalarBeta, ε] using scalar_reference_operator_stability β hβ μ
    (followupCavityD n β ρ) (followupCavityD_window n hn β ρ ⟨hρ.1.le, hρ.2⟩) a ha hμ f

end QuantitativeFollowup
