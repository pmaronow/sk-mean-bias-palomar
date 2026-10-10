module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarCoefficientAliases
public import QuantitativeFollowup.FollowupCavitySignedResponseDiagonalIntegral

@[expose] public section

/-! The diagonal scalar coefficients are the actual variance of the
magnetization square. Terminal signs are removed using the genuine
whole-Brownian-past conditional spin expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem scalarResponseKernel5_diagonal_eq_cavitySignedScalarVariance (β : ℝ)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    scalarResponseKernel5 β μ p p 0 = cavitySignedScalarVariance β μ p := by
  let X := fun ω : Paper.BrownianSample => M β μ p ω^2
  have hX : MemLp X 2 canonicalBrownianMeasure :=
    MemLp.of_bound ((measurable_M β μ p p.property).pow_const 2).aestronglyMeasurable 1
      (.of_forall fun ω => by
        change ‖M β μ p ω^2‖ ≤ 1
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ p ω))
  have hi : Integrable (fun ω=>X ω*X ω) canonicalBrownianMeasure := hX.integrable_mul hX
  have hic := (hX.const_mul (Gamma β μ p)).integrable one_le_two
  calc
    _ = ∫ ω, X ω*X ω-Gamma β μ p*X ω ∂canonicalBrownianMeasure := by
      apply integral_congr_ae
      exact .of_forall fun ω => by dsimp only [scalarCenteredSquare, X]; ring
    _ = (∫ ω, X ω*X ω ∂canonicalBrownianMeasure) -
        Gamma β μ p*(∫ ω, X ω ∂canonicalBrownianMeasure) := by
      rw [integral_sub hi hic, integral_const_mul]
    _ = cavitySignedScalarVariance β μ p := by
      rw [cavitySignedScalarVariance, variance_eq_sub hX]
      simp only [X, Pi.pow_apply, pow_two, Gamma]

theorem integral_scalarMarkedSpinLaw_centered_mean_sign_eq_variance (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (∫ z, scalarCenteredSquare β μ p z.1*M β μ p z.1*Paper.spinSign z.2
      ∂scalarMarkedSpinLaw β hβ μ) = cavitySignedScalarVariance β μ p := by
  let Z := fun ω => scalarCenteredSquare β μ p ω*M β μ p ω
  have hZ : Measurable[canonicalBrownianFiltration (p : ℝ).toNNReal] Z := by
    have hM := measurable_scalarM_past β hβ μ p
    exact ((hM.pow_const 2).sub measurable_const).mul hM
  have hb : ∀ ω, ‖Z ω‖ ≤ 1 := fun ω => by
    dsimp only [Z]
    rw [norm_mul]
    exact (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω)
      (scalar_M_norm_le_one β μ p ω) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he := integral_scalarMarkedSpinLaw_past_sign β hβ μ p Z hZ hb
  calc
    _ = ∫ z, Z z.1*M β μ p z.1 ∂scalarMarkedSpinLaw β hβ μ := he
    _ = ∫ z, scalarCenteredSquare β μ p z.1*M β μ p z.1^2
        ∂scalarMarkedSpinLaw β hβ μ := by
      apply integral_congr_ae
      exact .of_forall fun z => by dsimp only [Z]; ring
    _ = scalarResponseKernel5 β μ p p 0 :=
      integral_scalarMarkedSpinLaw_sample β hβ μ _
        (((((measurable_M β μ p p.property).pow_const 2).sub measurable_const)).mul
          ((measurable_M β μ p p.property).pow_const 2))
    _ = _ := scalarResponseKernel5_diagonal_eq_cavitySignedScalarVariance β μ p

end QuantitativeFollowup
