module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFeatures
public import Paper.ParisiSpatialBounds

@[expose] public section

/-! The scalar factor of the zero-coupling posterior is the genuine finite
Parisi gradient, including zero masses and repeated nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityScalarDepthKernel_gradient_average (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (x : ℝ) :
    (∫ y, parisiFDeriv s β j y ∂cavityScalarDepthKernel s β j x) = parisiFDeriv s β (j+1) x := by
  let m := anisotropicSchemeMass s j
  let v := β^2*(s.q (k+2-j)-s.q (k+1-j))
  let c := Real.exp (m*Real.log 2)
  have hc : c ≠ 0 := Real.exp_ne_zero _
  have hex (z : ℝ) : Real.exp (m*cavityScalarFinite s β j (x+Real.sqrt v*z)) =
      c*Real.exp (m*parisiF s β j (x+Real.sqrt v*z)) := by
    rw [cavityScalarFinite,mul_add,Real.exp_add]
  rw [cavityScalarDepthKernel_apply,
    integral_map (by fun_prop) ((parisiF_C2_props s β j).2.1).aestronglyMeasurable,
    integral_tilted]
  change (∫ z, (Real.exp (m*cavityScalarFinite s β j (x+Real.sqrt v*z)) /
    (∫ z,Real.exp (m*cavityScalarFinite s β j (x+Real.sqrt v*z)) ∂gaussianReal 0 1)) *
      parisiFDeriv s β j (x+Real.sqrt v*z) ∂gaussianReal 0 1) = _
  simp_rw [hex]
  rw [integral_const_mul]
  have he (z : ℝ) :
      (c*Real.exp (m*parisiF s β j (x+Real.sqrt v*z)) /
        (c*(∫ z,Real.exp (m*parisiF s β j (x+Real.sqrt v*z)) ∂gaussianReal 0 1))) *
        parisiFDeriv s β j (x+Real.sqrt v*z) =
      (parisiFDeriv s β j (x+Real.sqrt v*z)*Real.exp (m*parisiF s β j (x+Real.sqrt v*z))) /
        (∫ z,Real.exp (m*parisiF s β j (x+Real.sqrt v*z)) ∂gaussianReal 0 1) := by
    rw [mul_div_mul_left _ _ hc]
    ring
  simp_rw [he]
  rw [integral_div]
  rfl

theorem cavityScalarFiniteFeatureMean_sign (s : RSBScheme k) (β : ℝ)
    (j : ℕ) : cavityScalarFiniteFeatureMean s β j Paper.spinSign = parisiFDeriv s β j := by
  induction j with
  | zero =>
      funext x
      rw [cavityScalarFiniteFeatureMean_zero,integral_scalarSpinLaw_sign]
      simp only [parisiFDeriv,Real.tanh_eq_sinh_div_cosh]
  | succ j ih =>
      funext x
      rw [cavityScalarFiniteFeatureMean_succ,ih,cavityScalarDepthKernel_gradient_average]

theorem cavityFiniteIncidentFeature_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (j : ℕ)
    (f : Configuration n → ℝ) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) s j
        (fun σ => f (cavityRestConfiguration σ) * Paper.spinSign (σ (Fin.last n))) P =
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j f
        (cavityRestParameterProjection n P) *
      parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) := by
  rw [cavityFiniteJointFeature_zero,cavityScalarFiniteFeatureMean_sign]

end QuantitativeFollowup
