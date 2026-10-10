module
public import FourPapersCommon.SquaredResponseCoercivity

@[expose] public section

/-! Uniform positive denominator envelopes for the actual squared
response. This form can pass through weak approximation and Fatou without
asserting differentiability of the limiting functional. -/
noncomputable section
namespace FourPapersCommon

theorem squared_response_upper_envelope (rho A delta₀ delta signal B d : ℝ)
    (hrho : 0 < rho) (hA : 0 ≤ A) (hdelta₀ : 0 ≤ delta₀) (hdelta : delta₀ ≤ delta)
    (hB : 0 < B) (hd : 0 < d) (hsignal : A*delta/2 ≤ rho*signal) :
    0 < B+2*d*delta ∧
      (rho*A^2/72*min (delta₀^2/B) (delta₀/d))*(B+2*d*delta) ≤ rho^3*signal^2 := by
  have hdeltaN : 0 ≤ delta := hdelta₀.trans hdelta
  have hY : 0 < B+2*d*delta := by positivity
  refine ⟨hY,?_⟩
  let F := rho^3*signal^2/(B+2*d*delta)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hresponse : rho*(rho*signal)^2 ≤ F*(B+2*d*delta) := by
    dsimp only [F]
    rw [div_mul_cancel₀ _ hY.ne']
    ring_nf
    exact le_rfl
  have hh := squared_response_coercivity F rho A delta (rho*signal) (B+2*d*delta) B d
    hF hrho hA hdeltaN hB hd hsignal hresponse le_rfl
  have hmono := coercivity_min_monotone B d hB hd hdelta₀ hdelta
  have hfactor : 0 ≤ rho*A^2/72 := by positivity
  have hh' := (mul_le_mul_of_nonneg_left hmono hfactor).trans hh
  have hscaled := mul_le_mul_of_nonneg_right hh' hY.le
  dsimp only [F] at hscaled
  rwa [div_mul_cancel₀ _ hY.ne'] at hscaled

end FourPapersCommon
