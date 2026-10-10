module
public import QuantitativePaper.VectorTerminalHessianLower
public import QuantitativePaper.VectorGaussianLowerPropagation
public import QuantitativeFollowup.InverseFamily

@[expose] public section

/-! Explicit exponential inverse-Hessian domination for the actual finite
recursion. Constants may depend on the finite partition, as permitted for
bounded localization; no inverse-growth premise is supplied. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000

def vectorFiniteHessianLowerConstant (n : ℕ) {k : ℕ} (s : RSBScheme k) (β t : ℝ) : ℕ→ℝ
  | 0 => 1/((n : ℝ)*(Fintype.card (Configuration n) : ℝ))
  | j+1 => vectorFiniteHessianLowerConstant n s β t j*
      vectorGaussianLowerCoefficient n ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
        (s.m (k+1-j)) (Real.sqrt (n : ℝ)).toNNReal (2*Real.sqrt (n : ℝ))

theorem vectorFiniteHessianLowerConstant_pos {n k : ℕ} (hn : 0<n)
    (s : RSBScheme k) (β t : ℝ) (j : ℕ) : 0<vectorFiniteHessianLowerConstant n s β t j := by
  induction j with
  | zero => unfold vectorFiniteHessianLowerConstant;positivity
  | succ j ih => exact mul_pos ih (vectorGaussianLowerCoefficient_pos _ _ _ _ _)

theorem vectorObservableSecondResponse_field_exponential_lower {n k : ℕ} (hn : 0<n)
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x w : Field n) :
    vectorFiniteHessianLowerConstant n s β t j*
      Real.exp (-2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖))*‖w‖^2 ≤
      vectorObservableSecondResponse s β t p (fieldDot w) j 0 x := by
  induction j generalizing x with
  | zero =>
    have h:=vectorTerminalHessian_exponential_lower s hn β t p x w
    rw [vectorFieldHessian_quadratic_eq_secondResponse] at h
    simpa only [vectorFiniteHessianLowerConstant,div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using h
  | succ j ih =>
    let f:=vectorPerturbedRecursion s β t p (fieldDot w) j 0
    let v:=vectorObservableResponse s β t p (fieldDot w) j 0
    let H:=vectorObservableSecondResponse s β t p (fieldDot w) j 0
    let c:=(1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m:=s.m (k+1-j)
    let R:ℝ≥0:=(Real.sqrt (n : ℝ)*‖w‖).toNNReal
    have hB (σ : Configuration n) : |fieldDot w σ|≤R:=by
      rw [show (R : ℝ)=Real.sqrt (n : ℝ)*‖w‖ from
        Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      exact abs_fieldDot w σ
    have hf:=vectorPerturbedRecursion_lipschitz s β t p (fieldDot w) j 0
    have hH : Measurable H:=(measurable_vectorObservableSecondResponse s β t p (fieldDot w) j).comp
      (measurable_const.prodMk measurable_id)
    have hv : Measurable v:=(measurable_vectorObservableResponse s β t p (fieldDot w) j).comp
      (measurable_const.prodMk measurable_id)
    let d:=vectorFiniteHessianLowerConstant n s β t j*
      Real.exp (-2*vectorDisorderEnvelope n β t p)*‖w‖^2
    let K:=2*Real.sqrt (n : ℝ)
    have hd : 0≤d:=by
      dsimp [d]
      exact mul_nonneg (mul_nonneg (vectorFiniteHessianLowerConstant_pos hn s β t j).le
        (Real.exp_pos _).le) (sq_nonneg _)
    have hK : 0≤K:=by dsimp [K];positivity
    have hlower (y : Field n) : d*Real.exp (-K*‖y‖)≤H y := by
      have heq : d*Real.exp (-K*‖y‖)=vectorFiniteHessianLowerConstant n s β t j*
          Real.exp (-2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖y‖))*‖w‖^2 := by
        rw [show -2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖y‖)=
          -2*vectorDisorderEnvelope n β t p+(-K*‖y‖) by dsimp [K];ring,Real.exp_add]
        dsimp only [d]
        ring
      rw [heq]
      exact ih y
    have hP:=vectorStepResponse_exponential_lower f H _ hf hH (observableSecondBound R j)
      (fun z=>abs_vectorObservableSecondResponse_le s β t p (fieldDot w) R hB j 0 z)
      d K hd hK hlower c m x
    have hV:=vectorStepResponse_variance_nonneg f v _ hf hv R
      (fun z=>abs_vectorObservableResponse_le s β t p (fieldDot w) R hB j 0 z) c m x
    have hm : 0 ≤ m :=s.m_nonneg (Nat.sub_le _ _)
    have hAdd:=hP.trans (le_add_of_nonneg_right (mul_nonneg hm hV))
    change _ ≤vectorStepResponse c m f H x+m*(vectorStepResponse c m f (fun z=>v z^2) x-
      (vectorStepResponse c m f v x)^2)
    convert hAdd using 1
    rw [vectorFiniteHessianLowerConstant]
    rw [show -2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖)=
      -2*vectorDisorderEnvelope n β t p+(-K*‖x‖) by dsimp [K];ring,Real.exp_add]
    dsimp only [d,K,c,m]
    ring

theorem vectorFiniteHessian_exponential_lower {n k : ℕ} (hn : 0<n)
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x w : Field n) :
    vectorFiniteHessianLowerConstant n s β t j*
      Real.exp (-2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖))*‖w‖^2 ≤
      inner ℝ w (vectorFieldHessian s β t p j x w) := by
  rw [vectorFieldHessian_quadratic_eq_secondResponse]
  exact vectorObservableSecondResponse_field_exponential_lower hn s β t p j x w

theorem norm_inverse_vectorFiniteHessian_le {n k : ℕ} (hn : 0<n)
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    ‖Ring.inverse (vectorFieldHessian s β t p j x)‖ ≤
      (vectorFiniteHessianLowerConstant n s β t j)⁻¹*
        Real.exp (2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖)) := by
  have h:=QuantitativeFollowup.norm_ringInverse_le_of_coercive (vectorFieldHessian s β t p j x)
    (vectorFiniteHessianLowerConstant n s β t j*
      Real.exp (-2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖)))
    (mul_pos (vectorFiniteHessianLowerConstant_pos hn s β t j) (Real.exp_pos _))
    (vectorFiniteHessian_exponential_lower hn s β t p j x)
  convert h using 1
  rw [mul_inv_rev,neg_mul,Real.exp_neg,inv_inv]
  ring

end QuantitativePaper
