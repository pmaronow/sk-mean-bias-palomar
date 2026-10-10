module
public import QuantitativePaper.VectorFieldConditionalVariance
public import QuantitativePaper.VectorFiniteCellPDE
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

@[expose] public section

/-! Dimension-only bounds for the actual finite vector gradient and Hessian.
The operator bound is derived from the genuine terminal conditional variance. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem vectorMagnetization_eq_gradient {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    vectorMagnetization s β t p j x=gradient (vectorRecursion s β t p j) x := by
  apply PiLp.ext
  intro i
  rw [gradient_euclidean_coordinate]
  have hd := hasDerivAt_on_affine_line (vectorRecursion s β t p j)
    ((contDiff_vectorRecursion_field s β t p j).of_le (by simp))
    x (EuclideanSpace.single i (1 : ℝ)) 0
  simpa only [zero_smul,add_zero] using
    (hasDerivAt_vectorRecursion_coordinate s β t p j x i).unique hd

theorem vectorFieldHessian_isSymmetric {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    (vectorFieldHessian s β t p j x).IsSymmetric := by
  intro u v
  change inner ℝ (vectorFieldHessian s β t p j x u) v=
    inner ℝ u (vectorFieldHessian s β t p j x v)
  rw [vectorFieldHessian,inner_hessianOperator]
  conv_rhs => rw [real_inner_comm]
  rw [inner_hessianOperator]
  exact ((contDiff_vectorRecursion_field s β t p j).contDiffAt.isSymmSndFDerivAt (by simp)).eq u v

theorem vectorFieldHessian_quadratic_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x w : Field n) :
    |inner ℝ (vectorFieldHessian s β t p j x w) w| ≤ (n : ℝ)*‖w‖^2 := by
  let R : ℝ≥0 := (Real.sqrt (n : ℝ)*‖w‖).toNNReal
  have hb (σ : Configuration n) : |fieldDot w σ| ≤ R := by
    rw [show (R : ℝ)=Real.sqrt (n : ℝ)*‖w‖ from Real.coe_toNNReal _ (by positivity)]
    exact abs_fieldDot w σ
  have hC := abs_vectorObservableCovariance_le s β t p (fun σ => fieldDot w σ) R hb j 0 x
  have hH := (vectorFieldHessian_covariance_quadratic_bounds s β t p j x w).2
  rw [real_inner_comm,abs_of_nonneg (vectorFieldHessian_quadratic_nonneg s β t p j x w)]
  calc
    _ ≤ vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x := hH
    _ ≤ |vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x| := le_abs_self _
    _ ≤ (R : ℝ)^2 := hC
    _ = _ := by
      rw [show (R : ℝ)=Real.sqrt (n : ℝ)*‖w‖ from Real.coe_toNNReal _ (by positivity),mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg n)]

theorem norm_vectorFieldHessian_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    ‖vectorFieldHessian s β t p j x‖ ≤ (n : ℝ) := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _
    (vectorFieldHessian_isSymmetric s β t p j x)]
  apply ciSup_le
  intro w
  simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,abs_div,abs_sq]
  have hh := vectorFieldHessian_quadratic_bound s β t p j x w
  by_cases hw : w=0
  · simp [hw]
  · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).mpr hh

theorem hasFDerivAt_gradient_hessianOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E→ℝ)
    (hf : ContDiff ℝ 2 f) (x : E) :
    HasFDerivAt (gradient f) (hessianOperator f x) x := by
  have hh := ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp
    x ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).differentiable (by norm_num) x).hasFDerivAt
  convert hh using 1
  · funext y
    rfl
  · rfl

theorem vectorMagnetization_lipschitz {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) :
    LipschitzWith (n : ℝ≥0) (vectorMagnetization s β t p j) := by
  have he : vectorMagnetization s β t p j=gradient (vectorRecursion s β t p j) :=
    funext (vectorMagnetization_eq_gradient s β t p j)
  rw [he]
  have hd (x : Field n) := hasFDerivAt_gradient_hessianOperator
    (vectorRecursion s β t p j) ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) x
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).fderiv,←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_natCast]
  exact norm_vectorFieldHessian_le s β t p j x

end QuantitativePaper
