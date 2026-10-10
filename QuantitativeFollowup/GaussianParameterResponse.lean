module
public import QuantitativeFollowup.GaussianScoreCovarianceResponse

@[expose] public section

/-! Gaussian differentiation when both the observable and its linear
covariance input vary. The parameter derivative below is an actual Frechet
partial derivative. Its contribution and the covariance Hessian contribution
are derived by dominated differentiation and Gaussian integration by parts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def gaussianParameterDerivative (F : ℝ → Field m → ℝ) (u : ℝ) (y : Field m) : ℝ :=
  fderiv ℝ (Function.uncurry F) (u,y) (1,0)

theorem gaussian_joint_derivative_split (F : ℝ → Field m → ℝ)
    (u : ℝ) (y v : Field m) (hf : DifferentiableAt ℝ (Function.uncurry F) (u,y)) :
    fderiv ℝ (Function.uncurry F) (u,y) (1,v)=
      gaussianParameterDerivative F u y+fderiv ℝ (F u) y v := by
  have hs := hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right u y)
  have he : fderiv ℝ (F u) y v=fderiv ℝ (Function.uncurry F) (u,y) (0,v) := by
    convert! congrArg (fun L : Field m →L[ℝ] ℝ => L v) hs.fderiv using 1
  rw [he]
  change _=fderiv ℝ (Function.uncurry F) (u,y) (1,0)+_
  rw [←map_add]
  simp only [Prod.mk_add_mk,add_zero,zero_add]

theorem hasDerivAt_gaussian_parameter_input (F : ℝ → Field m → ℝ)
    (A B : ℝ → Field n →L[ℝ] Field m) (u : ℝ) (x : Field m) (z : Field n)
    (hA : HasDerivAt A (B u) u)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (u,x+A u z)) :
    HasDerivAt (fun v => F v (x+A v z))
      (gaussianParameterDerivative F u (x+A u z)+fderiv ℝ (F u) (x+A u z) (B u z)) u := by
  have hs : HasDerivAt (fun v => x+A v z) (B u z) u := by
    simpa only [zero_add,map_zero,add_zero] using
      ((hA.clm_apply (hasDerivAt_const u z)).const_add x)
  exact (hF.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk hs)).congr_deriv
    (gaussian_joint_derivative_split F u (x+A u z) (B u z) hF)

theorem gaussianParameterDerivative_input_bound (F : ℝ → Field m → ℝ)
    (A : Field n →L[ℝ] Field m) (u : ℝ) (x : Field m) (C R K : ℝ≥0)
    (hF : ∀ y,‖gaussianParameterDerivative F u y‖ ≤ C*Real.exp (R*‖y‖))
    (hA : ‖A‖ ≤ K) (z : Field n) :
    ‖gaussianParameterDerivative F u (x+A z)‖ ≤ C*Real.exp (R*‖x‖)*Real.exp ((R*K)*‖z‖) := by
  apply (hF _).trans
  have hn : ‖x+A z‖ ≤ ‖x‖+(K : ℝ)*‖z‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl ((A.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))))
  have he := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn R.coe_nonneg)) C.coe_nonneg
  simpa only [mul_add,Real.exp_add,mul_assoc] using he

/-- The genuine parameter-plus-covariance derivative of an actual Gaussian
mean. All hypotheses are local differentiability, measurability, and explicit
exponential-growth bounds; no integral response conclusion is assumed. -/
theorem hasDerivAt_gaussianLinearParameterMean (F : ℝ → Field m → ℝ)
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (d : ∀ u,VectorHeatDatum (F u))
    (hF : ∀ u∈S,∀ y,DifferentiableAt ℝ (Function.uncurry F) (u,y))
    (hAB : ∀ u∈S,HasDerivAt A (B u) u)
    (C R K L : ℝ≥0)
    (hA : ∀ u∈S,‖A u‖ ≤ K) (hB : ∀ u∈S,‖B u‖ ≤ L)
    (hfirst : ∀ u∈S,∀ y,‖fderiv ℝ (F u) y‖ ≤ C*Real.exp (R*‖y‖))
    (hpartial : ∀ u∈S,∀ y,‖gaussianParameterDerivative F u y‖ ≤ C*Real.exp (R*‖y‖))
    (x : Field m)
    (hmeas : AEStronglyMeasurable (fun z => gaussianParameterDerivative F a (x+A a z)) (fieldGaussian n)) :
    HasDerivAt (fun u => gaussianLinearMean (F u) (A u) x)
      ((∫ z,gaussianParameterDerivative F a (x+A a z) ∂fieldGaussian n)+
        ∫ z,∑ i : Fin n,vectorHessian (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) ∂fieldGaussian n) a := by
  have ha : a∈S := mem_of_mem_nhds hS
  let pbound : Field n → ℝ := fun z => C*Real.exp (R*‖x‖)*Real.exp ((R*K)*‖z‖)
  let dbound : Field n → ℝ := fun z => L*C*Real.exp (R*‖x‖)*Real.exp ((R*K+1)*‖z‖)
  have hip : Integrable pbound (fieldGaussian n) :=
    (SYK.integrable_exp_mul_norm (ι := Fin n) (R*K)).const_mul _
  have hid : Integrable dbound (fieldGaussian n) :=
    (SYK.integrable_exp_mul_norm (ι := Fin n) (R*K+1)).const_mul _
  have hpd (u : ℝ) (hu : u∈S) (z : Field n) :
      ‖gaussianParameterDerivative F u (x+A u z)‖ ≤ pbound z :=
    gaussianParameterDerivative_input_bound F (A u) u x C R K (hpartial u hu) (hA u hu) z
  have hdd (u : ℝ) (hu : u∈S) (z : Field n) :
      ‖fderiv ℝ (F u) (x+A u z) (B u z)‖ ≤ dbound z := by
    have ht : ‖fderiv ℝ (F u) (x+A u z)‖ ≤ C*Real.exp (R*‖x‖)*Real.exp ((R*K)*‖z‖) := by
      apply (hfirst u hu _).trans
      have hn : ‖x+A u z‖ ≤ ‖x‖+(K : ℝ)*‖z‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((A u).le_opNorm z |>.trans
          (mul_le_mul_of_nonneg_right (hA u hu) (norm_nonneg _))))
      have he := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn R.coe_nonneg)) C.coe_nonneg
      simpa only [mul_add,Real.exp_add,mul_assoc] using he
    have hz : ‖z‖ ≤ Real.exp ‖z‖ := (by linarith : ‖z‖ ≤ ‖z‖+1).trans (Real.add_one_le_exp _)
    have hb : ‖B u z‖ ≤ L*Real.exp ‖z‖ := ((B u).le_opNorm z).trans
      (mul_le_mul (hB u hu) hz (norm_nonneg _) L.coe_nonneg)
    calc
      _ ≤ ‖fderiv ℝ (F u) (x+A u z)‖*‖B u z‖ := (fderiv ℝ (F u) _).le_opNorm _
      _ ≤ (C*Real.exp (R*‖x‖)*Real.exp ((R*K)*‖z‖))*(L*Real.exp ‖z‖) :=
        mul_le_mul ht hb (norm_nonneg _) (by positivity)
      _ = dbound z := by dsimp only [dbound];rw [add_mul,one_mul,Real.exp_add];ring
  have hipa : Integrable (fun z => gaussianParameterDerivative F a (x+A a z)) (fieldGaussian n) :=
    hip.mono' hmeas (.of_forall (hpd a ha))
  have hiDa := (integral_gaussianLinear_covariance_response (d a) (A a) (B a) x).1
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => F u (x+A u z))
    (F' := fun u z => gaussianParameterDerivative F u (x+A u z)+fderiv ℝ (F u) (x+A u z) (B u z))
    (bound := fun z => pbound z+dbound z) (s := S) hS
    (.of_forall fun u => ((d u).regularity.continuous.comp
      (continuous_const.add (A u).continuous)).aestronglyMeasurable)
    (integrable_gaussianLinear_input (d a) (A a) x)
    (hmeas.add hiDa.aestronglyMeasurable)
    (.of_forall fun z u hu => (norm_add_le _ _).trans (add_le_add (hpd u hu z) (hdd u hu z)))
    (hip.add hid) (.of_forall fun z u hu => hasDerivAt_gaussian_parameter_input F A B u x z
      (hAB u hu) (hF u hu _))).2
  apply hd.congr_deriv
  rw [integral_add hipa hiDa,(integral_gaussianLinear_covariance_response (d a) (A a) (B a) x).2]

end QuantitativeFollowup
