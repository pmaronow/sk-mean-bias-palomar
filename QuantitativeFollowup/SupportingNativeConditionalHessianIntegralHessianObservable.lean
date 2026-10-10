module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralHessianResponse

@[expose] public section

/-! Actual bounded compensated field Hessian observable. Its normalized
Gaussian response is the literal cell Hessian plus the cell mass times
its literal field-direction mean square. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

private theorem native_hessian_eval_eq (f : AnisotropicParameter n→ℝ)
    (hf : ContDiff ℝ ∞ f) (P V : AnisotropicParameter n) :
    fderiv ℝ (fun Q=>fderiv ℝ f Q V) P V=fderiv ℝ (fderiv ℝ f) P V V := by
  have hd : Differentiable ℝ (fderiv ℝ f):=
    (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hd P) (differentiableAt_const V),
    show fderiv ℝ (fun _ : AnisotropicParameter n=>V) P=0 from (hasFDerivAt_const V P).fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

private theorem native_translate_bounded {f : AnisotropicParameter n→ℝ}
    (hf : BoundedJets f) (c : AnisotropicParameter n) : BoundedJets (fun P=>f (c+P)) := by
  refine ⟨hf.1.comp (contDiff_const.add contDiff_id),?_⟩
  intro j
  obtain ⟨B,hB,hb⟩:=hf.2 j
  exact ⟨B,hB,fun P=>by rw [iteratedFDeriv_comp_add_left];exact hb _⟩

def nativeAnisotropicFiniteFieldHessian (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (w : Field n) (P : AnisotropicParameter n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P
    (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)

theorem boundedJets_nativeAnisotropicFiniteFieldHessian (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (w : Field n) :
    BoundedJets (nativeAnisotropicFiniteFieldHessian D s j w) := by
  have he : nativeAnisotropicFiniteFieldHessian D s j w=
      fun P=>fderiv ℝ (nativeAnisotropicFiniteFieldResponse D s j w) P (anisotropicFieldInjection n w):=by
    funext P
    exact (native_hessian_eval_eq _ (contDiff_anisotropicFinitePotential D s j) P _).symm
  rw [he]
  exact (boundedJets_nativeAnisotropicFiniteFieldResponse D s j w).fderiv_apply _

def nativeAnisotropicWhitenedJointCompensatedHessian (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (g : AnisotropicDisorder n) (w : Field n)
    (z : VectorParameter n) : ℝ :=
  let P:=anisotropicDisorderInjection n g+anisotropicWhiteJointInput D z
  nativeAnisotropicFiniteFieldHessian D s (k+1-i) w P+
    s.m i*(nativeAnisotropicFiniteFieldResponse D s (k+1-i) w P)^2

theorem boundedJets_nativeAnisotropicWhitenedJointCompensatedHessian
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ)
    (g : AnisotropicDisorder n) (w : Field n) :
    BoundedJets (nativeAnisotropicWhitenedJointCompensatedHessian D s i g w) := by
  have hG:=boundedJets_nativeAnisotropicFiniteFieldResponse D s (k+1-i) w
  have hH:=boundedJets_nativeAnisotropicFiniteFieldHessian D s (k+1-i) w
  have hh:=native_translate_bounded (hH.add ((hG.mul hG).const_mul (s.m i)))
    (anisotropicDisorderInjection n g)
  unfold nativeAnisotropicWhitenedJointCompensatedHessian
  simp only [pow_two]
  exact hh.comp_linear (anisotropicWhiteJointInput D)

def nativeAnisotropicCompensatedHessianResponseData (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (g : AnisotropicDisorder n) (w : Field n) :
    VectorJointResponseTestData (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g)
      (nativeAnisotropicWhitenedJointCompensatedHessian D s i g w) := by
  let h:=boundedJets_nativeAnisotropicWhitenedJointCompensatedHessian D s i g w
  exact anisotropicWhitenedFiniteJointResponseData D s (k+1-i) g {
    regularity:=h.1.of_le (by simp)
    bounds:=fun r=>Classical.choose (h.2 r)
    bounds_nonneg:=fun r=>(Classical.choose_spec (h.2 r)).1
    jets:=fun r _=>(Classical.choose_spec (h.2 r)).2 }

theorem nativeAnisotropic_compensated_hessian_response (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤k+1)
    (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1))) (y : Field n) :
    vectorStepResponse (s.q (i+1)-q) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun z=>nativeAnisotropicWhitenedJointCompensatedHessian D s i g w (0,z)) y=
    fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q))
      (anisotropicDisorderInjection n g+anisotropicUnitInput D y)
      (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)+
    s.m i*(fderiv ℝ (anisotropicFiniteTailPotential D s q)
      (anisotropicDisorderInjection n g+anisotropicUnitInput D y) (anisotropicFieldInjection n w))^2 := by
  let f:=anisotropicWhitenedFinitePotential D s (k+1-i) g
  let G:=fun z=>nativeAnisotropicFiniteFieldResponse D s (k+1-i) w
    (anisotropicDisorderInjection n g+anisotropicUnitInput D z)
  let H:=fun z=>nativeAnisotropicFiniteFieldHessian D s (k+1-i) w
    (anisotropicDisorderInjection n g+anisotropicUnitInput D z)
  have hG : BoundedJets G:=(native_translate_bounded
    (boundedJets_nativeAnisotropicFiniteFieldResponse D s (k+1-i) w)
    (anisotropicDisorderInjection n g)).comp_linear (anisotropicUnitInput D)
  have hH : BoundedJets H:=(native_translate_bounded
    (boundedJets_nativeAnisotropicFiniteFieldHessian D s (k+1-i) w)
    (anisotropicDisorderInjection n g)).comp_linear (anisotropicUnitInput D)
  obtain ⟨R,hR,hRb⟩:=hG.2 0
  obtain ⟨S,hS,hSb⟩:=hH.2 0
  have hRb' (z : Field n) : |G z|≤R:=by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hRb z
  have hSb' (z : Field n) : |H z|≤S:=by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hSb z
  have hf : LipschitzWith (‖anisotropicEnergyMap D‖₊*‖anisotropicUnitInput D‖₊) f:=by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hh:=(anisotropicFinitePotential_lipschitz D s (k+1-i)).dist_le_mul
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x)
      (anisotropicDisorderInjection n g+anisotropicUnitInput D z)
    have ht:=(anisotropicUnitInput D).lipschitzWith.dist_le_mul x z
    rw [dist_add_left] at hh
    exact hh.trans (by simpa only [NNReal.coe_mul,coe_nnnorm,mul_assoc] using
      mul_le_mul_of_nonneg_left ht (norm_nonneg (anisotropicEnergyMap D)))
  have hs:=vectorStepResponse_add f H (fun z=>s.m i*(G z)^2) _ hf hH.1.continuous.measurable
    (measurable_const.mul (hG.1.continuous.measurable.pow_const 2)) S (|s.m i| * R^2)
    hSb' (fun z=>by
      rw [abs_mul,abs_sq]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hRb' z) 2)
        (abs_nonneg (s.m i)))
    (s.q (i+1)-q) (s.m i) y
  have hsecond:=nativeAnisotropic_step_second_response_eq_field_hessian D s q i hi hq
    (anisotropicDisorderInjection n g) (anisotropicFieldInjection n w) y
  have hfirst:=nativeAnisotropic_step_response_eq_field_derivative D s g w q i hi hq y
  change vectorStepResponse (s.q (i+1)-q) (s.m i) f (fun z=>H z+s.m i*(G z)^2) y=_
  rw [hs,vectorStepResponse_mul_const]
  change vectorStepResponse (s.q (i+1)-q) (s.m i) f H y+
    s.m i*(vectorStepResponse (s.q (i+1)-q) (s.m i) f (fun z=>(G z)^2) y-
      (vectorStepResponse (s.q (i+1)-q) (s.m i) f G y)^2)=_ at hsecond
  change vectorStepResponse (s.q (i+1)-q) (s.m i) f G y=_ at hfirst
  rw [hfirst] at hsecond
  linarith

end QuantitativeFollowup
