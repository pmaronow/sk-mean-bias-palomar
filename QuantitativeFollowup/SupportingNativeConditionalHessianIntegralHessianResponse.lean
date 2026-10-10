module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralResponse
public import QuantitativePaper.VectorGaussianExpectation

@[expose] public section

/-! Actual directional Hessian response on every anisotropic finite cell.
The two terminal derivatives are differentiated under the genuine normalized
Gaussian kernel, including zero cell mass and zero remaining variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

private theorem native_affine_tail_response (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤k+1)
    (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1)))
    (c V : AnisotropicParameter n) (y : Field n) :
    vectorStepResponse (s.q (i+1)-q) (s.m i)
      (fun z=>anisotropicFinitePotential D s (k+1-i) (c+anisotropicUnitInput D z))
      (fun z=>fderiv ℝ (anisotropicFinitePotential D s (k+1-i))
        (c+anisotropicUnitInput D z) V) y=
    fderiv ℝ (anisotropicFiniteTailPotential D s q) (c+anisotropicUnitInput D y) V := by
  let f:=anisotropicFinitePotential D s (k+1-i)
  let A:=anisotropicUnitInput D
  let F : ℝ→Field n→ℝ:=fun a z=>f (c+A z+a • V)
  let G : ℝ→Field n→ℝ:=fun a z=>fderiv ℝ f (c+A z+a • V) V
  let L:=‖anisotropicEnergyMap D‖₊*‖A‖₊
  obtain ⟨B,hB,hbj⟩:=(boundedPositiveJets_anisotropicFinitePotential D s (k+1-i)).2 1 le_rfl
  let R : ℝ≥0:=⟨B*‖V‖,mul_nonneg hB (norm_nonneg _)⟩
  have hF (a : ℝ) : LipschitzWith L (F a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hh:=(anisotropicFinitePotential_lipschitz D s (k+1-i)).dist_le_mul
      (c+A x+a • V) (c+A z+a • V)
    have hA:=A.lipschitzWith.dist_le_mul x z
    have hA' : dist (c+A x+a • V) (c+A z+a • V)≤‖A‖*dist x z:=by
      simpa only [dist_add_right,dist_add_left,coe_nnnorm] using hA
    simpa only [F,L,dist_add_right,dist_add_left,NNReal.coe_mul,coe_nnnorm,mul_assoc] using
      hh.trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg (anisotropicEnergyMap D)))
  have hG (a : ℝ) : Measurable (G a) :=
    ((boundedPositiveJets_anisotropicFinitePotential D s (k+1-i)).boundedJets_fderiv_apply V).1.continuous.measurable.comp
      (by fun_prop)
  have hb (a : ℝ) (z : Field n) : |G a z|≤R := by
    change |fderiv ℝ f (c+A z+a • V) V|≤B*‖V‖
    have he : ‖fderiv ℝ f (c+A z+a • V)‖≤B := by
      rw [←norm_iteratedFDeriv_one]
      exact hbj _
    simpa only [Real.norm_eq_abs] using
      ((fderiv ℝ f (c+A z+a • V)).le_opNorm V).trans
        (mul_le_mul_of_nonneg_right he (norm_nonneg V))
  have hd (a : ℝ) (z : Field n) : HasDerivAt (fun r=>F r z) (G a z) a :=
    hasDerivAt_affine_line_of_differentiable f
      ((contDiff_anisotropicFinitePotential D s (k+1-i)).differentiable (by simp)) (c+A z) V a
  have hr:=hasDerivAt_vectorColeHopfStep_response F G L R hF hG hb hd
    (s.q (i+1)-q) (s.m i) y 0
  have hfun : (fun a=>vectorColeHopfStep (s.q (i+1)-q) (s.m i) (F a) y)=
      (fun a=>anisotropicFiniteTailPotential D s q (c+A y+a • V)):=by
    funext a
    have he : F a=(fun z=>f ((c+a • V)+A z)):=by
      funext z
      dsimp only [F]
      congr 1
      abel
    rw [he,←gaussianShiftColeHopf_smul_eq_vectorStep]
    unfold anisotropicFiniteTailPotential
    rw [anisotropicTailRecursion_eq_cell D s q i hi hq]
    dsimp only [f,A]
    congr 1
    abel
  change HasDerivAt (fun a=>vectorColeHopfStep (s.q (i+1)-q) (s.m i) (F a) y) _ 0 at hr
  rw [hfun] at hr
  have ht:=hasDerivAt_affine_line_of_differentiable (anisotropicFiniteTailPotential D s q)
    ((contDiff_anisotropicFiniteTailPotential D s q).differentiable (by simp)) (c+A y) V 0
  change vectorStepResponse (s.q (i+1)-q) (s.m i) (fun z=>f (c+A z))
    (fun z=>fderiv ℝ f (c+A z) V) y=_
  simpa only [zero_smul,add_zero,F,G,f,A] using hr.unique ht


private theorem native_second_directional_eval (f : AnisotropicParameter n→ℝ)
    (hf : ContDiff ℝ ∞ f) (P V : AnisotropicParameter n) :
    fderiv ℝ (fun Q=>fderiv ℝ f Q V) P V=fderiv ℝ (fderiv ℝ f) P V V := by
  have hd : Differentiable ℝ (fderiv ℝ f):=
    (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hd P) (differentiableAt_const V),
    show fderiv ℝ (fun _ : AnisotropicParameter n=>V) P=0 from (hasFDerivAt_const V P).fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

theorem nativeAnisotropic_step_second_response_eq_field_hessian
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap)
    (i : ℕ) (hi : i≤k+1) (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1)))
    (c V : AnisotropicParameter n) (y : Field n) :
    vectorStepSecondResponse (s.q (i+1)-q) (s.m i)
      (fun z=>anisotropicFinitePotential D s (k+1-i) (c+anisotropicUnitInput D z))
      (fun z=>fderiv ℝ (anisotropicFinitePotential D s (k+1-i))
        (c+anisotropicUnitInput D z) V)
      (fun z=>fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s (k+1-i)))
        (c+anisotropicUnitInput D z) V V) y=
    fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q))
      (c+anisotropicUnitInput D y) V V := by
  let f:=anisotropicFinitePotential D s (k+1-i)
  let A:=anisotropicUnitInput D
  let u : AnisotropicParameter n→ℝ:=fun P=>fderiv ℝ f P V
  let h : AnisotropicParameter n→ℝ:=fun P=>fderiv ℝ u P V
  let F : ℝ→Field n→ℝ:=fun a z=>f (c+A z+a • V)
  let G : ℝ→Field n→ℝ:=fun a z=>u (c+A z+a • V)
  let H : ℝ→Field n→ℝ:=fun a z=>h (c+A z+a • V)
  have hu : BoundedJets u:=(boundedPositiveJets_anisotropicFinitePotential D s (k+1-i)).boundedJets_fderiv_apply V
  have hh : BoundedJets h:=hu.fderiv_apply V
  obtain ⟨R0,hR0,hRb⟩:=hu.2 0
  obtain ⟨S0,hS0,hSb⟩:=hh.2 0
  let R : ℝ≥0:=⟨R0,hR0⟩
  let S : ℝ≥0:=⟨S0,hS0⟩
  let L:=‖anisotropicEnergyMap D‖₊*‖A‖₊
  have hF (a : ℝ) : LipschitzWith L (F a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hx:=(anisotropicFinitePotential_lipschitz D s (k+1-i)).dist_le_mul
      (c+A x+a • V) (c+A z+a • V)
    have hz : dist (c+A x+a • V) (c+A z+a • V)≤‖A‖*dist x z:=by
      simpa only [dist_add_right,dist_add_left,coe_nnnorm] using A.lipschitzWith.dist_le_mul x z
    simpa only [F,L,NNReal.coe_mul,coe_nnnorm,mul_assoc] using
      hx.trans (mul_le_mul_of_nonneg_left hz (norm_nonneg (anisotropicEnergyMap D)))
  have hG (a : ℝ) : Measurable (G a):=hu.1.continuous.measurable.comp (by fun_prop)
  have hH (a : ℝ) : Measurable (H a):=hh.1.continuous.measurable.comp (by fun_prop)
  have hbG (a : ℝ) (z : Field n) : |G a z|≤R:=by
    change |u (c+A z+a • V)|≤R0
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hRb (c+A z+a • V)
  have hbH (a : ℝ) (z : Field n) : |H a z|≤S:=by
    change |h (c+A z+a • V)|≤S0
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hSb (c+A z+a • V)
  have hdF (a : ℝ) (z : Field n) : HasDerivAt (fun b=>F b z) (G a z) a:=
    hasDerivAt_affine_line_of_differentiable f
      ((contDiff_anisotropicFinitePotential D s (k+1-i)).differentiable (by simp)) (c+A z) V a
  have hdG (a : ℝ) (z : Field n) : HasDerivAt (fun b=>G b z) (H a z) a:=
    hasDerivAt_affine_line_of_differentiable u (hu.1.differentiable (by simp)) (c+A z) V a
  have hr:=hasDerivAt_vectorStepResponse F G H L R S hF hG hH hbG hbH hdF hdG
    (s.q (i+1)-q) (s.m i) y 0
  have hfun : (fun a=>vectorStepResponse (s.q (i+1)-q) (s.m i) (F a) (G a) y)=
      fun a=>fderiv ℝ (anisotropicFiniteTailPotential D s q) (c+A y+a • V) V:=by
    funext a
    have hfa : F a=fun z=>f ((c+a • V)+A z):=by funext z;dsimp only [F];congr 1;abel
    have hga : G a=fun z=>fderiv ℝ f ((c+a • V)+A z) V:=by
      funext z;dsimp only [G,u];congr 2;abel
    rw [hfa,hga]
    have he:=native_affine_tail_response D s q i hi hq (c+a • V) V y
    convert he using 1
    congr 2
    abel
  change HasDerivAt (fun a=>vectorStepResponse (s.q (i+1)-q) (s.m i) (F a) (G a) y) _ 0 at hr
  rw [hfun] at hr
  have htail : ContDiff ℝ ∞ (fun P=>fderiv ℝ (anisotropicFiniteTailPotential D s q) P V):=
    ((contDiff_anisotropicFiniteTailPotential D s q).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have ht:=hasDerivAt_affine_line_of_differentiable
    (fun P=>fderiv ℝ (anisotropicFiniteTailPotential D s q) P V)
    (htail.differentiable (by simp)) (c+A y) V 0
  rw [zero_smul,add_zero,native_second_directional_eval _ (contDiff_anisotropicFiniteTailPotential D s q)] at ht
  have hH0 : H 0=fun z=>fderiv ℝ (fderiv ℝ f) (c+A z) V V:=by
    funext z
    dsimp only [H,h,u]
    rw [zero_smul,add_zero,native_second_directional_eval _ (contDiff_anisotropicFinitePotential D s (k+1-i))]
  rw [hH0] at hr
  simpa only [F,G,u,f,A,zero_smul,add_zero] using hr.unique ht

end QuantitativeFollowup
