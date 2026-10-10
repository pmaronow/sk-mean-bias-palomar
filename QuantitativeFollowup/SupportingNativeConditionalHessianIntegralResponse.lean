module
public import QuantitativeFollowup.AnisotropicFiniteJointResponseData
public import QuantitativeFollowup.AnisotropicMagnetization
public import QuantitativePaper.VectorSpatialStep

@[expose] public section

/-! Genuine bounded-jet anisotropic field observables and their actual
single-cell normalized Gaussian response. The spatial direction is arbitrary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

private theorem native_boundedJets_translate {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E→ℝ} (hf : BoundedJets f) (c : E) :
    BoundedJets (fun y=>f (c+y)) := by
  refine ⟨hf.1.comp (contDiff_const.add contDiff_id),?_⟩
  intro j
  obtain ⟨B,hB,hb⟩:=hf.2 j
  refine ⟨B,hB,fun y=>?_⟩
  rw [iteratedFDeriv_comp_add_left]
  exact hb _

def nativeAnisotropicFiniteFieldResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (w : Field n) (P : AnisotropicParameter n) : ℝ :=
  fderiv ℝ (anisotropicFinitePotential D s j) P (anisotropicFieldInjection n w)

theorem boundedJets_nativeAnisotropicFiniteFieldResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (w : Field n) :
    BoundedJets (nativeAnisotropicFiniteFieldResponse D s j w) :=
  (boundedPositiveJets_anisotropicFinitePotential D s j).boundedJets_fderiv_apply
    (anisotropicFieldInjection n w)

def nativeAnisotropicWhitenedJointFieldResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (g : AnisotropicDisorder n) (w : Field n) (z : VectorParameter n) : ℝ :=
  nativeAnisotropicFiniteFieldResponse D s j w
    (anisotropicDisorderInjection n g+anisotropicWhiteJointInput D z)

theorem boundedJets_nativeAnisotropicWhitenedJointFieldResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (g : AnisotropicDisorder n) (w : Field n) :
    BoundedJets (nativeAnisotropicWhitenedJointFieldResponse D s j g w) :=
  (native_boundedJets_translate (boundedJets_nativeAnisotropicFiniteFieldResponse D s j w)
    (anisotropicDisorderInjection n g)).comp_linear (anisotropicWhiteJointInput D)

def nativeAnisotropicFieldResponseData (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (g : AnisotropicDisorder n) (w : Field n) :
    VectorJointResponseTestData (anisotropicWhitenedFiniteJointPotential D s j g)
      (nativeAnisotropicWhitenedJointFieldResponse D s j g w) := by
  let h:=boundedJets_nativeAnisotropicWhitenedJointFieldResponse D s j g w
  exact anisotropicWhitenedFiniteJointResponseData D s j g {
    regularity:=h.1.of_le (by simp)
    bounds:=fun r=>Classical.choose (h.2 r)
    bounds_nonneg:=fun r=>(Classical.choose_spec (h.2 r)).1
    jets:=fun r _=>(Classical.choose_spec (h.2 r)).2 }

theorem nativeAnisotropic_step_response_eq_field_derivative (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤k+1)
    (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1))) (y : Field n) :
    vectorStepResponse (s.q (i+1)-q) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun z=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (0,z)) y=
      fderiv ℝ (anisotropicFiniteTailPotential D s q)
        (anisotropicDisorderInjection n g+anisotropicUnitInput D y) (anisotropicFieldInjection n w) := by
  let f:=anisotropicFinitePotential D s (k+1-i)
  let V:=anisotropicFieldInjection n w
  let c:=anisotropicDisorderInjection n g
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
    dsimp only [f,A,c]
    congr 1
    abel
  change HasDerivAt (fun a=>vectorColeHopfStep (s.q (i+1)-q) (s.m i) (F a) y) _ 0 at hr
  rw [hfun] at hr
  have ht:=hasDerivAt_affine_line_of_differentiable (anisotropicFiniteTailPotential D s q)
    ((contDiff_anisotropicFiniteTailPotential D s q).differentiable (by simp)) (c+A y) V 0
  change vectorStepResponse (s.q (i+1)-q) (s.m i) (fun z=>f (c+A z))
    (fun z=>fderiv ℝ f (c+A z) V) y=_
  simpa only [zero_smul,add_zero,F,G,f,c,A,V] using hr.unique ht

theorem nativeAnisotropic_step_response_spatial_derivative (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤k+1)
    (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1))) (y e : Field n) :
    fderiv ℝ (vectorStepResponse (s.q (i+1)-q) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun z=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (0,z))) y e=
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q))
        (anisotropicDisorderInjection n g+anisotropicUnitInput D y)
        (anisotropicUnitInput D e) (anisotropicFieldInjection n w) := by
  let U:=anisotropicFiniteTailPotential D s q
  let V:=anisotropicFieldInjection n w
  let A:=anisotropicUnitInput D
  let c:=anisotropicDisorderInjection n g
  have hEq : vectorStepResponse (s.q (i+1)-q) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun z=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (0,z))=
      fun z=>fderiv ℝ U (c+A z) V:=
    funext (nativeAnisotropic_step_response_eq_field_derivative D s g w q i hi hq)
  rw [hEq]
  have hD : Differentiable ℝ (fderiv ℝ U):=
    ((contDiff_anisotropicFiniteTailPotential D s q).fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  have hF : Differentiable ℝ (fun P=>fderiv ℝ U P V):=hD.clm_apply (differentiable_const V)
  have hA : HasFDerivAt (fun z=>c+A z) A y:=A.hasFDerivAt.const_add c
  change (fderiv ℝ ((fun P : AnisotropicParameter n=>fderiv ℝ U P V) ∘
    (fun z : Field n=>c+A z)) y) e = _
  rw [fderiv_comp y (hF (c+A y)) hA.differentiableAt]
  rw [fderiv_clm_apply (hD (c+A y)) (differentiableAt_const V),
    show fderiv ℝ (fun _ : AnisotropicParameter n=>V) (c+A y)=0 from (hasFDerivAt_const V _).fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.comp_apply,
    hA.fderiv,ContinuousLinearMap.flip_apply]
  rfl

end QuantitativeFollowup
