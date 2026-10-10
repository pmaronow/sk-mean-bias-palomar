module
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions
public import QuantitativeFollowup.FollowupCavitySignedResponseT3Integrability
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalIdentity

@[expose] public section

/-! Original native signed-response estimate, with the true future
field derivative identified by actual Wiener conditioning and score
differentiation, rather than supplied as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

private theorem abs_difference_le (x y : ℝ) : |x-y|≤|x|+|y| := by
  simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x (0:ℝ) y

private theorem strict_kernel_norm (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (p l : Paper.Overlap) : ‖cavitySignedScalarStrictFutureKernel β0 μ p l‖≤1 := by
  have hp : Gamma β0 μ p*Gamma β0 μ l≤1 :=
    (mul_le_mul (scalarGamma_le_one β0 μ p p.property) (scalarGamma_le_one β0 μ l l.property)
      (scalarGamma_nonneg β0 μ l) zero_le_one).trans_eq (one_mul (1:ℝ))
  have hs := (cavitySignedScalarStrictFutureKernel_square_le β0 μ p l).trans hp
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (cavitySignedScalarStrictFutureKernel β0 μ p l),
    abs_nonneg (cavitySignedScalarStrictFutureKernel β0 μ p l)]

theorem cavitySignedResponseT3_eq_native_score_decomposition (D : AnisotropicSpinModel n)
    (hn : 0<n) (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (p : Paper.Overlap) :
    cavitySignedResponseT3 D μ a β0 p=
      cavitySignedResponseT3Diagonal D μ a β0 p-cavitySignedResponseT3Explicit D μ a β0 p-
        cavitySignedResponseT3Score D μ a β0 p-cavitySignedResponseT3LastHessian D μ a β0 p := by
  let ν := parisiFreeMeasure μ a
  let P := anisotropicMeasureSpinPathLaw D μ a
  let K := cavitySignedScalarStrictFutureKernel β0 μ p
  let E := fun l : Paper.Overlap=>K l*cavitySignedResponseMixedHessianMoment D μ a p l
  let S := fun l : Paper.Overlap=>K l*(∫z,cavitySignedResponseScore D μ a p z*
    cavitySignedResponseSelfOverlap D μ l z.1 ∂P)
  have hmap : Measurable (fun l : Paper.Overlap=>(p,l)) := measurable_const.prodMk measurable_id
  have hK := (measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ).comp hmap
  have hB := (measurable_cavitySignedResponseMixedHessianMoment D μ a).comp hmap
  have hiE : Integrable E ν := by
    apply (integrable_const 1).mono' (hK.mul hB).aestronglyMeasurable
    exact .of_forall fun l=>by
      change ‖K l*cavitySignedResponseMixedHessianMoment D μ a p l‖≤1
      rw [norm_mul]
      exact (mul_le_mul (strict_kernel_norm β0 μ p l)
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a p l)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hAmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hA := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap
  have hF := (hK.comp measurable_fst).mul
    (((measurable_cavitySignedResponseScore D μ a p).comp measurable_snd).mul hA)
  dsimp only [Function.comp_def] at hF
  have hiS0 := integrable_bounded_integral_family ν P
    (fun l z=>K l*(cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1)) hF 4
    (fun l z=>by
      change ‖K l*(cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1)‖≤4
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (strict_kernel_norm β0 μ p l)
        (mul_le_mul (norm_cavitySignedResponseScore_le D μ a ha p z)
          (norm_cavitySignedResponseSelfOverlap_le D μ l z.1) (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num))
  have hiS : Integrable S ν := hiS0.congr (.of_forall fun l=>integral_const_mul _ _)
  have he (l : Paper.Overlap) : K l*cavitySignedResponseFutureGradient D μ a p l=2*E l+S l := by
    by_cases hpl : p<l
    · rw [cavitySignedResponseFutureGradient_eq_score D hn μ a ha hμ p l hpl.le]
      dsimp only [E,S,cavitySignedResponseSelfOverlap]
      ring
    · simp only [K,cavitySignedScalarStrictFutureKernel,if_neg hpl,E,S,zero_mul,mul_zero,zero_add]
  unfold cavitySignedResponseT3
  change cavitySignedResponseT3Diagonal D μ a β0 p-(∫l,K l*cavitySignedResponseFutureGradient D μ a p l ∂ν)-_= _
  simp_rw [he]
  rw [integral_add (hiE.const_mul 2) hiS,integral_const_mul]
  change cavitySignedResponseT3Diagonal D μ a β0 p-
    (cavitySignedResponseT3Explicit D μ a β0 p+cavitySignedResponseT3Score D μ a β0 p)-_=_
  ring

theorem cavitySignedResponse_T3_original_integral_bound (D : AnisotropicSpinModel n)
    (hn : 0<n) (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    |∫p,cavitySignedResponseT3 D μ a β0 p ∂parisiFreeMeasure μ a|≤
      cavitySignedResponseWeightedA D μ a β0+16*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  have hD := integrable_cavitySignedResponseT3Diagonal D μ a β0 hβ0
  have hE := integrable_cavitySignedResponseT3Explicit D μ a β0 hβ0
  have hS := integrable_cavitySignedResponseT3Score D μ a β0 hβ0 ha
  have hH := integrable_cavitySignedResponseT3LastHessian D μ a β0 hβ0
  simp_rw [cavitySignedResponseT3_eq_native_score_decomposition D hn μ a β0 hβ0 ha hμ]
  rw [integral_sub
      (f:=fun p=>cavitySignedResponseT3Diagonal D μ a β0 p-cavitySignedResponseT3Explicit D μ a β0 p-
        cavitySignedResponseT3Score D μ a β0 p) (g:=cavitySignedResponseT3LastHessian D μ a β0)
      ((hD.sub hE).sub hS) hH,
    integral_sub
      (f:=fun p=>cavitySignedResponseT3Diagonal D μ a β0 p-cavitySignedResponseT3Explicit D μ a β0 p)
      (g:=cavitySignedResponseT3Score D μ a β0) (hD.sub hE) hS,
    integral_sub (f:=cavitySignedResponseT3Diagonal D μ a β0)
      (g:=cavitySignedResponseT3Explicit D μ a β0) hD hE]
  have hbD := cavitySignedResponse_T3_diagonal_integral_bound D μ a β0 hβ0
  have hbE0 := cavitySignedResponse_T3_future_explicit_integral_bound D μ a β0 hβ0 ha
  have hbE : |∫p,cavitySignedResponseT3Explicit D μ a β0 p ∂parisiFreeMeasure μ a|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
    simpa only [cavitySignedResponseT3Explicit,integral_const_mul] using hbE0
  have hbS := cavitySignedResponse_T3_score_original_integral_bound D μ a β0 hβ0 ha hμ hn
  have hbH := cavitySignedResponse_T3_last_Hessian_original_integral_bound D μ a β0 hβ0 ha
  have h1 := abs_difference_le (∫p,cavitySignedResponseT3Diagonal D μ a β0 p ∂parisiFreeMeasure μ a)
    (∫p,cavitySignedResponseT3Explicit D μ a β0 p ∂parisiFreeMeasure μ a)
  have h2 := abs_difference_le
    ((∫p,cavitySignedResponseT3Diagonal D μ a β0 p ∂parisiFreeMeasure μ a)-
      (∫p,cavitySignedResponseT3Explicit D μ a β0 p ∂parisiFreeMeasure μ a))
    (∫p,cavitySignedResponseT3Score D μ a β0 p ∂parisiFreeMeasure μ a)
  have h3 := abs_difference_le
    ((∫p,cavitySignedResponseT3Diagonal D μ a β0 p ∂parisiFreeMeasure μ a)-
      (∫p,cavitySignedResponseT3Explicit D μ a β0 p ∂parisiFreeMeasure μ a)-
      (∫p,cavitySignedResponseT3Score D μ a β0 p ∂parisiFreeMeasure μ a))
    (∫p,cavitySignedResponseT3LastHessian D μ a β0 p ∂parisiFreeMeasure μ a)
  linarith

theorem cavitySignedResponse_T_native_integral_bound (D : AnisotropicSpinModel n)
    (hn : 0<n) (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    |∫p,cavitySignedResponseT D μ a β0 hβ0 p ∂parisiFreeMeasure μ a|≤
      cavitySignedResponseWeightedA D μ a β0+24*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  have h1 := integrable_cavitySignedResponseT1 D μ a β0 hβ0
  have hF := integrable_cavitySignedResponseT2First D μ a β0 hβ0
  have hB := integrable_cavitySignedResponseT2Double D μ a β0 hβ0
  have h3 : Integrable (cavitySignedResponseT3 D μ a β0) (parisiFreeMeasure μ a) := by
    have hi := (((integrable_cavitySignedResponseT3Diagonal D μ a β0 hβ0).sub
      (integrable_cavitySignedResponseT3Explicit D μ a β0 hβ0)).sub
      (integrable_cavitySignedResponseT3Score D μ a β0 hβ0 ha)).sub
      (integrable_cavitySignedResponseT3LastHessian D μ a β0 hβ0)
    exact hi.congr (.of_forall fun p=>(cavitySignedResponseT3_eq_native_score_decomposition D hn μ a β0 hβ0 ha hμ p).symm)
  unfold cavitySignedResponseT cavitySignedResponseT2
  rw [integral_add
      (f:=fun p=>cavitySignedResponseT1 D μ a β0 hβ0 p+
        (cavitySignedResponseT2First D μ a β0 hβ0 p+cavitySignedResponseT2Double D μ a β0 p))
      (g:=cavitySignedResponseT3 D μ a β0) (h1.add (hF.add hB)) h3,
    integral_add (f:=cavitySignedResponseT1 D μ a β0 hβ0)
      (g:=fun p=>cavitySignedResponseT2First D μ a β0 hβ0 p+cavitySignedResponseT2Double D μ a β0 p)
      h1 (hF.add hB),
    integral_add (f:=cavitySignedResponseT2First D μ a β0 hβ0)
      (g:=cavitySignedResponseT2Double D μ a β0) hF hB]
  have hb1 := cavitySignedResponse_T1_original_integral_bound D μ a β0 hβ0 ha hμ hn
  have hbF := cavitySignedResponse_T2_first_original_integral_bound D μ a β0 hβ0 ha hμ hn
  have hbB := cavitySignedResponse_T2_double_original_integral_bound D μ a β0 hβ0 ha hμ hn
  have hb3 := cavitySignedResponse_T3_original_integral_bound D hn μ a β0 hβ0 ha hμ
  have hA1 := abs_add_le
    (∫p,cavitySignedResponseT2First D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)
    (∫p,cavitySignedResponseT2Double D μ a β0 p ∂parisiFreeMeasure μ a)
  have hA2 := abs_add_le
    (∫p,cavitySignedResponseT1 D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)
    ((∫p,cavitySignedResponseT2First D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)+
      (∫p,cavitySignedResponseT2Double D μ a β0 p ∂parisiFreeMeasure μ a))
  have hA3 := abs_add_le
    ((∫p,cavitySignedResponseT1 D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)+
      ((∫p,cavitySignedResponseT2First D μ a β0 hβ0 p ∂parisiFreeMeasure μ a)+
        (∫p,cavitySignedResponseT2Double D μ a β0 p ∂parisiFreeMeasure μ a)))
    (∫p,cavitySignedResponseT3 D μ a β0 p ∂parisiFreeMeasure μ a)
  linarith

end QuantitativeFollowup
