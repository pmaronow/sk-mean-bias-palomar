module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalScore

@[expose] public section

/-! The literal native signed-gradient identity. Every conditional/future
law and initial-field derivative is derived from the actual model. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128

private theorem native_coordinate_field_derivative_integrable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n) :
    Integrable (fun sample=>(fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample))
      (anisotropicMeasureSampleLaw D μ a) := by
  let Z:=fun sample : AnisotropicDisorderBrownianSample n=>(sample.1,anisotropicMeasureState D μ q sample)
  have hX:=(measurable_uncurry_anisotropicMeasureState D μ).comp
    ((measurable_const (a:=(q:ℝ))).prodMk (measurable_id (α:=AnisotropicDisorderBrownianSample n)))
  dsimp only [Function.comp_def] at hX
  have hmZ:=measurable_fst.prodMk hX
  have hm:=((measurable_cavityRestartNoiseSquareResponse D μ q r i).stronglyMeasurable.integral_prod_right'
    (ν:=vectorWienerMeasure n)).measurable.comp hmZ
  have hm' : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      ∫V,cavityRestartNoiseSquareResponse D μ q r i (Z sample,V) ∂vectorWienerMeasure n) := by
    convert hm using 1
    funext sample
    rfl
  have he sample : (fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)=
      ∫V,cavityRestartNoiseSquareResponse D μ q r i (Z sample,V) ∂vectorWienerMeasure n := by
    rw [←cavityRestartInitialMean_native D μ q sample]
    exact fderiv_anisotropicRestartSpinSquare_field_native_noise D μ sample.1 q r hqr _ i
  simp_rw [he]
  apply Integrable.of_bound hm'.aestronglyMeasurable (cavityRestartNoiseSquareBound D i)
  exact .of_forall fun sample=>by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=vectorWienerMeasure n)
      (.of_forall fun V=>norm_cavityRestartNoiseSquareResponse_le D μ q r i (Z sample,V))

private theorem native_square_response_integrable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n) :
    Integrable (cavitySignedResponseNativeSquareResponse D μ q r i) (anisotropicMeasureSampleLaw D μ a) := by
  have hZ : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample)):=
    (measurable_fst.prodMk ((measurable_uncurry_anisotropicMeasureState D μ).comp
      (measurable_const.prodMk measurable_id))).prodMk (measurable_anisotropicRecordedFutureBrownianPath _)
  have hm:=(measurable_cavityRestartNoiseSquareResponse D μ q r i).comp hZ
  dsimp only [Function.comp_def] at hm
  simp_rw [cavityRestartNoiseSquareResponse_native D μ q r hqr i] at hm
  apply Integrable.of_bound hm.aestronglyMeasurable (cavityRestartNoiseSquareBound D i)
  exact .of_forall fun sample=>by
    rw [←cavityRestartNoiseSquareResponse_native D μ q r hqr i sample]
    exact norm_cavityRestartNoiseSquareResponse_le D μ q r i _

private theorem native_mean_field_derivative_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (sample : AnisotropicDisorderBrownianSample n) :
    (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)=
      (∑i : Fin n,(fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
        (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample))/(n:ℝ) := by
  classical
  have hs:=HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    ((contDiff_anisotropicRestartSpinSquare_field D μ sample.1 q r hqr i).differentiable_one
      (anisotropicMeasureState D μ q sample)).hasFDerivAt)
  have hh:=(hs.const_mul ((n:ℝ)⁻¹)).fderiv
  have he : fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)=((n:ℝ)⁻¹) •∑i : Fin n,
      fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r) (anisotropicMeasureState D μ q sample) := by
    simpa only [anisotropicRestartMeanSquare,div_eq_mul_inv,mul_comm] using hh
  rw [he]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

private theorem native_square_response_sum (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (hn : 0<n) (q r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (∑i : Fin n,cavitySignedResponseNativeSquareResponse D μ q r i sample)/(n:ℝ)^2=
      2*cavitySignedResponseMixedHessian D μ q r sample/(n:ℝ)^2+
      (anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ r sample)*
        cavitySignedResponseWienerScore D μ q sample)/(n:ℝ) := by
  classical
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  let T:=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ r)) (anisotropicProcessParameter D μ r sample)
  let w:=anisotropicProcessMagnetization D μ q sample
  let v:=anisotropicProcessMagnetization D μ r sample
  have hH : T (anisotropicFieldInjection n w) (anisotropicFieldInjection n v)=
      ∑i : Fin n,v i*T (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i) := by
    rw [anisotropicFieldDirection_sum v,map_sum]
    simp only [map_smul,smul_eq_mul]
  change (∑i : Fin n,(2*v i*T (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i)+
    (v i)^2*cavitySignedResponseWienerScore D μ q sample))/(n:ℝ)^2=2*T (anisotropicFieldInjection n w)
    (anisotropicFieldInjection n v)/(n:ℝ)^2+_
  simp_rw [mul_assoc]
  rw [hH,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  simp only [anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin]
  field_simp
  dsimp only [v]
  ring

 theorem cavitySignedResponseFutureGradient_eq_score (D : AnisotropicSpinModel n)
    (hn : 0<n) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q r : Paper.Overlap) (hqr : q≤r) :
    cavitySignedResponseFutureGradient D μ a q r=
      2*cavitySignedResponseMixedHessianMoment D μ a q r+
      ∫p,cavitySignedResponseScore D μ a q p*
        anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ r p.1)
        ∂anisotropicMeasureSpinPathLaw D μ a := by
  classical
  let P:=anisotropicMeasureSampleLaw D μ a
  let A:=fun sample=>anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ r sample)
  have hM:=(measurable_uncurry_anisotropicProcessMagnetization D μ).comp
    ((measurable_const (a:=r)).prodMk (measurable_id (α:=AnisotropicDisorderBrownianSample n)))
  dsimp only [Function.comp_def] at hM
  have hA : Measurable A:=(continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp hM
  have hAb sample : ‖A sample‖≤1:=anisotropicSelectedMeanSquare_bound Finset.univ _
    (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ r _ i)
  have hScore : Measurable (cavitySignedResponseScore D μ a q):=
    (measurable_cavitySignedResponseTerminalResidual D μ q).sub
      ((measurable_cavitySignedResponseIntegratedFutureResidual D μ a q).comp measurable_fst)
  have hs : Integrable (fun p=>cavitySignedResponseScore D μ a q p*A p.1)
      (anisotropicMeasureSpinPathLaw D μ a) := by
    apply Integrable.of_bound (hScore.mul (hA.comp measurable_fst)).aestronglyMeasurable 4
    exact .of_forall fun p=>by
      change ‖cavitySignedResponseScore D μ a q p*A p.1‖≤4
      rw [norm_mul]
      have hb : ‖cavitySignedResponseScore D μ a q p‖≤4:=(norm_sub_le _ _).trans
        ((add_le_add (norm_cavitySignedResponseTerminalResidual_le D μ q p)
          (norm_cavitySignedResponseIntegratedFutureResidual_le D μ a ha q p.1)).trans_eq (by norm_num))
      exact (mul_le_mul hb (hAb p.1) (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)
  have hmarked : (∫p,cavitySignedResponseScore D μ a q p*A p.1 ∂anisotropicMeasureSpinPathLaw D μ a)=
      ∫sample,A sample*cavitySignedResponseWienerScore D μ q sample/(n:ℝ) ∂P := by
    rw [anisotropicMeasureSpinPathLaw,Measure.integral_compProd hs]
    apply integral_congr_ae
    exact .of_forall fun sample=>by
      change (∫σ,cavitySignedResponseScore D μ a q (sample,σ)*A sample
        ∂anisotropicMeasureTerminalKernel D μ sample)=A sample*cavitySignedResponseWienerScore D μ q sample/(n:ℝ)
      rw [integral_mul_const,integral_anisotropicMeasureTerminalKernel_signed_score D hn μ a ha hμ q sample]
      ring
  have hvalue : cavitySignedResponseFutureGradient D μ a q r=
      ∫sample,(∑i : Fin n,cavitySignedResponseNativeSquareResponse D μ q r i sample)/(n:ℝ)^2 ∂P := by
    unfold cavitySignedResponseFutureGradient
    simp_rw [native_mean_field_derivative_sum D μ q r hqr]
    rw [integral_div,integral_finsetSum Finset.univ (fun i _=>native_coordinate_field_derivative_integrable D μ a q r hqr i)]
    simp_rw [integral_native_restart_coordinate_field_score D μ a q r hqr]
    rw [←integral_finsetSum Finset.univ (fun i _=>native_square_response_integrable D μ a q r hqr i),integral_div]
    ring
  have hR : Integrable (fun sample=>(∑i : Fin n,cavitySignedResponseNativeSquareResponse D μ q r i sample)/(n:ℝ)^2) P :=
    (integrable_finsetSum _ fun i _=>native_square_response_integrable D μ a q r hqr i).div_const _
  have hM : Integrable (cavitySignedResponseMixedHessian D μ q r) P:=
    bounded_real_integrable _ (measurable_cavitySignedResponseMixedHessian D μ q r) _
      (norm_cavitySignedResponseMixedHessian_le D μ q r)
  have hB : Integrable (fun sample=>A sample*cavitySignedResponseWienerScore D μ q sample/(n:ℝ)) P:=by
    have h:=hR.sub ((hM.const_mul 2).div_const ((n:ℝ)^2))
    apply h.congr
    exact .of_forall fun sample=>by
      change (∑i : Fin n,cavitySignedResponseNativeSquareResponse D μ q r i sample)/(n:ℝ)^2-
        2*cavitySignedResponseMixedHessian D μ q r sample/(n:ℝ)^2=
        A sample*cavitySignedResponseWienerScore D μ q sample/(n:ℝ)
      rw [native_square_response_sum D μ hn q r sample]
      dsimp only [A]
      ring
  rw [hvalue]
  simp_rw [native_square_response_sum D μ hn q r]
  rw [integral_add ((hM.const_mul 2).div_const _) hB,integral_div,integral_const_mul,←hmarked]
  unfold cavitySignedResponseMixedHessianMoment
  ring

end QuantitativeFollowup
