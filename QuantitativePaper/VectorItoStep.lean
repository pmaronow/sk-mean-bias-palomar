module
public import QuantitativePaper.VectorWeightedItoCoefficients
public import QuantitativePaper.VectorTaylorExpectation

@[expose] public section

/-! Exact one-cell expectation expansion along a genuine bounded-drift
vector Wiener state. All stochastic cancellations come from the actual past
independence theorem; the remaining error has already proved cubic control.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem measurable_vectorSpatialTaylorError
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorStaticItoTest f X) (r t : ℝ≥0) :
    Measurable (vectorSpatialTaylorError f (X r)
      (fun sample=>σ • disorderVectorBrownianIncrement r t sample)
      (fun sample=>vectorIntegratedDrift (fun s=>d s sample) t-
        vectorIntegratedDrift (fun s=>d s sample) r)) := by
  have hX : Measurable (X r) := (hc.adapted_state r).measurable.mono
    ((vectorBrownianFiltration n).le r) le_rfl
  have hW : Measurable (fun sample=>σ • disorderVectorBrownianIncrement (n := n) r t sample) :=
    (measurable_disorderVectorBrownianIncrement r t).const_smul σ
  have hV : Measurable (fun sample=>vectorIntegratedDrift (fun s=>d s sample) t-
      vectorIntegratedDrift (fun s=>d s sample) r) :=
    (stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift t).measurable.sub
      (stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift r).measurable
  have hfirst : Measurable (fun sample=>fderiv ℝ (f sample) (X r sample)) :=
    (hf.adapted_first r).mono ((vectorBrownianFiltration n).le r) le_rfl
  have hsecond : Measurable (fun sample=>vectorHessian (f sample) (X r sample)) :=
    (hf.adapted_second r).mono ((vectorBrownianFiltration n).le r) le_rfl
  have heval : Measurable (fun p : (Field n →L[ℝ] ℝ) × Field n=>p.1 p.2) := by fun_prop
  have heval₂ : Measurable (fun p : (Field n →L[ℝ] Field n →L[ℝ] ℝ) × Field n=>
      p.1 p.2 p.2) := by fun_prop
  have hfa := hf.measurable.comp (measurable_id.prodMk ((hX.add hW).add hV))
  have hfb := hf.measurable.comp (measurable_id.prodMk hX)
  have hgW := heval.comp (hfirst.prodMk hW)
  have hgV := heval.comp (hfirst.prodMk hV)
  have hhW := heval₂.comp (hsecond.prodMk hW)
  exact hfa.sub (((hfb.add hgW).add hgV).add (hhW.const_mul (1/2)))

theorem vector_ito_step_expectation
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorStaticItoTest f X) (r t : ℝ≥0) (hrt : r ≤ t)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) :
    Integrable (fun sample=>Z sample*(f sample (X t sample)-f sample (X r sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(f sample (X t sample)-f sample (X r sample))
      ∂vectorDisorderBrownianMeasure n) =
      (∫ sample,Z sample*fderiv ℝ (f sample) (X r sample)
        (vectorIntegratedDrift (fun s=>d s sample) t-
          vectorIntegratedDrift (fun s=>d s sample) r) ∂vectorDisorderBrownianMeasure n)+
      σ^2/2*((t : ℝ)-r)*(∫ sample,Z sample*vectorBilinearTrace
        (vectorHessian (f sample) (X r sample)) ∂vectorDisorderBrownianMeasure n)+
      (∫ sample,Z sample*vectorSpatialTaylorError f (X r)
        (fun sample=>σ • disorderVectorBrownianIncrement r t sample)
        (fun sample=>vectorIntegratedDrift (fun s=>d s sample) t-
          vectorIntegratedDrift (fun s=>d s sample) r) sample ∂vectorDisorderBrownianMeasure n) := by
  let P := vectorDisorderBrownianMeasure n
  let W : VectorDisorderBrownianSample n → Field n := fun sample=>σ • disorderVectorBrownianIncrement r t sample
  let V : VectorDisorderBrownianSample n → Field n := fun sample=>
    vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r
  let G : VectorDisorderBrownianSample n → ℝ := fun sample=>
    Z sample*fderiv ℝ (f sample) (X r sample) (W sample)
  let A : VectorDisorderBrownianSample n → ℝ := fun sample=>
    Z sample*fderiv ℝ (f sample) (X r sample) (V sample)
  let B : VectorDisorderBrownianSample n → ℝ := fun sample=>
    Z sample*vectorHessian (f sample) (X r sample) (W sample) (W sample)
  let R : VectorDisorderBrownianSample n → ℝ := fun sample=>Z sample*vectorSpatialTaylorError f (X r) W V sample
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hV (sample : VectorDisorderBrownianSample n) : ‖V sample‖ ≤ D*((t : ℝ)-r) :=
    vectorIntegratedDrift_increment_bound _
      (hc.measurable_drift.comp (measurable_id.prodMk measurable_const)) D
      (fun s=>hD s sample) hrt
  have hVmeas : Measurable V :=
    (stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift t).measurable.sub
      (stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift r).measurable
  have hfirst : Measurable (fun sample=>fderiv ℝ (f sample) (X r sample)) :=
    (hf.adapted_first r).mono ((vectorBrownianFiltration n).le r) le_rfl
  have hAmeas : Measurable A := hZg.mul
    ((show Measurable (fun p : (Field n →L[ℝ] ℝ) × Field n=>p.1 p.2) from by fun_prop).comp
      (hfirst.prodMk hVmeas))
  have hAi : Integrable A P := by
    apply (integrable_const ((C : ℝ)*hf.firstBound*D*((t : ℝ)-r))).mono' hAmeas.aestronglyMeasurable
    apply Eventually.of_forall
    intro sample
    have hg := (fderiv ℝ (f sample) (X r sample)).le_opNorm (V sample)
    have hfB := hf.first_le sample (X r sample)
    have hh := mul_le_mul hfB (hV sample) (norm_nonneg _) hf.firstBound.coe_nonneg
    have hzB := mul_le_mul_of_nonneg_left (hg.trans hh) C.coe_nonneg
    dsimp only [A]
    rw [norm_mul]
    calc
      _ ≤ (C : ℝ)*‖fderiv ℝ (f sample) (X r sample) (V sample)‖ :=
        mul_le_mul_of_nonneg_right (hC sample) (norm_nonneg _)
      _ ≤ _ := by nlinarith
  have hGi0 := integrable_known_CLM_increment r t hrt _
    (measurable_weightedVectorFirst hf Z hZ r) (integrable_weightedVectorFirst hf Z hZ C hC r)
  have heG : G=(fun sample=>σ*(weightedVectorFirst f X Z r sample (disorderVectorBrownianIncrement r t sample))) := by
    funext sample
    dsimp only [G,W,weightedVectorFirst]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hGi : Integrable G P := by rw [heG];exact hGi0.const_mul σ
  have hBi0 := integrable_known_bilinear_increment r t hrt _
    (measurable_weightedVectorSecond hf Z hZ r) (integrable_weightedVectorSecond hf Z hZ C hC r)
  have heB : B=(fun sample=>σ^2*(weightedVectorSecond f X Z r sample
      (disorderVectorBrownianIncrement r t sample) (disorderVectorBrownianIncrement r t sample))) := by
    funext sample
    dsimp only [B,W,weightedVectorSecond]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hBi : Integrable B P := by rw [heB];exact hBi0.const_mul (σ^2)
  have hRi : Integrable R P := (integral_weighted_vectorSpatialTaylorError_bound r t hrt σ f
    hf.regularity hf.secondBound hf.thirdBound D hf.second_le hf.third_le (X r) V hV Z C hC
      (hZg.mul (measurable_vectorSpatialTaylorError hc hf r t)).aestronglyMeasurable).1
  have he (sample : VectorDisorderBrownianSample n) :
      Z sample*(f sample (X t sample)-f sample (X r sample))=
        G sample+A sample+(1/2:ℝ)*B sample+R sample := by
    dsimp only [G,A,B,R,vectorSpatialTaylorError,vectorNoiseDriftTaylorPolynomial]
    have hinc := hc.increment r t sample
    change X t sample=X r sample+W sample+V sample at hinc
    rw [hinc]
    ring
  have hsumi : Integrable (fun sample=>G sample+A sample+(1/2:ℝ)*B sample+R sample) P :=
    ((hGi.add hAi).add (hBi.const_mul (1/2))).add hRi
  refine ⟨hsumi.congr (Eventually.of_forall fun sample=>(he sample).symm),?_⟩
  rw [show (fun sample=>Z sample*(f sample (X t sample)-f sample (X r sample)))=
    (fun sample=>G sample+A sample+(1/2:ℝ)*B sample+R sample) from funext he]
  have hs := integral_add ((hGi.add hAi).add (hBi.const_mul (1/2))) hRi
  have hs' := integral_add (hGi.add hAi) (hBi.const_mul (1/2))
  have hs'' := integral_add hGi hAi
  simp only [Pi.add_apply] at hs hs' hs''
  rw [hs,hs',hs'',integral_const_mul]
  have hg0 : (∫ sample,G sample ∂P)=0 := integral_weighted_vector_gradient_noise hf Z hZ C hC r t hrt σ
  have hb0 := integral_weighted_vector_hessian_noise hf Z hZ C hC r t hrt σ
  change (∫ sample,B sample ∂P)=_ at hb0
  rw [hg0,hb0]
  dsimp only [A,R,P,V,W]
  ring

end QuantitativePaper
