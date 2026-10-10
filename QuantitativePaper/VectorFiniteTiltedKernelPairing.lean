module
public import QuantitativePaper.VectorFiniteConditionalKernel
public import QuantitativePaper.VectorTiltedIntegral

@[expose] public section

/-! Whole-Wiener-past kernel pairings under the actual normalized
fractional initial tilt, using its integrability rather than boundedness. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFinite_cell_kernel_pairing_tilt (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (F : VectorState n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x,‖F x‖≤B)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫sample,Z sample*F (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal sample)
      ∂vectorFiniteDisorderTilt s β t a)=
      ∫sample,Z sample*(∫ y,F y ∂vectorProfileKernel s β t i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample))
      ∂vectorFiniteDisorderTilt s β t a := by
  let W : VectorDisorderBrownianSample n→ℝ :=
    fun sample=>Real.exp (a*vectorRecursion s β t sample.1 (k+2) 0)
  have hW : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] W := by
    apply Real.measurable_exp.comp
    apply Measurable.const_mul
    simpa only [Function.comp_def] using
      (measurable_vectorRecursion s β t (k+2)).comp
        ((stronglyMeasurable_initialVectorDisorder n (s.q i).toNNReal).measurable.prodMk measurable_const)
  have hWi : Integrable W (vectorDisorderBrownianMeasure n) :=
    (integrable_exp_vectorRecursion s β t a (k+2) 0).comp_fst (vectorBrownianMeasure n)
  have hL : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] (W*Z) := hW.mul hZ
  have hLi : Integrable (W*Z) (vectorDisorderBrownianMeasure n) := by
    apply (hWi.norm.const_mul (C : ℝ)).mono'
      (hL.mono ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
    exact .of_forall fun sample=>by
      simp only [Pi.mul_apply,norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC sample) (norm_nonneg (W sample))
  have he := vectorFinite_cell_integrable_weighted_pairing s β t hβ ht i hi F hF B hB
    (W*Z) hL hLi
  rw [integral_vectorFiniteDisorderTilt,integral_vectorFiniteDisorderTilt]
  congr 1
  simpa only [Pi.mul_apply,W,mul_assoc] using he

end QuantitativePaper
