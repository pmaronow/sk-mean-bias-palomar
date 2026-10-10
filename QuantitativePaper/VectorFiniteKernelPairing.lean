module
public import QuantitativePaper.VectorFiniteCellBackward
public import QuantitativePaper.VectorConditionalLaw
public import FourPapersCommon.ConditionalKernelFourier

@[expose] public section

/-! Literal constructed finite diffusion transition kernels: bounded smooth
observables have the actual whole-past weighted kernel pairing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

def vectorFiniteJointState (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : VectorState n :=
  (sample.1,vectorFiniteState s β t ht r sample)

theorem measurable_vectorFiniteJointState (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) : Measurable (vectorFiniteJointState (n:=n) s β t ht r) :=
  measurable_fst.prodMk (((stronglyAdapted_vectorFiniteState s β t ht r).measurable).mono
    ((vectorBrownianFiltration n).le r) le_rfl)

theorem adapted_vectorFiniteJointState (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) : Measurable[vectorBrownianFiltration n r]
      (vectorFiniteJointState (n:=n) s β t ht r) :=
  (stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk
    (stronglyAdapted_vectorFiniteState s β t ht r).measurable

theorem vectorProfileKernel_jointResponse (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i≤k+1) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (x : VectorState n) :
    (∫ y,G y ∂vectorProfileKernel s β t i x)=
      vectorJointResponse (fun p=>vectorRecursion s β t p.1 (k+1-i) p.2) G
        (((1-t)*β^2)*(s.q (i+1)-s.q i)) (s.m i) x := by
  rw [vectorProfileKernel,if_pos hi,integral_vectorStateKernel_response
    _ (measurable_vectorRecursion s β t _)
    (Real.sqrt (n : ℝ)).toNNReal (fun p=>vectorRecursion_lipschitz s β t p _)
    _ hG.regularity.continuous.measurable]
  rw [show (1-t)*(β^2*(s.q (i+1)-s.q i))=((1-t)*β^2)*(s.q (i+1)-s.q i) by ring]
  rfl

theorem vectorFinite_cell_kernel_pairing (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫ sample,Z sample*G (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal sample)
      ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,Z sample*(∫ y,G y ∂vectorProfileKernel s β t i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n := by
  letI := vectorProfileKernel_markov (n:=n) s β t i
  have hZg := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hg : Measurable G := hG.regularity.continuous.measurable
  have hgb : ∀ y,‖G y‖≤hG.bounds 0 := fun y=>by
    simpa only [norm_iteratedFDeriv_zero] using hG.jets 0 (by omega) y
  have hi₁ : Integrable (fun sample=>Z sample*G
      (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal sample))
      (vectorDisorderBrownianMeasure n) := by
    apply (integrable_const ((C : ℝ)*hG.bounds 0)).mono'
      (hZg.mul (hg.comp (measurable_vectorFiniteJointState s β t ht.le _))).aestronglyMeasurable
    exact .of_forall (fun sample=>by
      simp only [Pi.mul_apply,Function.comp_apply] 
      rw [norm_mul]
      exact mul_le_mul (hC sample) (hgb _) (norm_nonneg _) C.coe_nonneg)
  have hkernel := FourPapersCommon.stronglyMeasurable_kernelObservable
    (vectorProfileKernel (n:=n) s β t i) G hg
  have hi₂ : Integrable (fun sample=>Z sample*(∫ y,G y ∂vectorProfileKernel s β t i
      (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample)))
      (vectorDisorderBrownianMeasure n) := by
    apply (integrable_const ((C : ℝ)*hG.bounds 0)).mono'
      (hZg.mul (hkernel.measurable.comp
        (measurable_vectorFiniteJointState s β t ht.le _))).aestronglyMeasurable
    exact .of_forall (fun sample=>by
      simp only [Pi.mul_apply,Function.comp_apply] 
      rw [norm_mul]
      exact mul_le_mul (hC sample)
        (by
          simpa using norm_integral_le_of_norm_le_const
            (μ := vectorProfileKernel s β t i (vectorFiniteJointState s β t ht.le _ sample))
            (Filter.Eventually.of_forall hgb)) (norm_nonneg _) C.coe_nonneg)
  have he := (vectorFinite_cell_backward_identity s β t hβ ht i hi hG Z hZ C hC).2
  have he' : (∫ sample,Z sample*(G (vectorFiniteJointState s β t ht.le
      (s.q (i+1)).toNNReal sample)-
      ∫ y,G y ∂vectorProfileKernel s β t i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n)=0 := by
    simpa only [vectorProfileKernel_jointResponse s β t i hi hG,vectorFiniteJointState] using he
  simp_rw [mul_sub] at he'
  rw [integral_sub hi₁ hi₂] at he'
  exact sub_eq_zero.mp he'

end QuantitativePaper
