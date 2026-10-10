module
public import QuantitativePaper.VectorFiniteRestrictedLaw
public import FourPapersCommon.ConditionalKernelWeight

@[expose] public section

/-! The actual finite vector diffusion conditional kernels retain the
whole Wiener past. Integrable past weights need not be bounded. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFinite_transition_condExp (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (F : VectorState n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x,‖F x‖≤B) :
    (vectorDisorderBrownianMeasure n)[
      (fun sample=>F (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal sample)) |
      vectorBrownianFiltration n (s.q i).toNNReal]=ᵐ[vectorDisorderBrownianMeasure n]
      fun sample=>∫ y,F y ∂vectorProfileKernel s β t i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample) := by
  letI := vectorProfileKernel_markov (n:=n) s β t i
  exact FourPapersCommon.condExp_kernel_of_restricted_transitionLaw
    (vectorBrownianFiltration n (s.q i).toNNReal) (vectorDisorderBrownianMeasure n)
    ((vectorBrownianFiltration n).le _) _ _
    (adapted_vectorFiniteJointState s β t ht.le _).stronglyMeasurable
    (measurable_vectorFiniteJointState s β t ht.le _) (vectorProfileKernel s β t i)
    (vectorFinite_restricted_transition_law s β t hβ ht i hi) F hF B hB

theorem vectorFinite_cell_integrable_weighted_pairing (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (F : VectorState n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x,‖F x‖≤B)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫sample,Z sample*F (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal sample)
      ∂vectorDisorderBrownianMeasure n)=
      ∫sample,Z sample*(∫ y,F y ∂vectorProfileKernel s β t i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n := by
  let Y := vectorFiniteJointState (n:=n) s β t ht.le (s.q (i+1)).toNNReal
  have hY : Measurable Y := measurable_vectorFiniteJointState s β t ht.le _
  have hg : Integrable (fun sample=>F (Y sample)) (vectorDisorderBrownianMeasure n) :=
    (integrable_const B).mono' (hF.comp hY).aestronglyMeasurable (.of_forall fun _=>hB _)
  have hZg := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hp : Integrable (Z*(fun sample=>F (Y sample))) (vectorDisorderBrownianMeasure n) := by
    apply (hZi.norm.const_mul B).mono' (hZg.mul (hF.comp hY)).aestronglyMeasurable
    exact .of_forall fun sample=>by
      simp only [Pi.mul_apply,norm_mul]
      simpa only [mul_comm,Function.comp_apply] using mul_le_mul_of_nonneg_left (hB (Y sample)) (norm_nonneg (Z sample))
  exact weighted_kernelObservable_of_condExp_integrable
    (vectorBrownianFiltration n (s.q i).toNNReal) (vectorDisorderBrownianMeasure n)
    ((vectorBrownianFiltration n).le _) _ _ hg
    (vectorFinite_transition_condExp s β t hβ ht i hi F hF B hB) Z hZ.stronglyMeasurable hp

end QuantitativePaper
