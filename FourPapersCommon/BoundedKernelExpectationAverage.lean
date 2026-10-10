module
public import FourPapersCommon.BoundedKernelAverageFubini

@[expose] public section

/-! A deterministic finite-measure average commutes with a bounded
probability expectation. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {Q S : Type*} [MeasurableSpace Q] [MeasurableSpace S]

theorem bounded_kernel_expectation_average (ν : Measure Q) (P : Measure S)
    [IsFiniteMeasure ν] [IsProbabilityMeasure P]
    (K : Q→ℝ) (R : S→ℝ) (A : Q→S→ℝ)
    (hK : Measurable K) (hR : Measurable R) (hA : Measurable (Function.uncurry A))
    (CK CR CA : ℝ) (hKb : ∀q,‖K q‖≤CK) (hRb : ∀s,‖R s‖≤CR)
    (hAb : ∀q s,‖A q s‖≤CA) (hCK : 0≤CK) (hCR : 0≤CR) :
    (∫q,K q*(∫s,R s*A q s ∂P) ∂ν)=∫s,R s*(∫q,K q*A q s ∂ν) ∂P := by
  let F := fun q s=>K q*(R s*A q s)
  have hF : Measurable (Function.uncurry F) :=
    (hK.comp measurable_fst).mul ((hR.comp measurable_snd).mul hA)
  have hb (qs : Q×S) : ‖F qs.1 qs.2‖≤CK*(CR*CA) := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact mul_le_mul (hKb qs.1) (mul_le_mul (hRb qs.2) (hAb qs.1 qs.2)
      (norm_nonneg _) hCR) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCK
  have hi : Integrable (Function.uncurry F) (ν.prod P) :=
    (integrable_const (CK*(CR*CA))).mono' hF.aestronglyMeasurable (.of_forall hb)
  have he (q : Q) : K q*(∫s,R s*A q s ∂P)=∫s,F q s ∂P :=
    (integral_const_mul _ _).symm
  simp_rw [he]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact .of_forall fun s=>by
    dsimp only [F]
    simp_rw [mul_left_comm (K _) (R s)]
    exact integral_const_mul _ _

end FourPapersCommon
