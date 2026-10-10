module
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Bounded deterministic-kernel averages may be moved inside an actual
probability expectation. All product integrability is derived here. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {I Q S : Type*} [MeasurableSpace I] [MeasurableSpace Q] [MeasurableSpace S]

theorem bounded_kernel_average_fubini (η : Measure I) (ν : Measure Q) (P : Measure S)
    [IsFiniteMeasure η] [IsFiniteMeasure ν] [IsProbabilityMeasure P]
    (K : I→Q→ℝ) (R : I→S→ℝ) (A : Q→S→ℝ)
    (hK : Measurable (Function.uncurry K)) (hR : Measurable (Function.uncurry R))
    (hA : Measurable (Function.uncurry A))
    (CK CR CA : ℝ) (hKbound : ∀i q,‖K i q‖≤CK)
    (hRbound : ∀i s,‖R i s‖≤CR) (hAbound : ∀q s,‖A q s‖≤CA)
    (hCK : 0≤CK) (hCR : 0≤CR) (hCA : 0≤CA) :
    (∫q,∫i,K i q*(∫s,R i s*A q s ∂P) ∂η ∂ν)=
      ∫i,∫s,R i s*(∫q,K i q*A q s ∂ν) ∂P ∂η := by
  let F := fun (i : I) (q : Q) (s : S)=>K i q*(R i s*A q s)
  have hF : Measurable (fun z : (I×Q)×S=>F z.1.1 z.1.2 z.2) :=
    (hK.comp measurable_fst).mul
      ((hR.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hA.comp (measurable_fst.snd.prodMk measurable_snd)))
  have hFb (i : I) (q : Q) (s : S) : ‖F i q s‖≤CK*(CR*CA) := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact mul_le_mul (hKbound i q) (mul_le_mul (hRbound i s) (hAbound q s)
      (norm_nonneg _) hCR) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCK
  have hGm : Measurable (fun iq : I×Q=>∫s,F iq.1 iq.2 s ∂P) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have hGi : Integrable (fun iq : I×Q=>∫s,F iq.1 iq.2 s ∂P) (η.prod ν) := by
    apply (integrable_const (CK*(CR*CA))).mono' hGm.aestronglyMeasurable
    exact .of_forall fun iq=>by
      simpa using norm_integral_le_of_norm_le_const (μ:=P) (.of_forall (hFb iq.1 iq.2))
  have he (i : I) (q : Q) : K i q*(∫s,R i s*A q s ∂P)=(∫s,F i q s ∂P) :=
    (integral_const_mul _ _).symm
  simp_rw [he]
  rw [←integral_integral_swap hGi]
  apply integral_congr_ae
  exact .of_forall fun i=>by
    dsimp only
    have hFi : Measurable (fun qs : Q×S=>F i qs.1 qs.2) :=
      hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hi : Integrable (fun qs : Q×S=>F i qs.1 qs.2) (ν.prod P) :=
      (integrable_const (CK*(CR*CA))).mono' hFi.aestronglyMeasurable
        (.of_forall fun qs=>hFb i qs.1 qs.2)
    rw [integral_integral_swap hi]
    apply integral_congr_ae
    exact .of_forall fun s=>by
      dsimp only
      dsimp only [F]
      simp_rw [mul_left_comm (K i _) (R i s)]
      exact integral_const_mul _ _

end FourPapersCommon
