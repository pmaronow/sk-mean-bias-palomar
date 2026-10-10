module
public import FourPapersCommon.PastIntegralComparison
public import FourPapersCommon.WeightedConditionalIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A genuine conditional comparison commutes with a deterministic bounded
probability kernel. No jointly chosen version of conditional expectations
of the individual integrands is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {Ω I : Type*} [m0 : MeasurableSpace Ω] [MeasurableSpace I]

theorem conditional_kernel_comparison_of_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure I) [IsFiniteMeasure ν] (m : MeasurableSpace Ω) (hm : m≤m0)
    (S : Ω→ℝ) (hS : StronglyMeasurable[m] S) (hiS : Integrable S P)
    (F : I×Ω→ℝ)
    (hF : @Measurable (I×Ω) ℝ (@Prod.instMeasurableSpace I Ω ‹MeasurableSpace I› m0) _ F)
    (B : ℝ) (hB : 0≤B) (hbF : ∀z,‖F z‖≤B)
    (κ : I→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ ν)
    (hκpos : ∀i,0≤κ i) (hnormal : (∫i,κ i ∂ν)=1)
    (hcompare : ∀ᵐi ∂ν,κ i≠0→S≤ᵐ[P]fun ω=>2*P[(fun ω=>F (i,ω))|m] ω) :
      S≤ᵐ[P]fun ω=>2*P[(fun ω=>∫i,κ i*F (i,ω) ∂ν)|m] ω := by
  let G : Ω→ℝ:=fun ω=>∫i,κ i*F (i,ω) ∂ν
  letI : MeasurableSpace Ω:=m0
  have hi : Integrable (fun z : I×Ω=>κ z.1*F z) (ν.prod P) := by
    apply ((hiκ.norm.const_mul B).comp_fst P).mono'
      ((hκ.comp measurable_fst).mul hF).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖κ z.1*F z‖≤B*‖κ z.1‖
      rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbF z) (norm_nonneg (κ z.1))
  have hiG : Integrable G P:=hi.integral_prod_right
  apply ae_le_of_past_bounded_nonneg_tests m P hm S (fun ω=>2*P[G|m] ω)
    hS (stronglyMeasurable_condExp.const_mul 2) hiS (integrable_condExp.const_mul 2)
  intro Z hZ hZpos hZbound
  have hZm:=hZ.mono hm le_rfl
  have hZS : Integrable (fun ω=>Z ω*S ω) P:=hiS.bdd_mul hZm.aestronglyMeasurable (.of_forall hZbound)
  have hZG : Integrable (fun ω=>Z ω*G ω) P:=hiG.bdd_mul hZm.aestronglyMeasurable (.of_forall hZbound)
  have hZprod : Integrable (fun z : I×Ω=>κ z.1*(Z z.2*F z)) (ν.prod P) := by
    apply ((hiκ.norm.const_mul B).comp_fst P).mono'
      ((hκ.comp measurable_fst).mul ((hZm.comp measurable_snd).mul hF)).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖κ z.1*(Z z.2*F z)‖≤B*‖κ z.1‖
      rw [norm_mul,norm_mul]
      have hz : ‖Z z.2‖*‖F z‖≤B:=
        (mul_le_mul (hZbound z.2) (hbF z) (norm_nonneg _) zero_le_one).trans_eq (by ring)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz (norm_nonneg (κ z.1))
  let H : I→ℝ:=fun i=>∫ω,Z ω*F (i,ω) ∂P
  have hiH : Integrable (fun i=>κ i*H i) ν := by
    convert hZprod.integral_prod_left using 1
    funext i
    exact (integral_const_mul _ _).symm
  have hH : ∀ᵐi ∂ν,κ i*(∫ω,Z ω*S ω ∂P)≤2*(κ i*H i) := by
    filter_upwards [hcompare] with i hi
    by_cases hz : κ i=0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    have hFi : Integrable (fun ω=>F (i,ω)) P := by
      apply (integrable_const B).mono'
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      exact .of_forall fun ω=>hbF (i,ω)
    have hZFi : Integrable (fun ω=>Z ω*F (i,ω)) P:=hFi.bdd_mul hZm.aestronglyMeasurable (.of_forall hZbound)
    have hZCE : Integrable (fun ω=>Z ω*P[(fun ω=>F (i,ω))|m] ω) P:=
      (integrable_condExp (μ:=P) (m:=m) (f:=fun ω=>F (i,ω))).bdd_mul
        hZm.aestronglyMeasurable (.of_forall hZbound)
    have hpoint : (fun ω=>Z ω*S ω)≤ᵐ[P]fun ω=>2*(Z ω*P[(fun ω=>F (i,ω))|m] ω) :=
      (hi hz).mono fun ω hω=>by
        simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hω (hZpos ω)
    have hh:=integral_mono_ae hZS (hZCE.const_mul 2) hpoint
    rw [integral_const_mul,integral_known_mul_condExp m hm Z _ hZ.stronglyMeasurable hFi hZFi] at hh
    have hh':(∫ω,Z ω*S ω ∂P)≤2*H i:=hh
    simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hh' (hκpos i)
  have hiC : Integrable (fun i=>κ i*(∫ω,Z ω*S ω ∂P)) ν:=hiκ.mul_const _
  have h:=integral_mono_ae hiC (hiH.const_mul 2) hH
  rw [integral_mul_const,hnormal,one_mul,integral_const_mul] at h
  have hswap : (∫i,κ i*H i ∂ν)=∫ω,Z ω*G ω ∂P := by
    have hs:=integral_integral_swap (μ:=ν) (ν:=P)
      (f:=fun i ω=>κ i*(Z ω*F (i,ω))) hZprod
    simp only [integral_const_mul] at hs
    change (∫i,κ i*H i ∂ν)=∫ω,Z ω*G ω ∂P
    calc
      _=∫ω,∫i,κ i*(Z ω*F (i,ω)) ∂ν ∂P := hs
      _=_ := by
        apply integral_congr_ae
        exact .of_forall fun ω=>by
          simp_rw [mul_left_comm (κ _) (Z ω)]
          rw [integral_const_mul]
  rw [hswap] at h
  have hCE : (∫ω,Z ω*(2*P[G|m] ω) ∂P)=2*(∫ω,Z ω*G ω ∂P) := by
    simp_rw [mul_left_comm (Z _) (2:ℝ)]
    rw [integral_const_mul,integral_known_mul_condExp m hm Z G hZ.stronglyMeasurable hiG hZG]
  rw [hCE]
  exact h

theorem conditional_kernel_comparison (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure I) [IsFiniteMeasure ν] (m : MeasurableSpace Ω) (hm : m≤m0)
    (S : Ω→ℝ) (hS : StronglyMeasurable[m] S) (hiS : Integrable S P)
    (F : I×Ω→ℝ)
    (hF : @Measurable (I×Ω) ℝ (@Prod.instMeasurableSpace I Ω ‹MeasurableSpace I› m0) _ F)
    (B : ℝ) (hB : 0≤B) (hbF : ∀z,‖F z‖≤B)
    (κ : I→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K) (hbκ : ∀i,‖κ i‖≤K)
    (hκpos : ∀i,0≤κ i) (hnormal : (∫i,κ i ∂ν)=1)
    (hcompare : ∀ᵐi ∂ν,κ i≠0→S≤ᵐ[P]fun ω=>2*P[(fun ω=>F (i,ω))|m] ω) :
      S≤ᵐ[P]fun ω=>2*P[(fun ω=>∫i,κ i*F (i,ω) ∂ν)|m] ω := by
  letI : MeasurableSpace Ω:=m0
  exact conditional_kernel_comparison_of_integrable P ν m hm S hS hiS F hF B hB hbF κ hκ
    ((integrable_const K).mono' hκ.aestronglyMeasurable (.of_forall hbκ)) hκpos hnormal hcompare

end FourPapersCommon
