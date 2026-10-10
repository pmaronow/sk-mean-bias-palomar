module
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The product of two genuine second-moment kernels integrates to an
actual square on the independent product probability space. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon
variable {I Ω₀ Ω₁ : Type*} [MeasurableSpace I] [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
variable (ν : Measure I) [IsFiniteMeasure ν]
variable (P : Measure Ω₀) [IsProbabilityMeasure P]
variable (Q : Measure Ω₁) [IsProbabilityMeasure Q]
set_option maxHeartbeats 1000000

theorem bounded_product_kernel_square (G : Ω₀×I→ℝ) (H : Ω₁×I→ℝ)
    (hG : Measurable G) (hH : Measurable H)
    (K L : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hbG : ∀z,‖G z‖≤K) (hbH : ∀z,‖H z‖≤L) :
    (∫ω : Ω₀×Ω₁,(∫p,G (ω.1,p)*H (ω.2,p) ∂ν)^2 ∂P.prod Q)=
      ∫pq : I×I,(∫ω,G (ω,pq.1)*G (ω,pq.2) ∂P)*
        (∫ω,H (ω,pq.1)*H (ω,pq.2) ∂Q) ∂ν.prod ν := by
  let W : (Ω₀×Ω₁)×(I×I)→ℝ:=fun z=>
    (G (z.1.1,z.2.1)*G (z.1.1,z.2.2))*
      (H (z.1.2,z.2.1)*H (z.1.2,z.2.2))
  have hm : Measurable W :=
    ((hG.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
      (hG.comp (measurable_fst.fst.prodMk measurable_snd.snd))).mul
    ((hH.comp (measurable_fst.snd.prodMk measurable_snd.fst)).mul
      (hH.comp (measurable_fst.snd.prodMk measurable_snd.snd)))
  have hb (z : (Ω₀×Ω₁)×(I×I)) : ‖W z‖≤K^2*L^2 := by
    change ‖(G (z.1.1,z.2.1)*G (z.1.1,z.2.2))*
      (H (z.1.2,z.2.1)*H (z.1.2,z.2.2))‖≤K^2*L^2
    simp only [norm_mul]
    calc
      _≤(K*K)*(L*L) := mul_le_mul
        (mul_le_mul (hbG _) (hbG _) (norm_nonneg _) hK)
        (mul_le_mul (hbH _) (hbH _) (norm_nonneg _) hL)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hK hK)
      _=K^2*L^2 := by ring
  have hi : Integrable W ((P.prod Q).prod (ν.prod ν)):=
    (integrable_const (K^2*L^2)).mono' hm.aestronglyMeasurable (.of_forall hb)
  calc
    _=∫ω : Ω₀×Ω₁,∫pq : I×I,W (ω,pq) ∂ν.prod ν ∂P.prod Q := by
      apply integral_congr_ae
      exact .of_forall fun ω=>by
        dsimp only
        rw [pow_two,←integral_prod_mul]
        apply integral_congr_ae
        exact .of_forall fun pq=>by dsimp [W];ring
    _=∫pq : I×I,∫ω : Ω₀×Ω₁,W (ω,pq) ∂P.prod Q ∂ν.prod ν :=
      integral_integral_swap (f:=fun ω pq=>W (ω,pq)) hi
    _=_ := by
      apply integral_congr_ae
      exact .of_forall fun pq=>integral_prod_mul
        (fun ω=>G (ω,pq.1)*G (ω,pq.2))
        (fun ω=>H (ω,pq.1)*H (ω,pq.2))

theorem bounded_product_kernel_integral_nonneg (G : Ω₀×I→ℝ) (H : Ω₁×I→ℝ)
    (hG : Measurable G) (hH : Measurable H)
    (K L : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hbG : ∀z,‖G z‖≤K) (hbH : ∀z,‖H z‖≤L) :
    0≤∫pq : I×I,(∫ω,G (ω,pq.1)*G (ω,pq.2) ∂P)*
      (∫ω,H (ω,pq.1)*H (ω,pq.2) ∂Q) ∂ν.prod ν := by
  rw [←bounded_product_kernel_square ν P Q G H hG hH K L hK hL hbG hbH]
  exact integral_nonneg fun _=>sq_nonneg _

end FourPapersCommon
