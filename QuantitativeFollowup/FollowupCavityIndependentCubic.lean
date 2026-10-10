module
public import QuantitativeFollowup.FollowupCavityThreeDefectAlgebra

@[expose] public section

/-! The normalizer mark is independent of the retained tree. Its cubic
bound uses the actual product law and elementary cubic Young inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem independent_pair_product_cubic_bound {Ω Omega2 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Omega2] (P : Measure Ω) (Q : Measure Omega2)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (x y : Ω → ℝ) (z : Omega2 → ℝ) (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hxb : ∀ω,|x ω|≤2) (hyb : ∀ω,|y ω|≤2) (hzb : ∀σ,|z σ|≤2) :
    |(∫ω,x ω*y ω ∂P)*(∫σ,z σ ∂Q)| ≤
      ((∫ω,|x ω|^3 ∂P)+(∫ω,|y ω|^3 ∂P)+(∫σ,|z σ|^3 ∂Q))/3 := by
  let d : Fin 3 → Ω × Omega2 → ℝ := ![fun w => x w.1,fun w => y w.1,fun w => z w.2]
  have hm (i : Fin 3) : Measurable (d i) := by
    fin_cases i
    · exact hx.comp measurable_fst
    · exact hy.comp measurable_fst
    · exact hz.comp measurable_snd
  have hb (i : Fin 3) (w : Ω × Omega2) : |d i w|≤2 := by
    fin_cases i
    · exact hxb _
    · exact hyb _
    · exact hzb _
  have hi (i : Fin 3) : Integrable (fun w => |d i w|^3) (P.prod Q) := by
    apply (integrable_const (8:ℝ)).mono' ((hm i).abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun w => by
      rw [Real.norm_of_nonneg (by positivity : 0≤|d i w|^3)]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hb i w) 3).trans_eq (by norm_num)
  have hprod : Integrable (fun w => d 0 w*d 1 w*d 2 w) (P.prod Q) := by
    apply (integrable_const (8:ℝ)).mono' (((hm 0).mul (hm 1)).mul (hm 2)).aestronglyMeasurable
    exact .of_forall fun w => by
      change ‖d 0 w*d 1 w*d 2 w‖≤8
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul (hb 0 w) (hb 1 w) (abs_nonneg _) (by norm_num))
        (hb 2 w) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hle := integral_mono hprod.norm ((((hi 0).add (hi 1)).add (hi 2)).div_const 3)
    (fun w => by
      convert! abs_three_product_le_cubic_mean (d 0 w) (d 1 w) (d 2 w) using 1 <;> simp only [Real.norm_eq_abs,Pi.add_apply])
  rw [integral_div] at hle
  simp only [Pi.add_apply] at hle
  have hsum := integral_add ((hi 0).add (hi 1)) (hi 2)
  have hfirst := integral_add (hi 0) (hi 1)
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum,hfirst] at hle
  have hh := (norm_integral_le_integral_norm (f:=fun w => d 0 w*d 1 w*d 2 w)).trans hle
  change |∫w : Ω × Omega2,x w.1*y w.1*z w.2 ∂P.prod Q| ≤
    ((∫w : Ω × Omega2,|x w.1|^3 ∂P.prod Q)+(∫w : Ω × Omega2,|y w.1|^3 ∂P.prod Q)+
      (∫w : Ω × Omega2,|z w.2|^3 ∂P.prod Q))/3 at hh
  rw [integral_prod_mul (μ:=P) (ν:=Q) (fun ω => x ω*y ω) z,
    integral_fun_fst (μ:=P) (ν:=Q) (fun ω => |x ω|^3),
    integral_fun_fst (μ:=P) (ν:=Q) (fun ω => |y ω|^3),
    integral_fun_snd (μ:=P) (ν:=Q) (fun σ => |z σ|^3)] at hh
  simpa only [probReal_univ,one_smul] using hh


end QuantitativeFollowup
