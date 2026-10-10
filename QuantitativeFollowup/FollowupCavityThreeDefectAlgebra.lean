module
public import QuantitativeFollowup.FollowupCavityMarkedDefectBounds

@[expose] public section

/-! Cubic domination for the actual physical overlap defects. The measure
may include deterministic level marks and independent continuation trees.
No third-moment or pair-marginal estimate is supplied as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

def cavityRestOverlap (n : ℕ) (σ τ : Configuration (n+1)) : ℝ :=
  (∑l : Fin n, Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc))/(n:ℝ)

theorem cavityRestOverlap_abs_le_one (n : ℕ) (σ τ : Configuration (n+1)) :
    |cavityRestOverlap n σ τ|≤1 := by
  have hs (x : Bool) : |Paper.spinSign x|=1 := by cases x <;> norm_num [Paper.spinSign]
  have hi : |∑l : Fin n, Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc)|≤(n:ℝ) := by
    calc
      _≤∑l : Fin n, |Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc)| :=
        Finset.abs_sum_le_sum_abs _ _
      _=(n:ℝ) := by simp only [abs_mul, hs, one_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hn : n=0
  · subst n; simp [cavityRestOverlap]
  · rw [cavityRestOverlap, abs_div, show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr (by simpa using hi)

theorem cavitySpinOverlapDefect_abs_eq_rest (n : ℕ) (q : ℝ)
    (σ τ : Configuration (n+1)) :
    |cavitySpinOverlapDefect n q σ τ|=|cavityRestOverlap n σ τ-q| := by
  have hs (x : Bool) : |Paper.spinSign x|=1 := by cases x <;> norm_num [Paper.spinSign]
  rw [cavitySpinOverlapDefect_eq, abs_mul, abs_mul, hs, hs, one_mul, one_mul]
  rfl

theorem abs_three_product_le_cubic_mean (x y z : ℝ) :
    |x*y*z|≤(|x|^3+|y|^3+|z|^3)/3 := by
  have hp : 0≤(|x|+|y|+|z|)*((|x|-|y|)^2+(|y|-|z|)^2+(|z|-|x|)^2) :=
    mul_nonneg (by positivity) (by positivity)
  rw [abs_mul, abs_mul]
  nlinarith only [hp]

theorem cavityThreeDefectProduct_abs_le_cubic_mean (n : ℕ)
    (q : Fin 3 → ℝ) (σ τ : Fin 3 → Configuration (n+1)) :
    |cavitySpinOverlapDefect n (q 0) (σ 0) (τ 0)*
      cavitySpinOverlapDefect n (q 1) (σ 1) (τ 1)*
      cavitySpinOverlapDefect n (q 2) (σ 2) (τ 2)|≤
      (|cavityRestOverlap n (σ 0) (τ 0)-q 0|^3+
        |cavityRestOverlap n (σ 1) (τ 1)-q 1|^3+
        |cavityRestOverlap n (σ 2) (τ 2)-q 2|^3)/3 := by
  simpa only [cavitySpinOverlapDefect_abs_eq_rest] using
    abs_three_product_le_cubic_mean
      (cavitySpinOverlapDefect n (q 0) (σ 0) (τ 0))
      (cavitySpinOverlapDefect n (q 1) (σ 1) (τ 1))
      (cavitySpinOverlapDefect n (q 2) (σ 2) (τ 2))

theorem integral_cavityThreeDefectProduct_le_cubic_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (n : ℕ) (q : Fin 3 → Ω → Paper.Overlap) (hq : ∀i, Measurable (q i))
    (σ τ : Fin 3 → Ω → Configuration (n+1))
    (hσ : ∀i, Measurable (σ i)) (hτ : ∀i, Measurable (τ i)) :
    (∫ω, |cavitySpinOverlapDefect n (q 0 ω) (σ 0 ω) (τ 0 ω)*
      cavitySpinOverlapDefect n (q 1 ω) (σ 1 ω) (τ 1 ω)*
      cavitySpinOverlapDefect n (q 2 ω) (σ 2 ω) (τ 2 ω)|∂P)≤
      ((∫ω, |cavityRestOverlap n (σ 0 ω) (τ 0 ω)-(q 0 ω:ℝ)|^3∂P)+
        (∫ω, |cavityRestOverlap n (σ 1 ω) (τ 1 ω)-(q 1 ω:ℝ)|^3∂P)+
        (∫ω, |cavityRestOverlap n (σ 2 ω) (τ 2 ω)-(q 2 ω:ℝ)|^3∂P))/3 := by
  let d : Fin 3 → Ω → ℝ := fun i ω=>cavitySpinOverlapDefect n (q i ω) (σ i ω) (τ i ω)
  have hm (i : Fin 3) : Measurable (d i) := by
    have hrest : Measurable (fun ω=>cavityRestOverlap n (σ i ω) (τ i ω)) :=
      (measurable_of_finite (Function.uncurry (cavityRestOverlap n))).comp
        ((hσ i).prodMk (hτ i))
    have heps : Measurable (fun ω=>Paper.spinSign (σ i ω (Fin.last n))*Paper.spinSign (τ i ω (Fin.last n))) :=
      ((measurable_of_finite (fun s : Configuration (n+1)=>Paper.spinSign (s (Fin.last n)))).comp (hσ i)).mul
        ((measurable_of_finite (fun s : Configuration (n+1)=>Paper.spinSign (s (Fin.last n)))).comp (hτ i))
    convert heps.mul (hrest.sub (measurable_subtype_coe.comp (hq i))) using 1
    funext ω
    exact cavitySpinOverlapDefect_eq n _ _ _
  have hb (i : Fin 3) (ω : Ω) : |d i ω|≤2 := cavitySpinOverlapDefect_abs_le_two n _ (q i ω).property _ _
  have hi (i : Fin 3) : Integrable (fun ω=>|d i ω|^3) P := by
    apply (integrable_const (8:ℝ)).mono' ((hm i).abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun ω=>by
      rw [Real.norm_of_nonneg (by positivity : 0≤|d i ω|^3)]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hb i ω) 3).trans_eq (by norm_num)
  have hprod : Integrable (fun ω=>|d 0 ω*d 1 ω*d 2 ω|) P := by
    apply (integrable_const (8:ℝ)).mono' (((hm 0).mul (hm 1)).mul (hm 2)).abs.aestronglyMeasurable
    exact .of_forall fun ω=>by
      change ‖|d 0 ω*d 1 ω*d 2 ω|‖≤8
      rw [Real.norm_of_nonneg (abs_nonneg _), abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul (hb 0 ω) (hb 1 ω) (abs_nonneg _) (by norm_num))
        (hb 2 ω) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hh:=integral_mono hprod ((((hi 0).add (hi 1)).add (hi 2)).div_const 3)
    (fun ω=>abs_three_product_le_cubic_mean (d 0 ω) (d 1 ω) (d 2 ω))
  rw [integral_div] at hh
  simp only [Pi.add_apply] at hh
  have hsum:=integral_add ((hi 0).add (hi 1)) (hi 2)
  have hfirst:=integral_add (hi 0) (hi 1)
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum, hfirst] at hh
  simpa only [d, cavitySpinOverlapDefect_abs_eq_rest] using hh

end QuantitativeFollowup
