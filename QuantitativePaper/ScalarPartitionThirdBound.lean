module
public import QuantitativePaper.ScalarLogThirdDerivative

@[expose] public section

/-! Honest scalar partition estimates used after actual dominated
Gaussian differentiation. Bound inputs concern the literal partition jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem abs_normalized_log_second_deriv_le (Z : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hZ : ContDiffOn ℝ 2 Z U) (hpos : ∀θ∈U,0<Z θ) (a B M : ℝ)
    (ha : a≠0) (hB : 0≤B) (hM : 0≤M) {θ : ℝ} (hθ : θ∈U)
    (h1 : |deriv Z θ|≤|a| *B*Z θ)
    (h2 : |iteratedDeriv 2 Z θ|≤(|a| *M+a^2*B^2)*Z θ) :
    |iteratedDeriv 2 (fun φ=>Real.log (Z φ)/a) θ|≤M+2*|a| *B^2 := by
  have hp : 0<Z θ:=hpos θ hθ
  have hap : 0 < |a| :=abs_pos.mpr ha
  have he1 : |deriv Z θ/Z θ|≤|a| *B:=by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr h1
  have he2 : |iteratedDeriv 2 Z θ/Z θ|≤|a| *M+a^2*B^2:=by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr h2
  rw [iteratedDeriv_div_const,abs_div,iteratedDeriv_two_log_on_open Z U hU hZ hpos hθ]
  apply (div_le_iff₀ hap).mpr
  calc
    _≤|iteratedDeriv 2 Z θ/Z θ|+|(deriv Z θ/Z θ)^2|:=abs_sub _ _
    _≤(|a| *M+a^2*B^2)+(|a| *B)^2:=by
      rw [abs_pow]
      exact add_le_add he2 (pow_le_pow_left₀ (abs_nonneg _) he1 2)
    _=(M+2*|a| *B^2)*|a|:=by simp only [←sq_abs a];ring

theorem abs_normalized_log_third_deriv_le (Z : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hZ : ContDiffOn ℝ 3 Z U) (hpos : ∀θ∈U,0<Z θ) (a B M R : ℝ)
    (ha : a≠0) (hB : 0≤B) (hM : 0≤M) (hR : 0≤R)
    {θ : ℝ} (hθ : θ∈U)
    (h1 : |deriv Z θ|≤|a| *B*Z θ)
    (h2 : |iteratedDeriv 2 Z θ|≤(|a| *M+a^2*B^2)*Z θ)
    (h3 : |iteratedDeriv 3 Z θ|≤(|a| *R+3*a^2*B*M+|a| ^3*B^3)*Z θ) :
    |iteratedDeriv 3 (fun φ=>Real.log (Z φ)/a) θ|≤
      R+6*|a| *B*M+6*a^2*B^3 := by
  have hp : 0<Z θ:=hpos θ hθ
  have hap : 0 < |a| :=abs_pos.mpr ha
  have hp0 : Z θ≠0:=hp.ne'
  have he1 : |deriv Z θ/Z θ|≤|a| *B:=by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr h1
  have he2 : |iteratedDeriv 2 Z θ/Z θ|≤|a| *M+a^2*B^2:=by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr h2
  have he3 : |iteratedDeriv 3 Z θ/Z θ|≤|a| *R+3*a^2*B*M+|a| ^3*B^3:=by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr h3
  rw [iteratedDeriv_div_const,abs_div,iteratedDeriv_three_log_on_open Z U hU hZ hpos hθ]
  apply (div_le_iff₀ hap).mpr
  have hj : 3*deriv Z θ*iteratedDeriv 2 Z θ/(Z θ)^2=
      3*(deriv Z θ/Z θ)*(iteratedDeriv 2 Z θ/Z θ):=by field_simp
  rw [hj]
  calc
    _≤|iteratedDeriv 3 Z θ/Z θ|+
        |3*(deriv Z θ/Z θ)*(iteratedDeriv 2 Z θ/Z θ)|+
          |2*(deriv Z θ/Z θ)^3|:=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _≤(|a| *R+3*a^2*B*M+|a| ^3*B^3)+
        3*(|a| *B)*(|a| *M+a^2*B^2)+2*(|a| *B)^3:=by
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),
        abs_of_pos (by norm_num : (0:ℝ)<2),abs_pow]
      have ht : 3*|deriv Z θ/Z θ| *|iteratedDeriv 2 Z θ/Z θ|≤
          3*(|a| *B)*(|a| *M+a^2*B^2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left he1 (by norm_num)) he2 (abs_nonneg _)
          (by positivity : 0≤3*(|a| *B))
      have ht' : 2*|deriv Z θ/Z θ|^3≤2*(|a| *B)^3:=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) he1 3) (by norm_num : (0:ℝ)≤2)
      exact add_le_add (add_le_add he3 ht) ht'
    _=(R+6*|a| *B*M+6*a^2*B^3)*|a|:=by
      simp only [←sq_abs a]
      ring

end QuantitativePaper
