module
public import FourPapersCommon.NormalizedCGF

@[expose] public section

/-! Genuine sup-distance stability of the normalized logarithmic moment,
including its expectation branch at tilt zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon

theorem cgf_sub_le_of_sup_distance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω→ℝ) (m R : ℝ)
    (hX : Integrable (fun ω => Real.exp (m*X ω)) P)
    (hY : Integrable (fun ω => Real.exp (m*Y ω)) P)
    (hxy : ∀ω,|X ω-Y ω| ≤ R) :
    cgf X P m-cgf Y P m ≤ |m| * R := by
  have hZ : mgf X P m ≤ Real.exp (|m| * R)*mgf Y P m := by
    unfold mgf
    rw [←integral_const_mul]
    apply integral_mono hX (hY.const_mul _)
    intro ω
    dsimp only
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : m*(X ω-Y ω) ≤ |m| * R :=
      (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hxy ω) (abs_nonneg _))
    linarith
  have hh := Real.log_le_log (mgf_pos hX) hZ
  rw [Real.log_mul (Real.exp_ne_zero _) (mgf_pos hY).ne',Real.log_exp] at hh
  exact sub_le_iff_le_add.mpr (by simpa only [cgf,add_comm] using hh)

theorem abs_cgf_sub_le_of_sup_distance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω→ℝ) (m R : ℝ)
    (hX : Integrable (fun ω => Real.exp (m*X ω)) P)
    (hY : Integrable (fun ω => Real.exp (m*Y ω)) P)
    (hxy : ∀ω,|X ω-Y ω| ≤ R) :
    |cgf X P m-cgf Y P m| ≤ |m| * R := by
  rw [abs_le]
  have hrev := cgf_sub_le_of_sup_distance P Y X m R hY hX
    (fun ω => (abs_sub_comm _ _).trans_le (hxy ω))
  exact ⟨by linarith,cgf_sub_le_of_sup_distance P X Y m R hX hY hxy⟩

theorem normalizedCGF_sup_distance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω→ℝ) (R : ℝ)
    (hX : ∀m,Integrable (fun ω => Real.exp (m*X ω)) P)
    (hY : ∀m,Integrable (fun ω => Real.exp (m*Y ω)) P)
    (hxy : ∀ω,|X ω-Y ω| ≤ R) (m : ℝ) :
    |normalizedCGF P X m-normalizedCGF P Y m| ≤ R := by
  by_cases hm : m=0
  · subst m
    have hX0 : (0 : ℝ)∈interior (integrableExpSet X P) := by
      have he : integrableExpSet X P=univ := Set.eq_univ_iff_forall.mpr hX
      rw [he,interior_univ];trivial
    have hY0 : (0 : ℝ)∈interior (integrableExpSet Y P) := by
      have he : integrableExpSet Y P=univ := Set.eq_univ_iff_forall.mpr hY
      rw [he,interior_univ];trivial
    rw [normalizedCGF_zero P X hX0,normalizedCGF_zero P Y hY0,
      ←integral_sub (integrable_of_mem_interior_integrableExpSet hX0)
        (integrable_of_mem_interior_integrableExpSet hY0)]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=P) (f:=fun ω => X ω-Y ω)
        (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hxy ω)
  · rw [normalizedCGF_of_ne P X hm,normalizedCGF_of_ne P Y hm,←sub_div,abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hm)).mpr
    simpa only [mul_comm] using abs_cgf_sub_le_of_sup_distance P X Y m R (hX m) (hY m) hxy

end QuantitativePaper
