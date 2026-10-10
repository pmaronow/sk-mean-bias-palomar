module
public import FourPapersCommon.NormalizedCGF

@[expose] public section

/-! Comparison of genuine logarithmic moments under a bounded pointwise
perturbation. The random variables and exponential integrability are explicit;
no logarithmic-moment monotonicity or convexity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon

theorem cgf_add_constant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (t c : ℝ)
    (hi : Integrable (fun ω => Real.exp (t*X ω)) P) :
    cgf (fun ω => X ω+c) P t=cgf X P t+t*c := by
  rw [cgf,mgf_add_const,Real.log_mul (mgf_pos hi).ne' (Real.exp_ne_zero _),Real.log_exp]
  rfl

theorem cgf_comparison_of_bounded_increment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (t a : ℝ)
    (hX : Integrable (fun ω => Real.exp (t*X ω)) P)
    (hY : Integrable (fun ω => Real.exp (t*Y ω)) P)
    (hXY : ∀ᵐ ω ∂P, Y ω≤X ω ∧ X ω≤Y ω+a) :
    min 0 (t*a) ≤ cgf X P t-cgf Y P t ∧
      cgf X P t-cgf Y P t ≤ max 0 (t*a) := by
  have hYa : Integrable (fun ω => Real.exp (t*(Y ω+a))) P := by
    simp_rw [mul_add,Real.exp_add]
    exact hY.mul_const _
  have h0 := mgf_pos hX
  have h1 := mgf_pos hY
  have h2 := mgf_pos hYa
  have he := cgf_add_constant P Y t a hY
  by_cases ht : 0≤t
  · have hlo := mgf_mono_of_nonneg (X:=Y) (Y:=X) (hXY.mono fun _ h=>h.1) ht hX
    have hhi := mgf_mono_of_nonneg (X:=X) (Y:=fun ω=>Y ω+a)
      (hXY.mono fun _ h=>h.2) ht hYa
    have hl : cgf Y P t≤cgf X P t := Real.log_le_log h1 hlo
    have hu : cgf X P t≤cgf Y P t+t*a := by
      rw [←he]
      exact Real.log_le_log h0 hhi
    exact ⟨(min_le_left _ _).trans (sub_nonneg.mpr hl),
      (show cgf X P t-cgf Y P t≤t*a by linarith).trans (le_max_right _ _)⟩
  · have ht' : t≤0 := (lt_of_not_ge ht).le
    have hlo := mgf_anti_of_nonpos (X:=Y) (Y:=X) (hXY.mono fun _ h=>h.1) ht' hY
    have hhi := mgf_anti_of_nonpos (X:=X) (Y:=fun ω=>Y ω+a)
      (hXY.mono fun _ h=>h.2) ht' hX
    have hu : cgf X P t≤cgf Y P t := Real.log_le_log h0 hlo
    have hl : cgf Y P t+t*a≤cgf X P t := by
      rw [←he]
      exact Real.log_le_log h2 hhi
    exact ⟨(min_le_right _ _).trans (by linarith),
      (sub_nonpos.mpr hu).trans (le_max_left _ _)⟩

theorem cgf_uniform_increment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (t a : ℝ)
    (hX : Integrable (fun ω => Real.exp (t*X ω)) P)
    (hY : Integrable (fun ω => Real.exp (t*Y ω)) P)
    (hXY : ∀ᵐ ω ∂P, Y ω≤X ω ∧ X ω≤Y ω+a) :
    |cgf X P t-cgf Y P t| ≤ |t| * |a| := by
  have h:=cgf_comparison_of_bounded_increment P X Y t a hX hY hXY
  rw [←abs_mul]
  exact abs_le.mpr ⟨(by
    have hh : -|t*a|≤min 0 (t*a) := le_min (by linarith [abs_nonneg (t*a)]) (neg_abs_le _)
    exact hh.trans h.1), h.2.trans (max_le (abs_nonneg _) (le_abs_self _))⟩

end FourPapersCommon
