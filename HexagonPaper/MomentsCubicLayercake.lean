module
public import FourPapersCommon.CubicSquareLayercake
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Full square layer cake, keeping the manuscript's upper endpoint one. -/
noncomputable section
open Set MeasureTheory intervalIntegral FourPapersCommon
open scoped NNReal ENNReal
namespace HexagonPaper
set_option maxHeartbeats 2200000

 theorem cubic_moment_full_square_layercake {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω→ℝ) (hf : Measurable f)
    (hb : ∀ω,|f ω|≤1) (z : ℝ) (hz : z∈Ioc (0:ℝ) 1) :
    (∫ω,|f ω|^3 ∂P)≤z*(∫ω,f ω^2 ∂P)+
      (∫θ in Ioo z 1,∫ω,{ω | θ < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P) :=by
  let T : ℝ→ℝ:=fun θ=>∫ω,{ω | θ < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P
  let K:=∫ω,f ω^2 ∂P
  have hiF : Integrable (fun ω=>f ω^2) P:=Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
    (.of_forall fun ω=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hb ω))
  have hTbound (θ : ℝ) : 0≤T θ ∧ T θ≤K:=by
    refine ⟨integral_nonneg (fun ω=>Set.indicator_nonneg (fun _ _=>sq_nonneg _) _),?_⟩
    exact MeasureTheory.integral_mono (hiF.indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs)) hiF
      (fun ω=>by simp only [Set.indicator,mem_setOf_eq];split_ifs <;> first | exact le_rfl | positivity)
  have hTanti : Antitone T:=by
    intro θ η hθη
    apply MeasureTheory.integral_mono (hiF.indicator (measurableSet_lt (measurable_const (a:=η)) hf.abs))
      (hiF.indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs))
    intro ω
    simp only [Set.indicator,mem_setOf_eq]
    split_ifs <;> first | exact le_rfl | positivity | exfalso; linarith
  have hiT (a b : ℝ) (hab : a≤b) : IntervalIntegrable T volume a b:=by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    apply Integrable.of_bound hTanti.measurable.aestronglyMeasurable K
    exact .of_forall fun θ=>by rw [Real.norm_of_nonneg (hTbound θ).1];exact (hTbound θ).2
  have hi0z:=hiT 0 z hz.1.le
  have hiz1:=hiT z 1 hz.2
  have h0:=intervalIntegral.integral_mono hz.1.le hi0z intervalIntegrable_const
    (fun θ=>(hTbound θ).2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h0
  rw [integral_abs_cube_eq_square_layercake P f hf hb,
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le zero_le_one,
    ←integral_add_adjacent_intervals hi0z hiz1]
  change (∫θ in 0..z,T θ)+(∫θ in z..1,T θ)≤_
  rw [intervalIntegral.integral_of_le hz.2,integral_Ioc_eq_integral_Ioo]
  exact add_le_add h0 le_rfl

/-- Display 079: the actual scalar inequality preceding product Fubini. -/
theorem abs_cube_le_full_square_layercake (y z : ℝ) (hy : |y|≤1)
    (hz : z∈Ioc (0:ℝ) 1) :
    |y|^3 ≤ z*y^2+∫θ in Ioc z 1,y^2*{r : ℝ | r < |y| }.indicator (fun _=>1) θ :=by
  have h:=cubic_moment_full_square_layercake (Measure.dirac ()) (fun _ : Unit=>y)
    measurable_const (fun _=>hy) z hz
  simp only [integral_dirac] at h
  rw [integral_Ioc_eq_integral_Ioo]
  convert h using 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  simp only [Set.indicator,mem_setOf_eq]
  split_ifs <;> ring

end HexagonPaper
