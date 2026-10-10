module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Genuine integrability and integral stability from a uniform pointwise
difference bound on a probability space. -/
noncomputable section
open MeasureTheory Filter
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrable_of_uniform_sub_bound {f g : Ω→ℝ} (hf : Integrable f P)
    (hg : AEStronglyMeasurable g P) (C : ℝ) (hb : ∀sample,|g sample-f sample|≤C) :
    Integrable g P := by
  apply (hf.norm.add (integrable_const C)).mono' hg
  exact Eventually.of_forall (fun sample=>by
    change |g sample|≤|f sample|+C
    have ht := norm_add_le (g sample-f sample) (f sample)
    rw [sub_add_cancel] at ht
    simp only [Real.norm_eq_abs] at ht
    linarith [hb sample])

theorem integral_sub_le_uniform_bound {f g : Ω→ℝ} (hf : Integrable f P)
    (hg : Integrable g P) (C : ℝ) (hb : ∀sample,|f sample-g sample|≤C) :
    |(∫sample,f sample ∂P)-(∫sample,g sample ∂P)|≤C := by
  rw [←integral_sub hf hg,←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := P) (f := fun sample=>f sample-g sample) (C := C)
    (Eventually.of_forall (fun sample=>by simpa only [Real.norm_eq_abs] using hb sample))
  simpa only [probReal_univ,one_mul,mul_one] using hh

end FourPapersCommon
