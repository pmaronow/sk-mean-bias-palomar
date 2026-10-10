module
public import QuantitativePaper.VectorColeHopf

@[expose] public section

/-! The actual Gaussian Cole--Hopf step at every real mass. Reflection
through mass zero preserves field Lipschitz bounds and the sup contraction;
the expectation branch is retained literally. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem vectorColeHopfStep_mass_reflection {n : ℕ} (c m : ℝ) (f : Field n→ℝ)
    (x : Field n) :
    vectorColeHopfStep c m f x = -vectorColeHopfStep c (-m) (fun y=>-f y) x := by
  by_cases hm : m=0
  · subst m
    simp only [neg_zero,vectorColeHopfStep,ite_true,integral_neg,neg_neg]
  · have hp : vectorStepPartition c (-m) (fun y=>-f y) x=vectorStepPartition c m f x := by
      unfold vectorStepPartition
      simp only [neg_mul_neg]
    simp only [vectorColeHopfStep,hm,neg_ne_zero.mpr hm,ite_false,hp,div_neg,neg_neg]

theorem vectorColeHopfStep_lipschitz_all_mass {n : ℕ} (f : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (c m : ℝ) :
    LipschitzWith K (vectorColeHopfStep c m f) := by
  by_cases hm : 0 ≤ m
  · exact vectorColeHopfStep_lipschitz f K hf c m hm
  · have hh := (vectorColeHopfStep_lipschitz (fun y=>-f y) K hf.neg c (-m)
        (by linarith)).neg
    have he : vectorColeHopfStep c m f=(fun x=>-vectorColeHopfStep c (-m) (fun y=>-f y) x) :=
      funext (vectorColeHopfStep_mass_reflection c m f)
    rw [he]
    exact hh

private theorem abs_vectorColeHopfStep_comparison_nonneg {n : ℕ}
    (f g : Field n→ℝ) (K L : ℝ≥0) (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (c m : ℝ) (hm : 0 ≤ m) (x y : Field n) (R : ℝ)
    (hfg : ∀z, |f (fieldShift c x z)-g (fieldShift c y z)|≤R) :
    |vectorColeHopfStep c m f x-vectorColeHopfStep c m g y|≤R := by
  by_cases hm0 : m=0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    rw [←integral_sub (integrable_vectorStep_input f K hf c x)
      (integrable_vectorStep_input g L hg c y)]
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (f:=fun z=>f (fieldShift c x z)-g (fieldShift c y z))
      (μ:=fieldGaussian n) (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hfg z)
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hb (f g : Field n→ℝ) (K L : ℝ≥0) (hf : LipschitzWith K f) (hg : LipschitzWith L g)
        (x y : Field n) (hfg : ∀z,f (fieldShift c x z)-g (fieldShift c y z)≤R) :
        vectorColeHopfStep c m f x-vectorColeHopfStep c m g y≤R := by
      have hZ : vectorStepPartition c m f x≤Real.exp (m*R)*vectorStepPartition c m g y := by
        rw [vectorStepPartition,vectorStepPartition,←integral_const_mul]
        apply integral_mono (integrable_exp_vectorStep f K hf c m x)
          ((integrable_exp_vectorStep g L hg c m y).const_mul _)
        intro z
        calc
          Real.exp (m*f (fieldShift c x z))≤Real.exp (m*(R+g (fieldShift c y z))) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hfg z]) hm)
          _=Real.exp (m*R)*Real.exp (m*g (fieldShift c y z)) := by rw [mul_add,Real.exp_add]
      have hl := Real.log_le_log (vectorStepPartition_pos f K hf c m x) hZ
      rw [Real.log_mul (Real.exp_ne_zero _) (vectorStepPartition_pos g L hg c m y).ne',Real.log_exp] at hl
      simp only [vectorColeHopfStep,hm0,ite_false]
      rw [←sub_div,div_le_iff₀ hmp]
      linarith
    apply abs_le.mpr
    constructor
    · have hh := hb g f L K hg hf y x (fun z=>by linarith [(abs_le.mp (hfg z)).1])
      linarith
    · exact hb f g K L hf hg x y (fun z=>(abs_le.mp (hfg z)).2)

theorem abs_vectorColeHopfStep_comparison_all_mass {n : ℕ}
    (f g : Field n→ℝ) (K L : ℝ≥0) (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (c m : ℝ) (x y : Field n) (R : ℝ)
    (hfg : ∀z, |f (fieldShift c x z)-g (fieldShift c y z)|≤R) :
    |vectorColeHopfStep c m f x-vectorColeHopfStep c m g y|≤R := by
  by_cases hm : 0 ≤ m
  · exact abs_vectorColeHopfStep_comparison_nonneg f g K L hf hg c m hm x y R hfg
  · rw [vectorColeHopfStep_mass_reflection c m f,vectorColeHopfStep_mass_reflection c m g,
      neg_sub_neg,abs_sub_comm]
    apply abs_vectorColeHopfStep_comparison_nonneg (fun z=>-f z) (fun z=>-g z)
      K L hf.neg hg.neg c (-m) (by linarith) x y R
    intro z
    simpa only [neg_sub_neg,abs_sub_comm] using hfg z

end QuantitativePaper
