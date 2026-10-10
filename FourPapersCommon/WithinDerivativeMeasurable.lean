module
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

@[expose] public section

/-! Measurability of genuine within derivatives, obtained from countably many
secants in the parameter domain. In particular, closed interval endpoints do
not require any extension of the family outside its domain. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem aestronglyMeasurable_of_ae_hasDerivWithinAt_along_sequence
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ) (s : Set ℝ) (u : ℝ) (v : ℕ → ℝ)
    (hv : ∀ n, v n ∈ s \ {u}) (ht : Tendsto v atTop (𝓝 u))
    (hFu : AEStronglyMeasurable (F u) P)
    (hFv : ∀ n, AEStronglyMeasurable (F (v n)) P)
    (hd : ∀ᵐ x ∂P, HasDerivWithinAt (fun z => F z x) (G x) s u) :
    AEStronglyMeasurable G P := by
  have htv : Tendsto v atTop (𝓝[s \ {u}] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall hv⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => slope (fun z => F z x) u (v n))
  · intro n
    simpa only [slope_def_module] using
      ((hFv n).fun_sub hFu).fun_const_smul ((v n - u)⁻¹)
  · exact hd.mono fun x hx =>
      (hasDerivWithinAt_iff_tendsto_slope.mp hx).comp htv

theorem aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1)
    (hF : ∀ v ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (F v) P)
    (hd : ∀ᵐ x ∂P,
      HasDerivWithinAt (fun v => F v x) (G x) (Icc (0 : ℝ) 1) u) :
    AEStronglyMeasurable G P := by
  have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rcases lt_or_eq_of_le hu.2 with hut | rfl
  · let v : ℕ → ℝ := fun n => u + (1 - u) / ((n : ℝ) + 1)
    have hv : ∀ n, v n ∈ Icc (0 : ℝ) 1 \ {u} := by
      intro n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hp : 0 < (1 - u) / ((n : ℝ) + 1) := by positivity
      have hb : (1 - u) / ((n : ℝ) + 1) ≤ 1 - u :=
        div_le_self (by linarith) hden
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp [v]; linarith [hu.1]
      · dsimp [v]; linarith
      · change v n ≠ u
        dsimp [v]; linarith
    have ht : Tendsto v atTop (𝓝 u) := by
      simpa only [v, div_eq_mul_inv, one_div, one_mul, mul_zero, add_zero] using
        (hz.const_mul (1 - u)).const_add u
    exact aestronglyMeasurable_of_ae_hasDerivWithinAt_along_sequence F G
      (Icc (0 : ℝ) 1) u v hv ht (hF u hu) (fun n => hF (v n) (hv n).1) hd
  · let v : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
    have hv : ∀ n, v n ∈ Icc (0 : ℝ) 1 \ {1} := by
      intro n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
        simpa only [div_one] using div_le_self (show (0 : ℝ) ≤ 1 by norm_num) hden
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp [v]; linarith
      · dsimp [v]; linarith
      · change v n ≠ 1
        dsimp [v]; linarith
    have ht : Tendsto v atTop (𝓝 (1 : ℝ)) := by
      simpa only [v, sub_zero] using tendsto_const_nhds.sub hz
    exact aestronglyMeasurable_of_ae_hasDerivWithinAt_along_sequence F G
      (Icc (0 : ℝ) 1) 1 v hv ht (hF 1 hu) (fun n => hF (v n) (hv n).1) hd

end FourPapersCommon
