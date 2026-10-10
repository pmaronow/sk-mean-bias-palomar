module
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Literal pullback-event integration, without an integrability premise. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem integral_pullback_indicator_one_mul (P : Measure Ω) (H : Ω→A)
    (hH : Measurable H) (S : Set A) (hS : MeasurableSet S) (F : Ω→ℝ) :
    (∫sample,S.indicator (fun _=>(1 : ℝ)) (H sample)*F sample ∂P)=
      ∫sample in H ⁻¹' S,F sample ∂P := by
  rw [←integral_indicator (hH hS)]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    by_cases hs : H sample∈S <;> simp [hs]

end FourPapersCommon
