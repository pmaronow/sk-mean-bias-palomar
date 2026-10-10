module
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

/-! The genuine layer-cake representation of a function in [0,1]. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem integral_layercake_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω→ℝ) (hi : Integrable f P)
    (hpos : 0≤ᵐ[P]f) (hle : f≤ᵐ[P]fun _=>1) :
    (∫ω,f ω ∂P)=(∫τ in Ioo (0:ℝ) 1,P.real {ω | τ<f ω}) := by
  rw [hi.integral_eq_integral_meas_lt hpos,←integral_indicator measurableSet_Ioi,
    ←integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact .of_forall fun τ=>by
    by_cases hτ : 0<τ
    · by_cases hl : τ<1
      · rw [indicator_of_mem (show τ∈Ioi (0:ℝ) from hτ),
          indicator_of_mem (show τ∈Ioo (0:ℝ) 1 from ⟨hτ,hl⟩)]
      · have he : P {ω | τ<f ω}=0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [hle] with ω hω
          exact not_lt.mpr (hω.trans (not_lt.mp hl))
        rw [indicator_of_mem (show τ∈Ioi (0:ℝ) from hτ),
          indicator_of_notMem (show τ∉Ioo (0:ℝ) 1 from fun h=>hl h.2)]
        simp only [Measure.real,he,ENNReal.toReal_zero]
    · rw [indicator_of_notMem (show τ∉Ioi (0:ℝ) from hτ),
        indicator_of_notMem (show τ∉Ioo (0:ℝ) 1 from fun h=>hτ h.1)]

theorem measurable_real_superlevels {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω→ℝ) :
    Measurable (fun τ : ℝ=>P.real {ω | τ<f ω}) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono (fun ω hω=>hab.trans_lt hω)

theorem integrable_real_superlevels_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω→ℝ) :
    IntegrableOn (fun τ : ℝ=>P.real {ω | τ<f ω}) (Ioo 0 1) := by
  apply Integrable.of_bound (measurable_real_superlevels P f).aestronglyMeasurable (P.real univ)
  exact .of_forall fun τ=>by
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_mono (subset_univ _)

end FourPapersCommon
