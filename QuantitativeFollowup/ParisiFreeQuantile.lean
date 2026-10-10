module
public import QuantitativeFollowup.ParisiFreeMeasure
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-! The literal free-quantile parameterization used in the follow-up.
It pushes `(0,1−s]` Lebesgue measure to the actual free overlap measure,
and its cumulative-mass lower bound includes every atom. -/
noncomputable section
open MeasureTheory Set Paper
open scoped ENNReal
namespace QuantitativeFollowup

def parisiFreeQuantile (μ : Paper.ParisiMeasure) (s v : ℝ) : Overlap :=
  parisiOverlapQuantile μ (s+v)

theorem parisiFreeQuantile_measurable (μ : Paper.ParisiMeasure) (s : ℝ) :
    Measurable (parisiFreeQuantile μ s) :=
  (parisiOverlapQuantile_measurable μ).comp (measurable_const.add measurable_id)

theorem volume_restrict_shift_Ioc (s : ℝ) :
    (volume.restrict (Ioc (0:ℝ) (1-s))).map (fun v => s+v)=
      volume.restrict (Ioc s 1) := by
  have hm : Measurable (fun v : ℝ => s+v) := by fun_prop
  have heq : (fun v : ℝ => s+v) ⁻¹' Ioc s 1=Ioc 0 (1-s) := by
    ext v
    simp only [mem_preimage,mem_Ioc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [←heq,←Measure.restrict_map hm measurableSet_Ioc,
    map_add_left_eq_self]

theorem parisiFreeQuantile_map (μ : Paper.ParisiMeasure) (s : ℝ) :
    (volume.restrict (Ioc (0:ℝ) (1-s))).map (parisiFreeQuantile μ s)=
      parisiFreeMeasure μ s := by
  have hm : Measurable (fun v : ℝ => s+v) := by fun_prop
  rw [parisiFreeMeasure,←volume_restrict_shift_Ioc s,
    Measure.map_map (parisiOverlapQuantile_measurable μ) hm]
  rfl

theorem parisiCDF_freeQuantile_lower (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) {v : ℝ} (hv : v∈Ioc (0:ℝ) (1-s)) :
    s+v ≤ parisiCDF μ (parisiFreeQuantile μ s v) := by
  apply le_parisiCDF_quantile
  exact ⟨by linarith [hs.1,hv.1],by linarith [hv.2]⟩

theorem integral_parisiFreeMeasure (μ : Paper.ParisiMeasure) (s : ℝ)
    (f : Overlap → ℝ) (hf : Measurable f) :
    (∫ q, f q ∂parisiFreeMeasure μ s)=
      ∫ v in Ioc (0:ℝ) (1-s), f (parisiFreeQuantile μ s v) := by
  rw [←parisiFreeQuantile_map μ s]
  exact integral_map (parisiFreeQuantile_measurable μ s).aemeasurable hf.aestronglyMeasurable

end QuantitativeFollowup
