module
public import QuantitativeFollowup.ParisiQuantile
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! The actual Lebesgue pushforward law of the generalized inverse CDF. -/
noncomputable section
open MeasureTheory Set Paper
open scoped ENNReal
namespace QuantitativeFollowup

def unitQuantileLaw : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)

instance unitQuantileLaw_probability : IsProbabilityMeasure unitQuantileLaw := by
  constructor
  simp [unitQuantileLaw,Real.volume_Ioc]

theorem parisiQuantile_preimage_Iic_inter (μ : Paper.ParisiMeasure) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) 1) :
    parisiQuantile μ ⁻¹' Iic x ∩ Ioc (0:ℝ) 1=Ioc 0 (parisiCDF μ x) := by
  ext u
  simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_Ioc]
  constructor
  · rintro ⟨hqu,hu₀,hu₁⟩
    exact ⟨hu₀,by simpa only [quantileLevel_eq ⟨hu₀.le,hu₁⟩] using
      (parisiQuantile_le_iff μ u x hx).mp hqu⟩
  · rintro ⟨hu₀,huc⟩
    have hu₁ := huc.trans (parisiCDF_le_one μ x)
    refine ⟨?_,hu₀,hu₁⟩
    apply (parisiQuantile_le_iff μ u x hx).mpr
    simpa only [quantileLevel_eq ⟨hu₀.le,hu₁⟩] using huc

theorem parisiQuantile_map_unitLaw (μ : Paper.ParisiMeasure) :
    unitQuantileLaw.map (parisiQuantile μ)=(μ : Measure Overlap).map Subtype.val := by
  have hQ := parisiQuantile_measurable μ
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hQ measurableSet_Iic,unitQuantileLaw,
    Measure.restrict_apply (hQ measurableSet_Iic)]
  by_cases hn : x<0
  · have hempty : parisiQuantile μ ⁻¹' Iic x ∩ Ioc (0:ℝ) 1=∅ := by
      ext u
      simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      rintro ⟨hux,_⟩
      exact not_le_of_gt (hn.trans_le (parisiQuantile_mem μ u).1) hux
    rw [hempty,measure_empty,←ProbabilityTheory.ofReal_cdf]
    rw [←FRSB.parisiCDF_eq_realCDF,FRSB.parisiCDF_eq_zero_of_lt_zero μ hn]
    simp
  by_cases ht : 1≤x
  · have hfull : parisiQuantile μ ⁻¹' Iic x ∩ Ioc (0:ℝ) 1=Ioc 0 1 := by
      apply inter_eq_right.mpr
      intro u hu
      exact (parisiQuantile_mem μ u).2.trans ht
    rw [hfull,Real.volume_Ioc,←ProbabilityTheory.ofReal_cdf,
      ←FRSB.parisiCDF_eq_realCDF,parisiCDF_eq_one_of_one_le μ ht]
    norm_num
  · have hx : x∈Icc (0:ℝ) 1 := ⟨not_lt.mp hn,(not_le.mp ht).le⟩
    rw [parisiQuantile_preimage_Iic_inter μ x hx,Real.volume_Ioc,
      ←ProbabilityTheory.ofReal_cdf,←FRSB.parisiCDF_eq_realCDF]
    simp

def parisiOverlapQuantile (μ : Paper.ParisiMeasure) (u : ℝ) : Overlap :=
  ⟨parisiQuantile μ u,parisiQuantile_mem μ u⟩

theorem parisiOverlapQuantile_measurable (μ : Paper.ParisiMeasure) :
    Measurable (parisiOverlapQuantile μ) := (parisiQuantile_measurable μ).subtype_mk

theorem parisiOverlapQuantile_map_unitLaw (μ : Paper.ParisiMeasure) :
    unitQuantileLaw.map (parisiOverlapQuantile μ)=(μ : Measure Overlap) := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe (parisiOverlapQuantile_measurable μ)]
  exact parisiQuantile_map_unitLaw μ

end QuantitativeFollowup
