module
public import QuantitativeFollowup.ParisiQuantileLaw
public import QuantitativePaper.ScalarFloorContinuity
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Sub

@[expose] public section

/-! The actual free overlap measure, obtained by removing the prescribed
root atom. Its quantile representation is constructed from Lebesgue
measure rather than assumed. -/
noncomputable section
open MeasureTheory Set Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup

def parisiFreeMeasure (μ : Paper.ParisiMeasure) (s : ℝ) : Measure Paper.Overlap :=
  (volume.restrict (Ioc s 1)).map (parisiOverlapQuantile μ)

theorem parisiFreeMeasure_univ (μ : Paper.ParisiMeasure) (s : ℝ) :
    parisiFreeMeasure μ s univ=ENNReal.ofReal (1-s) := by
  rw [parisiFreeMeasure,Measure.map_apply (parisiOverlapQuantile_measurable μ)
    MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply_univ,Real.volume_Ioc]

instance parisiFreeMeasure_finite (μ : Paper.ParisiMeasure) (s : ℝ) :
    IsFiniteMeasure (parisiFreeMeasure μ s) :=
  ⟨by rw [parisiFreeMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem parisiOverlapQuantile_root (μ : Paper.ParisiMeasure) (s : ℝ)
    (hμ : μ ∈ scalarFloor s) {u : ℝ} (hu : u∈Ioc (0:ℝ) s) :
    parisiOverlapQuantile μ u=zeroOverlap := by
  have hs := scalarFloor_cdf_lower hμ (show (0:ℝ) ≤ 0 by norm_num)
  have hu₁ : u ≤ 1 := hu.2.trans (hs.trans (parisiCDF_le_one μ 0))
  apply Subtype.ext
  apply le_antisymm
  · apply (parisiQuantile_le_iff μ u 0 (by constructor <;> norm_num)).mpr
    rw [quantileLevel_eq ⟨hu.1.le,hu₁⟩]
    exact hu.2.trans hs
  · exact (parisiQuantile_mem μ u).1

theorem rootQuantile_map (μ : Paper.ParisiMeasure) (s : ℝ) (hs : 0 ≤ s)
    (hμ : μ ∈ scalarFloor s) :
    (volume.restrict (Ioc (0:ℝ) s)).map (parisiOverlapQuantile μ)=
      ENNReal.ofReal s • Measure.dirac zeroOverlap := by
  have heq : parisiOverlapQuantile μ =ᵐ[volume.restrict (Ioc (0:ℝ) s)]
      (fun _ => zeroOverlap) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact parisiOverlapQuantile_root μ s hμ hu
  rw [Measure.map_congr heq,Measure.map_const,Measure.restrict_apply_univ,
    Real.volume_Ioc,sub_zero]

theorem root_add_parisiFreeMeasure (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor s) :
    ENNReal.ofReal s • Measure.dirac zeroOverlap+parisiFreeMeasure μ s=
      (μ : Measure Paper.Overlap) := by
  rw [←rootQuantile_map μ s hs.1 hμ,parisiFreeMeasure,←Measure.map_add]
  rw [←Measure.restrict_union (Ioc_disjoint_Ioc_of_le (show s ≤ s from le_rfl))
    measurableSet_Ioc,Ioc_union_Ioc_eq_Ioc hs.1 hs.2]
  exact parisiOverlapQuantile_map_unitLaw μ
  exact parisiOverlapQuantile_measurable μ

theorem parisiFreeMeasure_eq_sub (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor s) :
    parisiFreeMeasure μ s=(μ : Measure Paper.Overlap)-
      ENNReal.ofReal s • Measure.dirac zeroOverlap := by
  haveI : IsFiniteMeasure (ENNReal.ofReal s • Measure.dirac zeroOverlap) := by
    constructor
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,
      mul_one]
    exact ENNReal.ofReal_lt_top
  rw [←root_add_parisiFreeMeasure μ s hs hμ,add_comm,Measure.add_sub_cancel]

theorem parisiFreeMeasure_cdf (μ : Paper.ParisiMeasure) (s x : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor s) (hx : x∈Icc (0:ℝ) 1) :
    parisiFreeMeasure μ s {q : Paper.Overlap | (q:ℝ) ≤ x}=
      ENNReal.ofReal (parisiCDF μ x-s) := by
  have hm : MeasurableSet {q : Paper.Overlap | (q:ℝ) ≤ x} :=
    measurable_subtype_coe measurableSet_Iic
  rw [parisiFreeMeasure,Measure.map_apply (parisiOverlapQuantile_measurable μ) hm,
    Measure.restrict_apply ((parisiOverlapQuantile_measurable μ)
      hm)]
  have heq : parisiOverlapQuantile μ ⁻¹' {q : Paper.Overlap | (q:ℝ) ≤ x} ∩ Ioc s 1=
      Ioc s (parisiCDF μ x) := by
    ext u
    simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,mem_Ioc,parisiOverlapQuantile]
    constructor
    · rintro ⟨hQ,hu₀,hu₁⟩
      exact ⟨hu₀,by simpa only [quantileLevel_eq ⟨hs.1.trans hu₀.le,hu₁⟩] using
        (parisiQuantile_le_iff μ u x hx).mp hQ⟩
    · rintro ⟨hu₀,huc⟩
      have hu₁ := huc.trans (parisiCDF_le_one μ x)
      refine ⟨?_,hu₀,hu₁⟩
      apply (parisiQuantile_le_iff μ u x hx).mpr
      simpa only [quantileLevel_eq ⟨hs.1.trans hu₀.le,hu₁⟩] using huc
  rw [heq,Real.volume_Ioc]

end QuantitativeFollowup
