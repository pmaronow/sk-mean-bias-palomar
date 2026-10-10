module
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Equality of ordinary local Stieltjes measures from equality of their
actual primitives on a closed interval. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup

theorem stieltjes_restrict_Ioc_congr (f g : StieltjesFunction ℝ) (a b : ℝ)
    (hfg : ∀x∈Icc a b, f x=g x) :
    f.measure.restrict (Ioc a b)=g.measure.restrict (Ioc a b) := by
  apply Measure.ext_of_Ioc
  intro l u _hlu
  have he : Ioc l u∩Ioc a b=Ioc (max l a) (min u b) := by
    ext x
    simp only [mem_inter_iff,mem_Ioc,max_lt_iff,le_min_iff]
    tauto
  rw [Measure.restrict_apply measurableSet_Ioc,Measure.restrict_apply measurableSet_Ioc,he]
  by_cases hab : max l a < min u b
  · have hl : max l a ∈ Icc a b := ⟨le_max_right _ _,hab.le.trans (min_le_right _ _)⟩
    have hu : min u b ∈ Icc a b := ⟨(le_max_right l a).trans hab.le,min_le_right _ _⟩
    rw [StieltjesFunction.measure_Ioc,StieltjesFunction.measure_Ioc,hfg _ hl,hfg _ hu]
  · rw [Ioc_eq_empty hab,measure_empty,measure_empty]

theorem stieltjes_restrict_Ioo_congr (f g : StieltjesFunction ℝ) (a b : ℝ)
    (hfg : ∀x∈Icc a b, f x=g x) :
    f.measure.restrict (Ioo a b)=g.measure.restrict (Ioo a b) := by
  have h := congrArg (fun μ : Measure ℝ => μ.restrict (Ioo a b)) (stieltjes_restrict_Ioc_congr f g a b hfg)
  simpa only [Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo a b ⊆ Ioc a b from fun _ hx => ⟨hx.1,hx.2.le⟩)] using h

end QuantitativeFollowup
