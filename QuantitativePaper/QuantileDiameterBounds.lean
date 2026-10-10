module
public import QuantitativePaper.RefinedQuantileShell

@[expose] public section

/-! The literal essential pair diameter of an overlap quantile is at most one. -/
noncomputable section
open Set MeasureTheory Filter FourPapersCommon QuantitativeFollowup
namespace QuantitativePaper

theorem parisiQuantileImageDiameter_le_one (μ : Paper.ParisiMeasure) (s : ℝ) (I : Set ℝ)
    (hvol : 0<volume.real I) :
    parisiQuantileImageDiameter μ s I≤1 := by
  have hIpos : volume I≠0:=by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hvol
    exact (lt_irrefl _ hvol)
  have hPpos : (volume.restrict I).prod (volume.restrict I)≠0:=by
    intro h
    have he:=congrArg (fun P : Measure (ℝ×ℝ)=>P univ) h
    rw [←univ_prod_univ,Measure.prod_prod] at he
    simp only [Measure.restrict_apply_univ] at he
    change volume I*volume I=0 at he
    exact mul_ne_zero hIpos hIpos he
  let : NeZero ((volume.restrict I).prod (volume.restrict I)):=⟨hPpos⟩
  unfold parisiQuantileImageDiameter intervalEssentialDiameter
  refine essSup_le_of_ae_le 1 ?_ ?_
  · exact .of_forall fun p=>by
      rw [abs_le]
      constructor <;> linarith [(parisiFreeQuantile μ s p.1).property.1,
        (parisiFreeQuantile μ s p.1).property.2,(parisiFreeQuantile μ s p.2).property.1,
        (parisiFreeQuantile μ s p.2).property.2]
  · exact isCoboundedUnder_le_of_le _ (fun p=>abs_nonneg _)

end QuantitativePaper
