module
public import QuantitativeFollowup.VectorMeanIncrement

@[expose] public section

/-! The full root-floor domain of the mean-increment lemma, including the
vacuous endpoint at full root mass. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}

theorem parisiFreeMeasure_one (μ : Paper.ParisiMeasure) : parisiFreeMeasure μ 1=0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [parisiFreeMeasure_univ,sub_self,ENNReal.ofReal_zero]

theorem vector_mean_increment_towards_support_full (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) (r : Paper.Overlap) :
    |vectorMeanOverlap (n:=n) μ β t a ht.le r-vectorMeanOverlap (n:=n) μ β t a ht.le q|≤
      2*|(r:ℝ)-q| := by
  by_cases hs1 : s=1
  · subst s
    simpa only [parisiFreeMeasure_one,Measure.support_zero,mem_empty_iff_false] using hq
  · exact vector_mean_increment_towards_support hn μ s ⟨hs.1,lt_of_le_of_ne hs.2 hs1⟩
      hμ β t a hβ ht ha hmin q hq r

theorem vector_spinMean_increment_towards_support_full (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) (r : Paper.Overlap) (hrq : r≤q) :
    (∫sample,‖vectorMeasureSpinMean μ β t ht.le q sample-
        vectorMeasureSpinMean μ β t ht.le r sample‖^2∂vectorMeasureDisorderTilt (n:=n) μ β t a)≤
      2*(n:ℝ)*((q:ℝ)-r) := by
  by_cases hs1 : s=1
  · subst s
    simpa only [parisiFreeMeasure_one,Measure.support_zero,mem_empty_iff_false] using hq
  · exact vector_spinMean_increment_towards_support_bound hn μ s ⟨hs.1,lt_of_le_of_ne hs.2 hs1⟩
      hμ β t a hβ ht ha hmin q hq r hrq

end QuantitativeFollowup
