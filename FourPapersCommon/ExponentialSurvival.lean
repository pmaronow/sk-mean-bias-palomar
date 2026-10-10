module
public import FourPapersCommon.ExponentialMoments
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

@[expose] public section

/-! The actual canonical exponential survival function and nonnegative support. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon

 theorem noAtoms_expMeasure (r : ℝ) : NullSingletonClass (expMeasure r) := by
  unfold expMeasure gammaMeasure
  infer_instance

 theorem real_expMeasure_Ici (r : ℝ) (hr : 0<r) (x : ℝ) :
    (expMeasure r).real (Ici x)=Real.exp (-r*max x 0) := by
  let _:=isProbabilityMeasure_expMeasure hr
  let _:=noAtoms_expMeasure r
  have hm : (expMeasure r).real (Iio x)=(expMeasure r).real (Iic x) := by
    simp only [measureReal_def]
    rw [measure_congr Iio_ae_eq_Iic]
  rw [←compl_Iio,measureReal_compl measurableSet_Iio,probReal_univ,hm,
    ←cdf_eq_real,cdf_expMeasure_eq hr x]
  by_cases hx : 0≤x
  · simp only [if_pos hx,max_eq_left hx]
    ring_nf
  · simp [hx,max_eq_right (le_of_not_ge hx)]

 theorem ae_nonneg_expMeasure (r : ℝ) (hr : 0<r) :
    ∀ᵐx ∂expMeasure r,0≤x := by
  let _:=isProbabilityMeasure_expMeasure hr
  have h : (expMeasure r).real (Ici (0:ℝ))=1 := by
    rw [real_expMeasure_Ici r hr]
    simp
  have hc : (expMeasure r).real (Iio (0:ℝ))=0 := by
    have hh:=measureReal_add_measureReal_compl (μ:=expMeasure r) (measurableSet_Iio (a:=(0:ℝ)))
    simp only [compl_Iio,probReal_univ] at hh
    linarith
  rw [ae_iff]
  have he : {a : ℝ | ¬0≤a}=Iio (0:ℝ) := by ext a; simp
  rw [he]
  exact (ENNReal.toReal_eq_zero_iff _).mp hc |>.resolve_right (measure_ne_top _ _)
end FourPapersCommon
