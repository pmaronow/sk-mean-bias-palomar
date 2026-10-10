module
public import QuantitativePaper.VectorMeasureDisorderTilt

@[expose] public section

/-! Literal normalized exponential expectations under the actual initial
fractional disorder tilt. The identities apply to every real observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000
variable {n k : ℕ}

theorem integral_vectorFiniteDisorderTilt (s : RSBScheme k) (β t a : ℝ)
    (F : VectorDisorderBrownianSample n→ℝ) :
    (∫sample,F sample ∂vectorFiniteDisorderTilt s β t a)=
      (∫sample,Real.exp (a*vectorRecursion s β t sample.1 (k+2) 0)*F sample
        ∂vectorDisorderBrownianMeasure n)/vectorOuterPartition (n:=n) s β t a := by
  have hw : Measurable (fun sample : VectorDisorderBrownianSample n=>
      vectorOuterWeight s β t a sample.1) := (measurable_vectorOuterWeight s β t a).comp measurable_fst
  have hp : ∀ sample : VectorDisorderBrownianSample n,0≤vectorOuterWeight s β t a sample.1 :=
    fun _=>div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t a).le
  rw [vectorFiniteDisorderTilt,integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  change (∫sample,(ENNReal.ofReal (vectorOuterWeight s β t a sample.1)).toReal*F sample
    ∂vectorDisorderBrownianMeasure n)=_
  simp_rw [ENNReal.toReal_ofReal (hp _)]
  simp only [vectorOuterWeight]
  have he : (fun sample : VectorDisorderBrownianSample n=>
      Real.exp (a*vectorRecursion s β t sample.1 (k+2) 0)/vectorOuterPartition (n:=n) s β t a*F sample)=
      fun sample=>(Real.exp (a*vectorRecursion s β t sample.1 (k+2) 0)*F sample)/
        vectorOuterPartition (n:=n) s β t a := by funext sample;ring
  rw [he,integral_div]

theorem integral_vectorMeasureDisorderTilt (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (F : VectorDisorderBrownianSample n→ℝ) :
    (∫sample,F sample ∂vectorMeasureDisorderTilt μ β t a)=
      (∫sample,Real.exp (a*vectorMeasurePotential μ β t sample.1 0)*F sample
        ∂vectorDisorderBrownianMeasure n)/vectorMeasureOuterPartition (n:=n) μ β t a := by
  have hw : Measurable (fun sample : VectorDisorderBrownianSample n=>
      vectorMeasureOuterWeight μ β t a sample.1) :=
    (measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst
  have hp : ∀ sample : VectorDisorderBrownianSample n,0≤vectorMeasureOuterWeight μ β t a sample.1 :=
    fun _=>div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t a ht).le
  rw [vectorMeasureDisorderTilt,integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  change (∫sample,(ENNReal.ofReal (vectorMeasureOuterWeight μ β t a sample.1)).toReal*F sample
    ∂vectorDisorderBrownianMeasure n)=_
  simp_rw [ENNReal.toReal_ofReal (hp _)]
  simp only [vectorMeasureOuterWeight]
  have he : (fun sample : VectorDisorderBrownianSample n=>
      Real.exp (a*vectorMeasurePotential μ β t sample.1 0)/vectorMeasureOuterPartition (n:=n) μ β t a*F sample)=
      fun sample=>(Real.exp (a*vectorMeasurePotential μ β t sample.1 0)*F sample)/
        vectorMeasureOuterPartition (n:=n) μ β t a := by funext sample;ring
  rw [he,integral_div]

end QuantitativePaper
