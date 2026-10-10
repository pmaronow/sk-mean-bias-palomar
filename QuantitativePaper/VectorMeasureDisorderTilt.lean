module
public import QuantitativePaper.VectorFiniteTiltedPathLaw
public import QuantitativePaper.VectorMeasurePotential

@[expose] public section

/-! The actual normalized fractional disorder law for an arbitrary profile.
Its exponential moment and total mass are proved from the constructed
potential, and the independent Wiener factor retains total mass one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorMeasureOuterPartition (μ : Paper.ParisiMeasure) (β t a : ℝ) : ℝ :=
  ∫ p,Real.exp (a*vectorMeasurePotential μ β t p 0) ∂completionLaw n

theorem measurable_vectorMeasurePotential_initial (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) : Measurable (fun p : Couplings n×ℝ=>vectorMeasurePotential μ β t p 0) := by
  simpa only [Function.comp_def,id_eq] using
    (continuous_vectorMeasurePotential_joint μ β t ht).measurable.comp
      (measurable_id.prodMk measurable_const)

theorem vectorMeasureOuterPartition_pos (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    0<vectorMeasureOuterPartition (n:=n) μ β t a := by
  apply (integral_pos_iff_support_of_nonneg (fun _=>(Real.exp_pos _).le)
    (integrable_exp_vectorMeasurePotential μ β t ht a 0)).mpr
  have hs : Function.support (fun p : Couplings n×ℝ=>
      Real.exp (a*vectorMeasurePotential μ β t p 0))=univ := by
    ext p
    simp [Function.mem_support,Real.exp_ne_zero]
  rw [hs]
  simp

def vectorMeasureOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ) (p : Couplings n×ℝ) : ℝ :=
  Real.exp (a*vectorMeasurePotential μ β t p 0)/vectorMeasureOuterPartition (n:=n) μ β t a

theorem measurable_vectorMeasureOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : Measurable (vectorMeasureOuterWeight (n:=n) μ β t a) := by
  unfold vectorMeasureOuterWeight
  exact (Real.measurable_exp.comp (measurable_const.mul
    (measurable_vectorMeasurePotential_initial μ β t ht))).div_const _

def vectorMeasureOuterLaw (μ : Paper.ParisiMeasure) (β t a : ℝ) : Measure (Couplings n×ℝ) :=
  (completionLaw n).withDensity (fun p=>ENNReal.ofReal (vectorMeasureOuterWeight μ β t a p))

theorem vectorMeasureOuterLaw_probability (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    IsProbabilityMeasure (vectorMeasureOuterLaw (n:=n) μ β t a) := by
  constructor
  rw [vectorMeasureOuterLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  unfold vectorMeasureOuterWeight
  rw [←ofReal_integral_eq_lintegral_ofReal
    ((integrable_exp_vectorMeasurePotential μ β t ht a 0).div_const _)
    (.of_forall fun p=>div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t a ht).le),
    integral_div,←vectorMeasureOuterPartition,div_self (vectorMeasureOuterPartition_pos μ β t a ht).ne']
  norm_num

def vectorMeasureDisorderTilt (μ : Paper.ParisiMeasure) (β t a : ℝ) :
    Measure (VectorDisorderBrownianSample n) :=
  (vectorDisorderBrownianMeasure n).withDensity
    (fun sample=>ENNReal.ofReal (vectorMeasureOuterWeight μ β t a sample.1))

theorem vectorMeasureDisorderTilt_probability (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    IsProbabilityMeasure (vectorMeasureDisorderTilt (n:=n) μ β t a) := by
  constructor
  rw [vectorMeasureDisorderTilt,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [←lintegral_map (measurable_vectorMeasureOuterWeight μ β t a ht).ennreal_ofReal measurable_fst,
    (hasLaw_initialVectorDisorder n).map_eq]
  haveI := vectorMeasureOuterLaw_probability (n:=n) μ β t a ht
  have h := measure_univ (μ:=vectorMeasureOuterLaw (n:=n) μ β t a)
  rw [vectorMeasureOuterLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at h
  exact h

end QuantitativePaper
