module
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityCore
public import QuantitativePaper.VectorMeasureCovarianceMatrix

@[expose] public section

/-! Literal covariance-square moments of the changing marked posterior law
are expressed through a conditional expectation under one fixed Wiener law.
The actual outer density has all finite Gaussian moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorBasePairObservable (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (i j : Fin n) : VectorDisorderBrownianSample n→ℝ :=
  vectorMeasureTerminalObservable μ β t ht (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))

def vectorBaseMeanProduct (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (i j : Fin n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorMeasureSpinMean μ β t ht q sample i*vectorMeasureSpinMean μ β t ht q sample j

def vectorBaseOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=vectorMeasureOuterWeight μ β t a sample.1

theorem vectorBasePairObservable_bound (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (i j : Fin n) (sample : VectorDisorderBrownianSample n) :
    ‖vectorBasePairObservable μ β t ht i j sample‖≤1 := by
  rw [Real.norm_eq_abs]
  exact terminalMean_bound _ _ 1 (fun σ=>by simp [abs_mul,Paper.abs_spinSign])

theorem vectorBaseMeanProduct_bound (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (i j : Fin n) (sample : VectorDisorderBrownianSample n) :
    ‖vectorBaseMeanProduct μ β t ht q i j sample‖≤1 := by
  rw [vectorBaseMeanProduct,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (mul_le_mul (vectorMeasureSpinMean_component_bound μ β t ht q sample i)
    (vectorMeasureSpinMean_component_bound μ β t ht q sample j) (abs_nonneg _) zero_le_one).trans_eq (by ring)

theorem memLp_vectorBasePairObservable (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (i j : Fin n) : MemLp (vectorBasePairObservable μ β t ht i j) 2 (vectorDisorderBrownianMeasure n) := by
  apply MemLp.of_bound (measurable_vectorMeasureTerminalObservable μ β t ht _).aestronglyMeasurable 1
  exact .of_forall (vectorBasePairObservable_bound μ β t ht i j)

theorem memLp_vectorBaseMeanProduct (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (i j : Fin n) :
    MemLp (vectorBaseMeanProduct μ β t ht q i j) 2 (vectorDisorderBrownianMeasure n) := by
  have hi:Measurable (fun sample=>vectorMeasureSpinMean (n:=n) μ β t ht q sample i):=
    (adapted_vectorMeasureSpinMean_component μ β t ht q i).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hj:Measurable (fun sample=>vectorMeasureSpinMean (n:=n) μ β t ht q sample j):=
    (adapted_vectorMeasureSpinMean_component μ β t ht q j).mono ((vectorBrownianFiltration n).le _) le_rfl
  exact MemLp.of_bound (hi.mul hj).aestronglyMeasurable 1
    (.of_forall (vectorBaseMeanProduct_bound μ β t ht q i j))

theorem memLp_vectorBaseOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    MemLp (vectorBaseOuterWeight (n:=n) μ β t a) 2 (vectorDisorderBrownianMeasure n) := by
  have hm:Measurable (vectorBaseOuterWeight (n:=n) μ β t a):=
    (measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi:= (hasLaw_initialVectorDisorder n).integrable_comp
    ((integrable_exp_vectorMeasurePotential (n:=n) μ β t ht (2*a) 0).div_const
      ((vectorMeasureOuterPartition (n:=n) μ β t a)^2))
  convert hi using 1
  funext sample
  simp only [Function.comp_def,vectorBaseOuterWeight,vectorMeasureOuterWeight,div_pow]
  congr 1
  rw [←Real.exp_nat_mul]
  congr 1
  ring

theorem vectorMeasureSpinCovariance_entry_square_eq_base (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    (∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i j)^2
      ∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
    ∫sample,vectorBaseOuterWeight μ β t a sample*
      ((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i j|
        vectorBrownianFiltration n (q:ℝ).toNNReal] sample-vectorBaseMeanProduct μ β t ht q i j sample)^2
      ∂vectorDisorderBrownianMeasure n := by
  have he:=vectorMeasureTerminalObservable_condExp_eq_base (n:=n) μ β t a ht q
    (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))
  have hh:(∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i j)^2
      ∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
    ∫sample,((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i j|
      vectorBrownianFiltration n (q:ℝ).toNNReal] sample-vectorBaseMeanProduct μ β t ht q i j sample)^2
      ∂vectorMeasureDisorderTilt μ β t a:=by
    apply integral_congr_ae
    filter_upwards [he] with sample hs
    simp only [vectorMeasureSpinCovariance,vectorBasePairObservable,vectorBaseMeanProduct,hs]
  rw [hh,vectorMeasureDisorderTilt]
  have hd:Measurable (fun sample:VectorDisorderBrownianSample n=>
      ENNReal.ofReal (vectorMeasureOuterWeight μ β t a sample.1)):=by
    exact ((measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    simp only [smul_eq_mul]
    have hp:0≤vectorMeasureOuterWeight (n:=n) μ β t a sample.1:=
      div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t a ht).le
    rw [ENNReal.toReal_ofReal hp]
    rfl

end QuantitativePaper
