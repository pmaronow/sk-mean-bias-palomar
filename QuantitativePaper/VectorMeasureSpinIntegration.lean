module
public import QuantitativePaper.VectorMeasureSpinLaw

@[expose] public section

/-! Actual terminal Gibbs marking preserves the sample marginal and
integrates every bounded sample weight against the literal terminal mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorMeasureSpinPathLaw_fst (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    (vectorMeasureSpinPathLaw (n:=n) μ β t a ht).fst=vectorMeasureDisorderTilt μ β t a := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  unfold vectorMeasureSpinPathLaw
  exact Measure.fst_compProd _ _

theorem integral_vectorMeasureSpinPathLaw_sample (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (F : VectorDisorderBrownianSample n→ℝ) (hF : Measurable F) :
    (∫p,F p.1 ∂vectorMeasureSpinPathLaw μ β t a ht)=
      ∫sample,F sample ∂vectorMeasureDisorderTilt μ β t a := by
  rw [←vectorMeasureSpinPathLaw_fst μ β t a ht]
  exact (integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable).symm

theorem integral_vectorMeasureSpinPathLaw_terminal_weight (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) (d : Configuration n→ℝ) :
    (∫p,Z p.1*d p.2 ∂vectorMeasureSpinPathLaw μ β t a ht)=
      ∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)) d
        ∂vectorMeasureDisorderTilt μ β t a := by
  haveI := vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let D : ℝ := ∑σ : Configuration n,|d σ|
  have hd (σ : Configuration n) : ‖d σ‖≤D := by
    rw [Real.norm_eq_abs]
    change |d σ|≤∑τ : Configuration n,|d τ|
    exact Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hm : Measurable (fun p : VectorDisorderBrownianSample n×Configuration n=>Z p.1*d p.2) :=
    (hZ.comp measurable_fst).mul ((measurable_of_finite d).comp measurable_snd)
  have hi : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>Z p.1*d p.2)
      (vectorMeasureSpinPathLaw μ β t a ht) := by
    apply (integrable_const ((C : ℝ)*D)).mono' hm.aestronglyMeasurable
    exact .of_forall fun p=>by
      rw [norm_mul]
      exact mul_le_mul (hC p.1) (hd p.2) (norm_nonneg _) C.coe_nonneg
  rw [vectorMeasureSpinPathLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (∫σ,Z sample*d σ ∂terminalLaw
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)))=_
    rw [integral_const_mul,integral_terminalLaw]

end QuantitativePaper
