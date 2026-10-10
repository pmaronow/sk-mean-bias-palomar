module
public import QuantitativePaper.VectorFeedbackControlGap
public import QuantitativePaper.VectorMeasureMild
public import Mathlib.Probability.Moments.IntegrableExpMul

@[expose] public section

/-! Genuine vector control upper bound and attained representation for the
constructed arbitrary probability profile, including zero diffusion.
All objective integrability and the actual feedback state are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorParisiControlObjective (μ : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) : ℝ :=
  ∫sample,vectorTerminalPotential n β t sample.1
    (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
      vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample ∂vectorDisorderBrownianMeasure n

theorem integrable_vectorMeasurePotential (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (x : Field n) :
    Integrable (fun p : Couplings n×ℝ=>vectorMeasurePotential μ β t p x) (completionLaw n) := by
  have he : integrableExpSet (fun p : Couplings n×ℝ=>vectorMeasurePotential μ β t p x)
      (completionLaw n)=univ := by
    ext a
    simp only [integrableExpSet,mem_setOf_eq,mem_univ,iff_true]
    exact integrable_exp_vectorMeasurePotential μ β t ht a x
  apply integrable_of_mem_interior_integrableExpSet
  rw [he]
  simp

theorem vectorMeasurePotential_zero_diffusion (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (hc : (1-t)*β^2=0) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasurePotential μ β t p x=vectorTerminalPotential n β t p x := by
  rw [←vectorMeasureTailPotential_zero μ β t ht p x]
  exact vectorMeasureTailPotential_zero_diffusion μ β t ht hc ⟨0,by constructor <;>norm_num⟩ p x

@[simp] theorem vectorControlledState_zero_rate (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : vectorControlledState 0 μ A r sample=0 := by
  simp [vectorControlledState,vectorControlDrift,vectorIntegratedDrift]

@[simp] theorem vectorParisiControlIntegratedCost_zero_rate (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (sample : VectorDisorderBrownianSample n) :
    vectorParisiControlIntegratedCost 0 μ A sample=0 := by
  simp [vectorParisiControlIntegratedCost,vectorParisiControlCost]

theorem vectorMeasureControlGap_zero_diffusion (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (hc : (1-t)*β^2=0)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureControlGap μ β t A sample=0 := by
  rw [vectorMeasureControlGap,hc,vectorControlledState_zero_rate,
    vectorParisiControlIntegratedCost_zero_rate,vectorMeasurePotential_zero_diffusion μ β t ht hc]
  ring

theorem integrable_vectorMeasureControlGap_all (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Integrable (vectorMeasureControlGap μ β t A) (vectorDisorderBrownianMeasure n) := by
  by_cases hβ : β=0
  · have he : vectorMeasureControlGap μ β t A=fun _=>0 :=
      funext (vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [hβ]) A)
    rw [he]
    exact integrable_const 0
  by_cases he : t=1
  · have hh : vectorMeasureControlGap μ β t A=fun _=>0 :=
      funext (vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [he]) A)
    rw [hh]
    exact integrable_const 0
  exact integrable_vectorMeasureControlGap μ β t hβ (lt_of_le_of_ne ht he) A hA

theorem integrable_vectorParisiControlPayoff (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Integrable (fun sample=>vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
      vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample) (vectorDisorderBrownianMeasure n) := by
  have hu := (integrable_vectorMeasurePotential μ β t ht (0 : Field n)).comp_fst (vectorBrownianMeasure n)
  have hg := integrable_vectorMeasureControlGap_all μ β t ht A hA
  apply (hg.add hu).congr
  exact Eventually.of_forall (fun sample=>by
    simp only [Pi.add_apply,vectorMeasureControlGap]
    ring)

theorem vectorParisiControlObjective_eq_gap_add_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    vectorParisiControlObjective μ β t A=
      (∫sample,vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)+
      (∫p,vectorMeasurePotential μ β t p 0 ∂completionLaw n) := by
  have hu := (integrable_vectorMeasurePotential μ β t ht (0 : Field n)).comp_fst (vectorBrownianMeasure n)
  have hg := integrable_vectorMeasureControlGap_all μ β t ht A hA
  have he : (fun sample=>vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
        vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample)=
      (fun sample=>vectorMeasureControlGap μ β t A sample+vectorMeasurePotential μ β t sample.1 0) := by
    funext sample
    unfold vectorMeasureControlGap
    ring
  unfold vectorParisiControlObjective
  rw [he,integral_add hg hu]
  congr 1
  have hh := integral_fun_fst (μ := completionLaw n) (ν := vectorBrownianMeasure n)
    (fun p=>vectorMeasurePotential μ β t p (0 : Field n))
  simpa only [vectorDisorderBrownianMeasure,probReal_univ,one_smul] using hh

theorem vectorParisiControlObjective_le_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    vectorParisiControlObjective μ β t A≤∫p,vectorMeasurePotential μ β t p 0 ∂completionLaw n := by
  rw [vectorParisiControlObjective_eq_gap_add_value μ β t ht A hA]
  suffices (∫sample,vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)≤0 by linarith
  by_cases hβ : β=0
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [hβ]) A]
    simp
  by_cases he : t=1
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [he]) A]
    simp
  exact integral_vectorMeasureControlGap_le_zero μ β t hβ (lt_of_le_of_ne ht he) A hA

theorem vectorParisiControlObjective_feedback_eq_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) :
    vectorParisiControlObjective μ β t (vectorMeasureFeedbackControl (n := n) μ β t ht)=
      ∫p,vectorMeasurePotential μ β t p 0 ∂completionLaw n := by
  rw [vectorParisiControlObjective_eq_gap_add_value μ β t ht _
    (isVectorParisiControl_vectorMeasureFeedbackControl μ β t ht)]
  suffices (∫sample,vectorMeasureControlGap μ β t (vectorMeasureFeedbackControl μ β t ht) sample
      ∂vectorDisorderBrownianMeasure n)=0 by rw [this,zero_add]
  by_cases hβ : β=0
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [hβ])]
    simp
  by_cases he : t=1
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [he])]
    simp
  exact integral_vectorMeasureControlGap_feedback_eq_zero μ β t hβ (lt_of_le_of_ne ht he)

theorem vectorMeasure_control_representation (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) :
    (∀A : ℝ≥0→VectorDisorderBrownianSample n→Field n,IsVectorParisiControl A→
      vectorParisiControlObjective μ β t A≤∫p,vectorMeasurePotential μ β t p 0 ∂completionLaw n) ∧
    vectorParisiControlObjective μ β t (vectorMeasureFeedbackControl (n := n) μ β t ht)=
      ∫p,vectorMeasurePotential μ β t p 0 ∂completionLaw n :=
  ⟨fun A hA=>vectorParisiControlObjective_le_value μ β t ht A hA,
    vectorParisiControlObjective_feedback_eq_value μ β t ht⟩

end QuantitativePaper
