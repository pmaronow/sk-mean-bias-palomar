module
public import QuantitativePaper.VectorGaussianDiagonalShift
public import FourPapersCommon.NormalizedCGFScalingCompletion

@[expose] public section

/-! Actual off-diagonal Gaussian moments and exact removal of the common
diagonal Gaussian from the arbitrary-profile potential. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 300000

theorem integrable_exp_vectorMeasurePotential_offDiagonal {n : ℕ}
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (x : Field n) :
    Integrable (fun g : Couplings n=>Real.exp (a*vectorMeasurePotential μ β t (g,0) x)) (couplingLaw n) := by
  have hm : Measurable (fun g : Couplings n=>vectorMeasurePotential μ β t (g,0) x) := by
    have harg : Measurable (fun g : Couplings n=>(((g,(0:ℝ)),x):VectorParameter n)) := by fun_prop
    simpa only [Function.comp_def] using (continuous_vectorMeasurePotential_joint μ β t ht).measurable.comp harg
  apply ((integrable_exp_couplingEnvelope n (|a| * |β| * Real.sqrt t) (by positivity)).const_mul
    (Real.exp (|a| * |vectorMeasurePotential μ β t (0,0) x|))).mono'
    (Real.measurable_exp.comp (measurable_const.mul hm)).aestronglyMeasurable
  apply Eventually.of_forall
  intro g
  dsimp only [Function.comp_def,Pi.mul_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb:=vectorMeasurePotential_disorder_bound μ β t ht (g,0) x
  simp only [vectorDisorderEnvelope,abs_zero,add_zero] at hb
  have habs : |vectorMeasurePotential μ β t (g,0) x| ≤
      |vectorMeasurePotential μ β t (0,0) x|+|β| * Real.sqrt t*couplingEnvelope n g := by
    have hh:=abs_add_le (vectorMeasurePotential μ β t (0,0) x)
      (vectorMeasurePotential μ β t (g,0) x-vectorMeasurePotential μ β t (0,0) x)
    rw [add_sub_cancel] at hh
    linarith
  calc
    _ ≤ |a| * |vectorMeasurePotential μ β t (g,0) x| := by rw [←abs_mul];exact le_abs_self _
    _ ≤ |a| * (|vectorMeasurePotential μ β t (0,0) x|+|β| * Real.sqrt t*couplingEnvelope n g) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = _ := by ring

theorem normalizedCGF_vectorMeasurePotential_diagonal_completion {n : ℕ}
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (x : Field n) :
    normalizedCGF (completionLaw n) (fun p=>vectorMeasurePotential μ β t p x) a=
      normalizedCGF (couplingLaw n) (fun g=>vectorMeasurePotential μ β t (g,0) x) a+
        (β*Real.sqrt t)^2*a/4 := by
  have he : (fun p : Couplings n×ℝ=>vectorMeasurePotential μ β t p x)=
      fun p=>vectorMeasurePotential μ β t (p.1,0) x+(β*Real.sqrt t)*p.2 := by
    funext p
    rw [vectorMeasurePotential_diagonal_shift μ β t ht p x]
    ring
  rw [he]
  exact normalizedCGF_gaussian_completion (couplingLaw n) _
    (fun b=>integrable_exp_vectorMeasurePotential_offDiagonal μ β t ht b x) (β*Real.sqrt t) a

end QuantitativePaper
