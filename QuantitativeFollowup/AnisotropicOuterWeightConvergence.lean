module
public import QuantitativeFollowup.AnisotropicMeasureOuterLaw
public import QuantitativePaper.VectorMeasureEndpoints
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Actual anisotropic finite-profile disorder tilts converge to the genuine
 arbitrary-profile tilt. Uniform potential error gives an integrable
 Gaussian exponential majorant, followed by honest dominated convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 900000

def anisotropicDyadicOuterPartition (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (j : ℕ) : ℝ :=
  ∫g,Real.exp (a*anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n g))
    ∂anisotropicDisorderLaw n

theorem integrable_exp_anisotropicDyadicPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) :
    Integrable (fun g=>Real.exp (a*anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n g)))
      (anisotropicDisorderLaw n) := by
  simpa only [anisotropicDyadicPotential,anisotropicFiniteFieldPotential,anisotropicDisorderInjection_apply] using
    integrable_exp_anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) _ a

theorem anisotropicDyadicOuterPartition_pos (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (j : ℕ) : 0 < anisotropicDyadicOuterPartition D μ a j :=
  integral_exp_pos (integrable_exp_anisotropicDyadicPotential D μ a j)

def anisotropicOuterExponentialEnvelope (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (g : AnisotropicDisorder n) : ℝ :=
  Real.exp (|a| * (4*anisotropicProfileStabilityConstant D))*
    Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g))

theorem integrable_anisotropicOuterExponentialEnvelope (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (anisotropicOuterExponentialEnvelope D μ a) (anisotropicDisorderLaw n) :=
  (integrable_exp_anisotropicMeasurePotential D μ a).const_mul _

theorem anisotropicDyadicOuterExponential_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) (g : AnisotropicDisorder n) :
    ‖Real.exp (a*anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n g))‖ ≤
      anisotropicOuterExponentialEnvelope D μ a g := by
  have hb:=anisotropicDyadicPotential_limit_abs_sub_le D μ j (anisotropicDisorderInjection n g)
  have hp : (1/2 : ℝ)^j ≤ 1:=pow_le_one₀ (by norm_num) (by norm_num)
  have hb':=hb.trans (mul_le_of_le_one_right
    (mul_nonneg (by norm_num) (anisotropicProfileStabilityConstant_nonneg D)) hp)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,anisotropicOuterExponentialEnvelope,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh:=le_abs_self (a*(anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n g)-
    anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g)))
  rw [abs_mul] at hh
  have hmul:=mul_le_mul_of_nonneg_left hb' (abs_nonneg a)
  nlinarith

theorem tendsto_anisotropicDyadicOuterPartition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Tendsto (anisotropicDyadicOuterPartition D μ a) atTop (𝓝 (anisotropicMeasureOuterPartition D μ a)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (anisotropicOuterExponentialEnvelope D μ a)
    (.of_forall fun j=>(integrable_exp_anisotropicDyadicPotential D μ a j).aestronglyMeasurable)
    (.of_forall fun j=>.of_forall (anisotropicDyadicOuterExponential_bound D μ a j))
    (integrable_anisotropicOuterExponentialEnvelope D μ a)
  exact .of_forall fun g => Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_anisotropicDyadicPotential D μ (anisotropicDisorderInjection n g)).const_mul a)

def anisotropicDyadicOuterWeight (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (j : ℕ) (g : AnisotropicDisorder n) : ℝ :=
  Real.exp (a*anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n g))/
    anisotropicDyadicOuterPartition D μ a j

def anisotropicMeasureOuterWeight (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (g : AnisotropicDisorder n) : ℝ :=
  Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g))/
    anisotropicMeasureOuterPartition D μ a

theorem tendsto_anisotropicDyadicOuterWeight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (g : AnisotropicDisorder n) :
    Tendsto (fun j=>anisotropicDyadicOuterWeight D μ a j g) atTop
      (𝓝 (anisotropicMeasureOuterWeight D μ a g)) := by
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_anisotropicDyadicPotential D μ (anisotropicDisorderInjection n g)).const_mul a)
  exact he.div (tendsto_anisotropicDyadicOuterPartition D μ a)
    (anisotropicMeasureOuterPartition_pos D μ a).ne'

theorem anisotropicDyadicOuterWeight_eventual_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    ∀ᶠj in atTop,∀g,‖anisotropicDyadicOuterWeight D μ a j g‖ ≤
      2*anisotropicOuterExponentialEnvelope D μ a g/anisotropicMeasureOuterPartition D μ a := by
  have hZ:=anisotropicMeasureOuterPartition_pos D μ a
  have he:=(tendsto_anisotropicDyadicOuterPartition D μ a).eventually
    (lt_mem_nhds (by linarith : anisotropicMeasureOuterPartition D μ a/2<anisotropicMeasureOuterPartition D μ a))
  filter_upwards [he] with j hj
  intro g
  rw [anisotropicDyadicOuterWeight,norm_div,Real.norm_of_nonneg (anisotropicDyadicOuterPartition_pos D μ a j).le]
  apply (div_le_div_of_nonneg_right (anisotropicDyadicOuterExponential_bound D μ a j g)
    (anisotropicDyadicOuterPartition_pos D μ a j).le).trans
  have hb : 0 ≤ anisotropicOuterExponentialEnvelope D μ a g := by unfold anisotropicOuterExponentialEnvelope;positivity
  apply (div_le_div_of_nonneg_left hb (by positivity : 0<anisotropicMeasureOuterPartition D μ a/2) hj.le).trans
  apply le_of_eq
  field_simp
  <;> ring

end QuantitativeFollowup
