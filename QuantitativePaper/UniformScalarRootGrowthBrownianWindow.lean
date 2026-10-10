module
public import Paper.CanonicalBrownian
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! A positive, temperature-independent Brownian window probability. This
constant is an actual Gaussian interval probability rather than a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace QuantitativePaper
set_option maxHeartbeats 600000

def scalarBrownianWindowProbability : ℝ := (gaussianReal 0 1).real (Icc (1:ℝ) 2)

theorem scalarBrownianWindowProbability_pos : 0<scalarBrownianWindowProbability := by
  have hs : Function.support (gaussianPDFReal 0 1)=univ:=by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (gaussianPDFReal_pos 0 1 x (by norm_num)).ne'
  have hi : 0<(∫x in Icc (1:ℝ) 2,gaussianPDFReal 0 1 x):=by
    rw [integral_pos_iff_support_of_nonneg (fun x=>gaussianPDFReal_nonneg 0 1 x)
      (integrable_gaussianPDFReal 0 1).restrict,hs]
    norm_num [Measure.restrict_apply]
  unfold scalarBrownianWindowProbability Measure.real
  rw [gaussianReal_apply_eq_integral 0 (by norm_num),ENNReal.toReal_ofReal hi.le]
  exact hi

theorem hasLaw_standardized_canonicalBrownian (q : ℝ) (hq : 0<q) :
    HasLaw (fun ω=>canonicalBrownian q.toNNReal ω/Real.sqrt q) (gaussianReal 0 1)
      canonicalBrownianMeasure := by
  have hl:=isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval q.toNNReal
  have hh:=gaussianReal_div_const hl (Real.sqrt q)
  have hv : q.toNNReal / NNReal.mk ((Real.sqrt q)^2) (sq_nonneg (Real.sqrt q)) = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_div,NNReal.coe_mk,NNReal.coe_one,Real.coe_toNNReal q hq.le,
      Real.sq_sqrt hq.le,div_self hq.ne']
  simpa only [zero_div,hv] using hh

theorem scalarBrownianWindow_probability (q : ℝ) (hq : 0<q) :
    canonicalBrownianMeasure.real {ω|canonicalBrownian q.toNNReal ω/Real.sqrt q∈Icc (1:ℝ) 2}=
      scalarBrownianWindowProbability := by
  have hl:=hasLaw_standardized_canonicalBrownian q hq
  unfold Measure.real scalarBrownianWindowProbability
  rw [←hl.map_eq]
  exact congrArg ENNReal.toReal (Measure.map_apply_of_aemeasurable hl.aemeasurable measurableSet_Icc).symm

end QuantitativePaper
