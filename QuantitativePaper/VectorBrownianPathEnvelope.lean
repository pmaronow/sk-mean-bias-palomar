module
public import QuantitativePaper.VectorBrownian
public import FourPapersCommon.WienerExponential
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! A genuine integrable path envelope for every actual Wiener coordinate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Paper FourPapersCommon Set
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorBrownianPathEnvelope (sample : VectorBrownianSample n) : ℝ :=
  ∑i : Fin n,‖canonicalBrownianPath (sample i)‖

theorem vectorBrownianPathEnvelope_nonneg (sample : VectorBrownianSample n) :
    0≤vectorBrownianPathEnvelope sample:=Finset.sum_nonneg fun _ _=>norm_nonneg _

theorem measurable_vectorBrownianPathEnvelope (n : ℕ) :
    Measurable (vectorBrownianPathEnvelope (n:=n)):=
  Finset.measurable_sum Finset.univ fun i _=>
    ((measurable_canonicalBrownianPath.comp (measurable_pi_apply i)).norm)

theorem norm_vectorBrownian_le_pathEnvelope (r : ℝ≥0) (hr : r≤1)
    (sample : VectorBrownianSample n) :
    ‖vectorBrownian r sample‖≤vectorBrownianPathEnvelope sample := by
  have he : vectorBrownian r sample=
      ∑i : Fin n,canonicalBrownian r (sample i) • EuclideanSpace.single i (1 : ℝ):=by
    ext j
    simp [Pi.single_apply]
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>?_)
  simp only [norm_smul,PiLp.norm_single,norm_one,mul_one]
  have hh:=(canonicalBrownianPath (sample i)).norm_coe_le_norm
    (⟨(r : ℝ),⟨r.coe_nonneg,show (r : ℝ)≤1 from hr⟩⟩ : Icc (0 : ℝ) 1)
  simpa only [canonicalBrownianPath,Real.toNNReal_coe,ContinuousMap.coe_mk] using hh

theorem integrable_exp_vectorBrownianPathEnvelope (K : ℝ) :
    Integrable (fun sample : VectorBrownianSample n=>Real.exp (K*vectorBrownianPathEnvelope sample))
      (vectorBrownianMeasure n) := by
  have hi : Integrable (fun sample : VectorBrownianSample n=>
      ∏i : Fin n,Real.exp (K*‖canonicalBrownianPath (sample i)‖))
      (vectorBrownianMeasure n):=
    Integrable.fintype_prod (fun _ : Fin n=>integrable_exp_norm_canonicalBrownianPath K)
  simpa only [vectorBrownianPathEnvelope,Finset.mul_sum,Real.exp_sum] using hi

end QuantitativePaper
