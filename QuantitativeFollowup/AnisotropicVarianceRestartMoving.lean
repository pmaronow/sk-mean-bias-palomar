module
public import QuantitativeFollowup.AnisotropicVarianceRestartConvergence

@[expose] public section

/-! Moving elapsed observations of the genuine variance-varying restarted
state converge, and so do its physical parameter and terminal-spin response. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1400000
variable {n : ℕ}

theorem tendsto_anisotropicVarianceFiniteRestartState_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n)
    {R : ℕ→ℝ≥0} {r : ℝ≥0} (hR : ∀j,R j≤vectorRestartHorizon q)
    (hRt : Tendsto R atTop (𝓝 r)) :
    Tendsto (fun j=>anisotropicFiniteRestartState
      (anisotropicReplaceVariance D i (bj j)) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      g q (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i (bj j)) x) (R j) sample) atTop
      (𝓝 (anisotropicRestartState (anisotropicReplaceVariance D i b) μ g q
        (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i b) x) r sample)) := by
  have hu:=tendstoUniformlyOn_anisotropicVarianceFiniteRestartState D μ i hb ht g q x sample
  have hX:=(continuous_anisotropicRestartState (anisotropicReplaceVariance D i b) μ g q
    (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i b) x) sample).tendsto r |>.comp hRt
  have hd : Tendsto (fun j=>dist
      (anisotropicFiniteRestartState (anisotropicReplaceVariance D i (bj j))
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q
        (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i (bj j)) x) (R j) sample)
      (anisotropicRestartState (anisotropicReplaceVariance D i b) μ g q
        (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i b) x) (R j) sample)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with j hj
    have hh:=hj (R j) ⟨(R j).coe_nonneg,hR j⟩
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
    simpa only [dist_comm] using hh
  exact tendsto_of_tendsto_of_dist hX (by simpa only [dist_comm,Function.comp_def] using hd)

def anisotropicRestartPhysicalParameter (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n g+anisotropicUnitInput D
    (anisotropicRestartState D μ g q (anisotropicInverseNoiseMap D x) r sample)

theorem tendsto_anisotropicVarianceFiniteRestartPhysicalParameter_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n)
    {R : ℕ→ℝ≥0} {r : ℝ≥0} (hR : ∀j,R j≤vectorRestartHorizon q)
    (hRt : Tendsto R atTop (𝓝 r)) :
    Tendsto (fun j=>anisotropicDisorderInjection n g+anisotropicUnitInput (anisotropicReplaceVariance D i (bj j))
      (anisotropicFiniteRestartState (anisotropicReplaceVariance D i (bj j))
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q
        (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i (bj j)) x) (R j) sample)) atTop
      (𝓝 (anisotropicRestartPhysicalParameter (anisotropicReplaceVariance D i b) μ g q x r sample)) := by
  have hU:=(continuousAt_anisotropicReplaceVariance_unitInput D i b hb).tendsto.comp ht
  have hX:=tendsto_anisotropicVarianceFiniteRestartState_moving D μ i hb ht g q x sample hR hRt
  have hUX:=((isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=Field n) (F:=AnisotropicParameter n)).continuous.tendsto _).comp (hU.prodMk_nhds hX)
  exact tendsto_const_nhds.add hUX

end QuantitativeFollowup
