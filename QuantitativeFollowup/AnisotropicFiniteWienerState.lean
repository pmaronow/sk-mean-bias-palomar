module
public import QuantitativeFollowup.AnisotropicFiniteWienerRealization
public import QuantitativeFollowup.AnisotropicWhitenedStateConvergence
public import QuantitativeFollowup.AnisotropicTailContinuity

@[expose] public section

/-! The genuine finite anisotropic process on its native disorder/Wiener
sample space and its same-driver limit at fixed or moving physical times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128

def anisotropicFiniteWienerState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (r : ℝ≥0) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicNoiseMap D (anisotropicWhitenedFiniteState D s sample.1 r ((0,0),sample.2))

theorem continuous_anisotropicFiniteWienerState (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun r => anisotropicFiniteWienerState D s r sample) :=
  (anisotropicNoiseMap D).continuous.comp (continuous_vectorAdditiveState _ _ _ _ _)

theorem measurable_uncurry_anisotropicFiniteWienerState (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Measurable (fun z : ℝ≥0×AnisotropicDisorderBrownianSample n =>
      anisotropicFiniteWienerState D s z.1 z.2) := by
  have hm := (measurable_uncurry_anisotropicWhitenedFiniteState_parameter D s).comp
    (show Measurable (fun z : ℝ≥0×AnisotropicDisorderBrownianSample n =>
      (z.1,(z.2.1,((0,0),z.2.2)))) from by fun_prop)
  exact (anisotropicNoiseMap D).continuous.measurable.comp hm

theorem anisotropicFiniteWienerHistory_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (sample : AnisotropicDisorderBrownianSample n)
    (i : ℕ) (hi : i ≤ k+2) :
    historyExtended (anisotropicFiniteWienerHistory D s (k+2) sample) i=
      anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
        (anisotropicFiniteWienerState D s (s.q i).toNNReal sample) := by
  change anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
    (anisotropicNoiseMap D (anisotropicWhitenedFiniteState D s sample.1
      (s.q (Fin.ofNat (k+3) i).val).toNNReal ((0,0),sample.2)))=_
  have he : (Fin.ofNat (k+3) i).val=i := Nat.mod_eq_of_lt (by omega)
  rw [he]
  rfl

theorem tendsto_anisotropicFiniteWienerState_moving_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    {rj : ℕ→ℝ≥0} {r : ℝ≥0} (hrj : ∀j,rj j ≤ 1) (hr : r ≤ 1)
    (hlim : Tendsto rj atTop (𝓝 r)) :
    Tendsto (fun j => anisotropicFiniteWienerState D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (rj j) sample) atTop
      (𝓝 (anisotropicMeasureState D μ r sample)) := by
  have hu := tendstoUniformlyOn_anisotropicWhitenedFiniteState D μ
  have hdist : Tendsto (fun j => dist
      (anisotropicWhitenedFiniteState D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        sample.1 (rj j) ((0,0),sample.2))
      (vectorAdditiveState (anisotropicWhitenedDriftData D μ sample.1) 1 0 1
        (rj j) ((0,0),sample.2))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with j hj
    simp only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
    simpa only [dist_comm] using
      (hj (rj j,(sample.1,((0,0),sample.2))) ⟨⟨bot_le,hrj j⟩,mem_univ _⟩)
  have hstate := (continuous_vectorAdditiveState (anisotropicWhitenedDriftData D μ sample.1)
    1 0 1 ((0,0),sample.2)).tendsto r |>.comp hlim
  have ht : Tendsto (fun j => anisotropicWhitenedFiniteState D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) sample.1 (rj j) ((0,0),sample.2))
      atTop (𝓝 (vectorAdditiveState (anisotropicWhitenedDriftData D μ sample.1)
        1 0 1 r ((0,0),sample.2))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _=>dist_nonneg) (fun j=>dist_triangle _
      (vectorAdditiveState (anisotropicWhitenedDriftData D μ sample.1) 1 0 1
        (rj j) ((0,0),sample.2)) _)
    simpa only [zero_add,Function.comp_def] using
      hdist.add (tendsto_iff_dist_tendsto_zero.mp hstate)
  rw [anisotropicMeasureState_eq_whitenedPicard D μ sample.1 ((0,0),sample.2) r hr]
  exact (anisotropicNoiseMap D).continuous.continuousAt.tendsto.comp ht

end QuantitativeFollowup
