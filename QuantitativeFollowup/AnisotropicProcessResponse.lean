module
public import QuantitativeFollowup.AnisotropicFiniteWienerState
public import QuantitativeFollowup.AnisotropicFiniteHistoryObservables
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-! Genuine magnetization and selected self-overlap along the constructed
anisotropic processes, with moving-overlap dyadic convergence. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicProcessParameter (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
    (anisotropicMeasureState D μ q sample)

def anisotropicFiniteProcessParameter (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
    (anisotropicFiniteWienerState D s (q:ℝ).toNNReal sample)

def anisotropicProcessMagnetization (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicMeasureTailMagnetization D μ q (anisotropicProcessParameter D μ q sample)

def anisotropicFiniteProcessMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicFiniteTailMagnetization D s q (anisotropicFiniteProcessParameter D s q sample)

theorem measurable_uncurry_anisotropicProcessParameter (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicProcessParameter D μ z.1 z.2) := by
  unfold anisotropicProcessParameter
  have hX := (measurable_uncurry_anisotropicMeasureState D μ).comp
    (show Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      ((z.1:ℝ),z.2)) from (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hXs : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicMeasureState D μ z.1 z.2) := by
    simpa only [Function.comp_def,Function.uncurry_def] using hX
  exact ((anisotropicDisorderInjection n).continuous.measurable.comp measurable_snd.fst).add
    ((anisotropicFieldInjection n).continuous.measurable.comp hXs)

theorem measurable_uncurry_anisotropicFiniteProcessParameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicFiniteProcessParameter D s z.1 z.2) := by
  unfold anisotropicFiniteProcessParameter
  have hX := (measurable_uncurry_anisotropicFiniteWienerState D s).comp
    (show Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      ((z.1:ℝ).toNNReal,z.2)) from
        (((continuous_real_toNNReal.measurable.comp measurable_subtype_coe).comp
          measurable_fst).prodMk measurable_snd))
  have hXs : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicFiniteWienerState D s (z.1:ℝ).toNNReal z.2) := by
    simpa only [Function.comp_def] using hX
  exact ((anisotropicDisorderInjection n).continuous.measurable.comp measurable_snd.fst).add
    ((anisotropicFieldInjection n).continuous.measurable.comp hXs)

theorem measurable_uncurry_anisotropicProcessMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicProcessMagnetization D μ z.1 z.2) := by
  have h := (continuous_anisotropicMeasureTailMagnetization_joint D μ).measurable.comp
    (measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ))
  simpa only [Function.comp_def,anisotropicProcessMagnetization] using h

theorem measurable_uncurry_anisotropicFiniteProcessMagnetization (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicFiniteProcessMagnetization D s z.1 z.2) := by
  have h := (measurable_anisotropicFiniteTailMagnetization D s).comp
    (measurable_fst.prodMk (measurable_uncurry_anisotropicFiniteProcessParameter D s))
  simpa only [Function.comp_def,anisotropicFiniteProcessMagnetization] using h

theorem continuous_anisotropicProcessMagnetization_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun q : Paper.Overlap => anisotropicProcessMagnetization D μ q sample) := by
  have hX := (continuous_anisotropicMeasureState D μ sample).comp
    (continuous_subtype_val : Continuous (fun q : Paper.Overlap => (q:ℝ)))
  have hP := (continuous_const (y:=anisotropicDisorderInjection n sample.1)).add
    ((anisotropicFieldInjection n).continuous.comp hX)
  have h := (continuous_anisotropicMeasureTailMagnetization_joint D μ).comp
    (continuous_id.prodMk hP)
  simpa only [Function.comp_def,anisotropicProcessMagnetization,
    anisotropicProcessParameter,Pi.add_apply,id_eq] using h

theorem anisotropicFiniteProcessMagnetization_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (sample : AnisotropicDisorderBrownianSample n)
    (i : ℕ) (hi : i ≤ k+2) :
    anisotropicFiniteProcessMagnetization D s (anisotropicSchemeNode s i hi) sample=
      anisotropicHistoryMagnetization D s i (anisotropicFiniteWienerHistory D s (k+2) sample) := by
  rw [anisotropicHistoryMagnetization,anisotropicFiniteWienerHistory_node D s sample i hi]
  unfold anisotropicFiniteProcessMagnetization
  rw [anisotropicFiniteTailMagnetization_node D s i hi]
  rfl

theorem tendsto_anisotropicFiniteProcessParameter_moving_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j => anisotropicFiniteProcessParameter D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) sample) atTop
      (𝓝 (anisotropicProcessParameter D μ q sample)) := by
  have hr : Tendsto (fun j => (qj j:ℝ).toNNReal) atTop (𝓝 (q:ℝ).toNNReal) :=
    ((continuous_real_toNNReal.comp continuous_subtype_val).tendsto q).comp hq
  have hs := tendsto_anisotropicFiniteWienerState_moving_time D μ sample
    (fun j => by simpa using Real.toNNReal_le_toNNReal (qj j).property.2)
    (by simpa using Real.toNNReal_le_toNNReal q.property.2) hr
  rw [Real.coe_toNNReal _ q.property.1] at hs
  exact tendsto_const_nhds.add ((anisotropicFieldInjection n).continuous.continuousAt.tendsto.comp hs)

theorem tendsto_anisotropicFiniteProcessMagnetization_moving_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j => anisotropicFiniteProcessMagnetization D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) sample) atTop
      (𝓝 (anisotropicProcessMagnetization D μ q sample)) := by
  have h := (tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_comp
    (continuous_anisotropicMeasureTailMagnetization_joint D μ).continuousAt
    (hq.prodMk_nhds (tendsto_anisotropicFiniteProcessParameter_moving_time D μ sample hq))
  simpa only [Function.comp_def,anisotropicProcessMagnetization,
    anisotropicFiniteProcessMagnetization] using h

def anisotropicSelectedMeanSquare (J : Finset (Fin n)) (m : Field n) : ℝ :=
  (∑i∈J,(m i)^2)/(J.card:ℝ)

theorem continuous_anisotropicSelectedMeanSquare (J : Finset (Fin n)) :
    Continuous (anisotropicSelectedMeanSquare J) := by
  unfold anisotropicSelectedMeanSquare
  apply Continuous.div_const
  apply continuous_finset_sum
  intro i _
  exact (EuclideanSpace.proj i).continuous.pow 2

theorem anisotropicSelectedMeanSquare_bound (J : Finset (Fin n)) (m : Field n)
    (hm : ∀i,|m i| ≤ 1) : ‖anisotropicSelectedMeanSquare J m‖ ≤ 1 := by
  by_cases hJ : J.Nonempty
  swap
  · have hJe : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [hJe,anisotropicSelectedMeanSquare]
  have hc : 0 < (J.card:ℝ) := by exact_mod_cast hJ.card_pos
  have hs : (∑i∈J,(m i)^2) ≤ (J.card:ℝ) := by
    calc
      _ ≤ ∑_i∈J,(1:ℝ) := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hm i) 2
      _ = _ := by simp
  rw [Real.norm_of_nonneg (by unfold anisotropicSelectedMeanSquare;positivity)]
  exact (div_le_one hc).mpr hs

end QuantitativeFollowup
