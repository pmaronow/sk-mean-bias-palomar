module
public import QuantitativePaper.VectorBrownianConditionalContinuity
public import QuantitativePaper.VectorConditionalMomentProfileContinuity

@[expose] public section

/-! Actual terminal-spin conditional expectations converge in L² as both
the profile and conditioning time vary. The true raw-Wiener filtration is
used throughout; no completion or right-continuity premise is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n:ℕ} {J:Type*} {l:Filter J}

theorem measurable_vectorMeasureTerminalObservable_unitPast (μ:Paper.ParisiMeasure)
    (β t:ℝ) (ht:t≤1) (d:Configuration n→ℝ):
    Measurable[vectorBrownianFiltration n 1] (vectorMeasureTerminalObservable μ β t ht d):=by
  have hh:=(continuous_vectorTerminalMean_joint β t d).measurable.comp
    (adapted_vectorMeasureJointState μ β t ht 1)
  exact hh

theorem continuous_conditionalBaseL2_vectorBasePairObservable (μ:Paper.ParisiMeasure)
    (β t:ℝ) (ht:t≤1) (i k:Fin n):
    Continuous (fun q:Paper.Overlap=>conditionalBaseL2
      (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      ((memLp_vectorBasePairObservable μ β t ht i k).toLp
        (vectorBasePairObservable μ β t ht i k))):=
  continuous_conditionalBaseL2_of_unitPast _
    (measurable_vectorMeasureTerminalObservable_unitPast μ β t ht _)
    (memLp_vectorBasePairObservable μ β t ht i k)

theorem tendsto_conditionalBaseL2_of_unitPast_and_input
    (F:VectorDisorderBrownianSample n→ℝ)
    (hF:Measurable[vectorBrownianFiltration n 1] F)
    (hF2:MemLp F 2 (vectorDisorderBrownianMeasure n))
    (fj:J→Lp ℝ 2 (vectorDisorderBrownianMeasure n))
    (hfj:Tendsto fj l (𝓝 (hF2.toLp F)))
    {qj:J→Paper.Overlap} {q:Paper.Overlap} (hq:Tendsto qj l (𝓝 q)):
    Tendsto (fun j=>conditionalBaseL2 (vectorBrownianFiltration n (qj j:ℝ).toNNReal)
      ((vectorBrownianFiltration n).le _) (fj j)) l
      (𝓝 (conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal)
        ((vectorBrownianFiltration n).le _) (hF2.toLp F))):=by
  have he:Tendsto (fun j=>dist
      (conditionalBaseL2 (vectorBrownianFiltration n (qj j:ℝ).toNNReal)
        ((vectorBrownianFiltration n).le _) (fj j))
      (conditionalBaseL2 (vectorBrownianFiltration n (qj j:ℝ).toNNReal)
        ((vectorBrownianFiltration n).le _) (hF2.toLp F))) l (𝓝 0):=by
    apply squeeze_zero (fun _=>dist_nonneg) (fun j=>dist_conditionalBaseL2_le
      (vectorBrownianFiltration n (qj j:ℝ).toNNReal) ((vectorBrownianFiltration n).le _) _ _)
    exact (tendsto_iff_dist_tendsto_zero.mp hfj)
  have hc:=((continuous_conditionalBaseL2_of_unitPast F hF hF2).tendsto q).comp hq
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _=>dist_nonneg)
    (fun j=>dist_triangle _
      (conditionalBaseL2 (vectorBrownianFiltration n (qj j:ℝ).toNNReal)
        ((vectorBrownianFiltration n).le _) (hF2.toLp F)) _)
  simpa using he.add (tendsto_iff_dist_tendsto_zero.mp hc)

theorem tendsto_conditionalBaseL2_vectorBasePairObservable_of_weak_and_time
    [l.IsCountablyGenerated] {ν:J→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure}
    (β t:ℝ) (ht:t≤1) (hν:Tendsto ν l (𝓝 μ))
    {qj:J→Paper.Overlap} {q:Paper.Overlap} (hq:Tendsto qj l (𝓝 q)) (i k:Fin n):
    Tendsto (fun j=>conditionalBaseL2 (vectorBrownianFiltration n (qj j:ℝ).toNNReal)
      ((vectorBrownianFiltration n).le _)
      ((memLp_vectorBasePairObservable (ν j) β t ht i k).toLp
        (vectorBasePairObservable (ν j) β t ht i k))) l
      (𝓝 (conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal)
        ((vectorBrownianFiltration n).le _)
        ((memLp_vectorBasePairObservable μ β t ht i k).toLp
          (vectorBasePairObservable μ β t ht i k)))):=
  tendsto_conditionalBaseL2_of_unitPast_and_input _
    (measurable_vectorMeasureTerminalObservable_unitPast μ β t ht _)
    (memLp_vectorBasePairObservable μ β t ht i k) _
    (tendsto_vectorBasePairObservable_toLp_of_weak β t ht hν i k) hq

end QuantitativePaper
