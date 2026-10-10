module
public import QuantitativePaper.VectorBrownianConditionalContinuousTest

@[expose] public section

/-! Genuine L² continuity in the conditioning time for every observable
measurable in the actual unit-time raw Brownian history. Bounded continuous
observed-path tests are dense, and every conditional expectation is a contraction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n:ℕ}

def vectorObservedPathMeasure (n:ℕ):Measure (VectorObservedPathSpace n):=
  (completionLaw n).prod (vectorWienerMeasure n)

instance vectorObservedPathMeasure_probability (n:ℕ):
    IsProbabilityMeasure (vectorObservedPathMeasure n):=by
  unfold vectorObservedPathMeasure
  infer_instance

theorem measurePreserving_vectorObservedBrownianPath :
    MeasurePreserving (vectorObservedBrownianPath (n:=n))
      (vectorDisorderBrownianMeasure n) (vectorObservedPathMeasure n):=
  ⟨measurable_vectorObservedBrownianPath,hasLaw_vectorObservedBrownianPath.map_eq⟩

def vectorObservedLpPullback:
    Lp ℝ 2 (vectorObservedPathMeasure n)→ₗᵢ[ℝ] Lp ℝ 2 (vectorDisorderBrownianMeasure n):=
  Lp.compMeasurePreservingₗᵢ ℝ vectorObservedBrownianPath
    measurePreserving_vectorObservedBrownianPath

theorem vectorObservedLpPullback_continuousTest (f:VectorObservedPathSpace n →ᵇ ℝ):
    vectorObservedLpPullback (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f)=
      (memLp_vectorObservedContinuousTest f).toLp (fun sample=>f (vectorObservedBrownianPath sample)):=by
  apply Lp.ext
  have hp:=Lp.coeFn_compMeasurePreserving
    (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f)
    measurePreserving_vectorObservedBrownianPath
  have hf:=measurePreserving_vectorObservedBrownianPath.quasiMeasurePreserving.ae
    (BoundedContinuousFunction.coeFn_toLp 2 (vectorObservedPathMeasure n) ℝ f)
  filter_upwards [hp,hf,(memLp_vectorObservedContinuousTest f).coeFn_toLp] with sample h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

theorem dist_conditionalBaseL2_le {Ω:Type*} (V:MeasurableSpace Ω) [mΩ:MeasurableSpace Ω]
    {P:Measure Ω} [IsProbabilityMeasure P] (hV:V ≤ mΩ) (x y:Lp ℝ 2 P):
    dist (conditionalBaseL2 (mΩ:=mΩ) V hV x) (conditionalBaseL2 (mΩ:=mΩ) V hV y)≤dist x y:=by
  rw [dist_eq_norm,dist_eq_norm,←map_sub]
  exact norm_condExpL2_coe_le (E:=ℝ) (𝕜:=ℝ) hV (x-y)

theorem continuous_conditionalBaseL2_observedLp (g:Lp ℝ 2 (vectorObservedPathMeasure n)):
    Continuous (fun q:Paper.Overlap=>conditionalBaseL2
      (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (vectorObservedLpPullback g)):=by
  have hd:DenseRange (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ:
      (VectorObservedPathSpace n →ᵇ ℝ)→L[ℝ] Lp ℝ 2 (vectorObservedPathMeasure n)):=
    BoundedContinuousFunction.toLp_denseRange ℝ (vectorObservedPathMeasure n) ℝ (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro q
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨f,hf⟩:=Metric.denseRange_iff.mp hd g (ε/3) (by positivity)
  have hc:=continuous_conditionalBaseL2_vectorObservedContinuousTest f
  simp_rw [←vectorObservedLpPullback_continuousTest] at hc
  obtain ⟨δ,hδ,hδf⟩:=Metric.continuousAt_iff.mp (hc.continuousAt (x:=q)) (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro r hr
  have h1:=dist_conditionalBaseL2_le (vectorBrownianFiltration n (r:ℝ).toNNReal)
    ((vectorBrownianFiltration n).le _) (vectorObservedLpPullback g)
    (vectorObservedLpPullback (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f))
  have h2:=dist_conditionalBaseL2_le (vectorBrownianFiltration n (q:ℝ).toNNReal)
    ((vectorBrownianFiltration n).le _)
    (vectorObservedLpPullback (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f))
    (vectorObservedLpPullback g)
  rw [vectorObservedLpPullback.dist_map] at h1 h2
  have hf' : dist ((BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ) f) g < ε/3 := by
    simpa only [dist_comm] using hf
  have hm:=hδf hr
  have ht:=dist_triangle4
    (conditionalBaseL2 (vectorBrownianFiltration n (r:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (vectorObservedLpPullback g))
    (conditionalBaseL2 (vectorBrownianFiltration n (r:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (vectorObservedLpPullback (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f)))
    (conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (vectorObservedLpPullback (BoundedContinuousFunction.toLp 2 (vectorObservedPathMeasure n) ℝ f)))
    (conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (vectorObservedLpPullback g))
  linarith

theorem continuous_conditionalBaseL2_of_unitPast (F:VectorDisorderBrownianSample n→ℝ)
    (hF:Measurable[vectorBrownianFiltration n 1] F)
    (hF2:MemLp F 2 (vectorDisorderBrownianMeasure n)):
    Continuous (fun q:Paper.Overlap=>conditionalBaseL2
      (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      (hF2.toLp F)):=by
  rw [vectorBrownianFiltration_one_eq_observedPath] at hF
  obtain ⟨g,hg,hFg⟩:=hF.exists_eq_measurable_comp
  have hgm:MemLp g 2 (vectorObservedPathMeasure n):=by
    rw [←measurePreserving_vectorObservedBrownianPath.map_eq]
    exact (memLp_map_measure_iff hg.aestronglyMeasurable
      measurable_vectorObservedBrownianPath.aemeasurable).mpr (hFg ▸ hF2)
  have he:vectorObservedLpPullback (hgm.toLp g)=hF2.toLp F:=by
    apply Lp.ext
    have h1:=Lp.coeFn_compMeasurePreserving (hgm.toLp g) measurePreserving_vectorObservedBrownianPath
    have h2:=measurePreserving_vectorObservedBrownianPath.quasiMeasurePreserving.ae hgm.coeFn_toLp
    filter_upwards [h1,h2,hF2.coeFn_toLp] with sample h1 h2 h3
    exact h1.trans (h2.trans ((congrFun hFg sample).symm.trans h3.symm))
  rw [←he]
  exact continuous_conditionalBaseL2_observedLp (hgm.toLp g)

end QuantitativePaper
