module
public import QuantitativePaper.VectorBrownianSplicing
public import QuantitativePaper.BrownianIndependentConditionalMean
public import QuantitativePaper.VectorTemperatureDensityCore
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

/-! The raw-Wiener conditional expectation of a bounded continuous observed
disorder/path test has a genuinely continuous L² version in the conditioning
time. This follows from actual future independence and continuous splicing. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n:ℕ}
abbrev VectorObservedPathSpace (n:ℕ):=(Couplings n×ℝ)×VectorWienerPath n

def vectorBrownianSplicedMean (f:VectorObservedPathSpace n→ᵇ ℝ) (q:Paper.Overlap)
    (sample:VectorDisorderBrownianSample n):ℝ:=
  ∫V,f (sample.1,vectorWienerSplice q (vectorCanonicalBrownianPath sample.2) V)∂vectorWienerMeasure n

theorem vectorBrownianSplicedMean_bound (f:VectorObservedPathSpace n→ᵇ ℝ)
    (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n):
    ‖vectorBrownianSplicedMean f q sample‖≤‖f‖:=by
  simpa [vectorBrownianSplicedMean] using norm_integral_le_of_norm_le_const (μ:=vectorWienerMeasure n)
    (.of_forall fun V=>f.norm_coe_le_norm (sample.1,vectorWienerSplice q (vectorCanonicalBrownianPath sample.2) V))

theorem measurable_vectorBrownianSplicedMean (f:VectorObservedPathSpace n→ᵇ ℝ) (q:Paper.Overlap):
    Measurable (vectorBrownianSplicedMean f q):=by
  have hs:Measurable (fun z:VectorDisorderBrownianSample n×VectorWienerPath n=>
      (z.1.1,vectorWienerSplice q (vectorCanonicalBrownianPath z.1.2) z.2)):=
    measurable_fst.fst.prodMk (continuous_vectorWienerSplice.measurable.comp
      (measurable_const.prodMk
        ((measurable_vectorCanonicalBrownianPath.comp measurable_fst.snd).prodMk measurable_snd)))
  exact (f.continuous.measurable.comp hs).stronglyMeasurable.integral_prod_right' |>.measurable

theorem memLp_vectorBrownianSplicedMean (f:VectorObservedPathSpace n→ᵇ ℝ) (q:Paper.Overlap):
    MemLp (vectorBrownianSplicedMean f q) 2 (vectorDisorderBrownianMeasure n):=
  MemLp.of_bound (measurable_vectorBrownianSplicedMean f q).aestronglyMeasurable ‖f‖
    (.of_forall (vectorBrownianSplicedMean_bound f q))

theorem memLp_vectorObservedContinuousTest (f:VectorObservedPathSpace n→ᵇ ℝ):
    MemLp (fun sample=>f (vectorObservedBrownianPath sample)) 2 (vectorDisorderBrownianMeasure n):=
  MemLp.of_bound (f.continuous.measurable.comp measurable_vectorObservedBrownianPath).aestronglyMeasurable
    ‖f‖ (.of_forall fun sample=>f.norm_coe_le_norm _)

theorem condExp_vectorObservedContinuousTest (f:VectorObservedPathSpace n→ᵇ ℝ) (q:Paper.Overlap):
    (vectorDisorderBrownianMeasure n)[(fun sample=>f (vectorObservedBrownianPath sample))|
      vectorBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[vectorDisorderBrownianMeasure n]
      vectorBrownianSplicedMean f q:=by
  let X:VectorDisorderBrownianSample n→VectorObservedPathSpace n:=
    fun sample=>(sample.1,vectorStoppedBrownianPath q sample)
  have hX:Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] X:=
    (stronglyMeasurable_initialVectorDisorder n _).measurable.prodMk
      (measurable_vectorStoppedBrownianPath_past q)
  let g:VectorObservedPathSpace n×VectorWienerPath n→ℝ:=
    fun z=>f (z.1.1,vectorWienerSplice q z.1.2 z.2)
  have hg:Measurable g:=f.continuous.measurable.comp
    (measurable_fst.fst.prodMk (continuous_vectorWienerSplice.measurable.comp
      (measurable_const.prodMk (measurable_fst.snd.prodMk measurable_snd))))
  have hh:=condExp_independent_noise (vectorBrownianFiltration n (q:ℝ).toNNReal)
    (vectorDisorderBrownianMeasure n) ((vectorBrownianFiltration n).le _) X hX
    (vectorFutureBrownianPath (q:ℝ).toNNReal) (measurable_vectorFutureBrownianPath _)
    (vectorWienerMeasure n) (hasLaw_vectorFutureBrownianPath _)
    (indep_vectorFutureBrownianPath_filtration _) g hg ‖f‖ (fun z=>f.norm_coe_le_norm _)
  have he:(fun sample=>g (X sample,vectorFutureBrownianPath (q:ℝ).toNNReal sample))=
      fun sample=>f (vectorObservedBrownianPath sample):=by
    funext sample
    dsimp only [g,X]
    rw [vectorWienerSplice_stopped,vectorWienerSplice_actual]
    rfl
  rw [he] at hh
  convert hh using 1
  funext sample
  apply integral_congr_ae
  exact .of_forall fun V=>by dsimp only [g,X,vectorBrownianSplicedMean];rw [vectorWienerSplice_stopped]

theorem continuous_vectorBrownianSplicedMean_time (f:VectorObservedPathSpace n→ᵇ ℝ)
    (sample:VectorDisorderBrownianSample n):Continuous (fun q:Paper.Overlap=>vectorBrownianSplicedMean f q sample):=by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply continuousAt_of_dominated (bound:=fun _=>‖f‖)
  · exact .of_forall fun r=>((f.continuous.comp
      (continuous_const.prodMk (continuous_vectorWienerSplice.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))))).measurable).aestronglyMeasurable
  · exact .of_forall fun r=>.of_forall fun V=>f.norm_coe_le_norm _
  · exact integrable_const _
  · exact .of_forall fun V=>(f.continuous.comp
      (continuous_const.prodMk (continuous_vectorWienerSplice.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))))).continuousAt

def vectorBrownianSplicedMeanLp (f:VectorObservedPathSpace n→ᵇ ℝ) (q:Paper.Overlap):
    Lp ℝ 2 (vectorDisorderBrownianMeasure n):=
  (memLp_vectorBrownianSplicedMean f q).toLp (vectorBrownianSplicedMean f q)

theorem continuous_vectorBrownianSplicedMeanLp (f:VectorObservedPathSpace n→ᵇ ℝ):
    Continuous (vectorBrownianSplicedMeanLp f):=by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun r=>vectorBrownianSplicedMean f r) (vectorBrownianSplicedMean f q)
    (memLp_vectorBrownianSplicedMean f) (memLp_vectorBrownianSplicedMean f q)
    (fun _=>‖f‖) (by simpa using integrable_const (‖f‖^2) (μ:=vectorDisorderBrownianMeasure n))
    (.of_forall fun r=>.of_forall (vectorBrownianSplicedMean_bound f r))
    (.of_forall (vectorBrownianSplicedMean_bound f q))
    (.of_forall fun sample=>(continuous_vectorBrownianSplicedMean_time f sample).tendsto q)

theorem conditionalBaseL2_vectorObservedContinuousTest (f:VectorObservedPathSpace n→ᵇ ℝ)
    (q:Paper.Overlap):
    conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
      ((memLp_vectorObservedContinuousTest f).toLp (fun sample=>f (vectorObservedBrownianPath sample)))=
      vectorBrownianSplicedMeanLp f q:=by
  apply Lp.ext
  exact (conditionalBaseL2_ae _ _ _ (memLp_vectorObservedContinuousTest f)).trans
    ((condExp_vectorObservedContinuousTest f q).trans (memLp_vectorBrownianSplicedMean f q).coeFn_toLp.symm)

theorem continuous_conditionalBaseL2_vectorObservedContinuousTest (f:VectorObservedPathSpace n→ᵇ ℝ):
    Continuous (fun q:Paper.Overlap=>
      conditionalBaseL2 (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
        ((memLp_vectorObservedContinuousTest f).toLp (fun sample=>f (vectorObservedBrownianPath sample)))):=by
  simp_rw [conditionalBaseL2_vectorObservedContinuousTest]
  exact continuous_vectorBrownianSplicedMeanLp f

end QuantitativePaper
