module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeWienerRepresentation
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanSquare

@[expose] public section

/-! Genuine moving-node convergence of the finite Wiener score response.
The strict-future residual vanishes at the restart level, so no atom or CDF
continuity restriction occurs. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128

theorem tendsto_cavityRestartFieldHessian_dyadic_node (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    Tendsto (fun j=>cavityRestartFieldHessian D
      (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)))
      g q x w (Paper.parisiGridRound (vectorDyadicIndex j) r) sample i) atTop
      (𝓝 (cavityRestartFieldHessian D μ g q x w r sample i)) := by
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let v:=fun j=>vectorDyadicTimeIndex r j
  let R:=fun j=>anisotropicRestartElapsed (sj j) q (v j)
  let Pj:=fun j=>anisotropicFiniteRestartPhysicalParameter D (sj j) g q
    (anisotropicInverseNoiseMap D x) (R j) sample
  let rj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) r
  have hv j : v j≤vectorDyadicIndex j+3:=(vectorDyadicTimeIndex_le r j).trans (by omega)
  have hn j : anisotropicSchemeNode (sj j) (v j) (hv j)=rj j :=
    Subtype.ext (vectorDyadicTimeIndex_node μ r j)
  have hqj j : q≤rj j:=hqr.trans (Paper.le_parisiGridRound _ r)
  have hR j : R j≤vectorRestartHorizon q := by
    unfold R anisotropicRestartElapsed vectorRestartHorizon
    apply Real.toNNReal_le_toNNReal
    exact sub_le_sub_right (max_le q.property.2 ((sj j).q_le_one (hv j))) _
  have hrj : Tendsto rj atTop (𝓝 r):=(Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex
  have hRt : Tendsto R atTop (𝓝 ((r:ℝ)-(q:ℝ)).toNNReal) := by
    have hh:=(continuous_subtype_val.tendsto r).comp hrj
    have htime:=continuous_real_toNNReal.tendsto _ |>.comp
      (((tendsto_const_nhds (x:=(q:ℝ))).max hh).sub_const (q:ℝ))
    have hnode j : (sj j).q (v j)=(rj j:ℝ) := vectorDyadicTimeIndex_node μ r j
    simpa only [R,anisotropicRestartElapsed,hnode,max_eq_right (show (q:ℝ)≤(r:ℝ) from hqr),
      Function.comp_def] using htime
  have hPi : Tendsto Pj atTop
      (𝓝 (anisotropicRestartPhysicalParameter D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample)) := by
    have h:=tendsto_anisotropicVarianceFiniteRestartPhysicalParameter_moving D μ i
      (D.variance_pos i) (tendsto_const_nhds (x:=D.variance i)) g q x sample hR hRt
    simpa only [anisotropicReplaceVariance_self,Pj,anisotropicFiniteRestartPhysicalParameter,anisotropicWhitenedParameterMap] using h
  have hT:=(tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_comp
    (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).continuousAt (hrj.prodMk_nhds hPi)
  have hev : Continuous (fun T : AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ)=>
      T (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  have hH:=hev.continuousAt.tendsto.comp hT
  have he j : cavityRestartFieldHessian D (Paper.parisiSchemeMeasure (sj j)) g q x w (rj j) sample i=
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D (sj j) (rj j))) (Pj j)
        (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i) := by
    have h:=cavityRestartFieldHessian_scheme_node D (sj j) g q x w (v j) (hv j) sample i
    simpa only [hn,max_eq_right (hqj j)] using h
  change Tendsto (fun j=>cavityRestartFieldHessian D (Paper.parisiSchemeMeasure (sj j))
    g q x w (rj j) sample i) atTop _
  simp_rw [he]
  simpa only [Function.comp_def,anisotropicDyadicTailPotential,anisotropicFiniteTailPotential,
    cavityRestartFieldHessian,Pj] using hH

theorem tendsto_cavityRestartSquareFieldResponse_dyadic_node (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    Tendsto (fun j=>cavityRestartSquareFieldResponse D
      (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)))
      g q x w (Paper.parisiGridRound (vectorDyadicIndex j) r) sample i) atTop
      (𝓝 (cavityRestartSquareFieldResponse D μ g q x w r sample i)) := by
  let μj:=fun j=>Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
  let rj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) r
  have hμ : Tendsto μj atTop (𝓝 μ) := by
    simp only [μj,FRSB.parisiSchemeMeasure_grid_eq]
    exact (FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex
  have hU:=tendstoUniformlyOn_cavityRestartSpinVector_profile D hμ g q x sample
  have hr : Tendsto rj atTop (𝓝 r):=(Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex
  have hM : Tendsto (fun j=>cavityRestartSpinVector D (μj j) g q x sample (rj j)) atTop
      (𝓝 (cavityRestartSpinVector D μ g q x sample r)) := by
    apply hU.tendsto_comp
      (continuous_cavityRestartSpinVector D μ g q x sample).continuousAt.continuousWithinAt
    exact tendsto_nhdsWithin_iff.mpr ⟨hr,.of_forall fun j=>hqr.trans (Paper.le_parisiGridRound _ r)⟩
  have h1:=hU.tendsto_at (show q≤(1:Paper.Overlap) from q.property.2)
  have hq:=hU.tendsto_at (show q≤q from le_rfl)
  have hS:=tendsto_cavityRestartStrictFutureResidual_dyadic D μ g q x w sample
  have hH:=tendsto_cavityRestartFieldHessian_dyadic_node D μ g q r hqr x w sample i
  have hi:=(EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp hM
  have hevin : Continuous (fun y : Field n=>inner ℝ w y) := continuous_const.inner continuous_id
  have hinner:=hevin.continuousAt.tendsto.comp (h1.sub hq)
  have h:=((hi.const_mul 2).mul hH).add ((hi.pow 2).mul (hinner.sub hS))
  simpa only [cavityRestartSquareFieldResponse,EuclideanSpace.proj,PiLp.proj_apply,
    Function.comp_def,μj,rj] using h

end QuantitativeFollowup
