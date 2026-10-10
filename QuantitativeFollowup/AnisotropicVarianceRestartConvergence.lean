module
public import QuantitativeFollowup.AnisotropicVarianceMapContinuity
public import QuantitativeFollowup.AnisotropicVarianceRestartState
public import QuantitativePaper.VectorInitialPathDriftStability
public import FRSB.ParisiGridTopology
public import QuantitativePaper.VectorMeasureEndpoints
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section

/-! Genuine same-Wiener convergence of restarted anisotropic states when a
positive diagonal variance and the finite profile vary simultaneously. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendsto_anisotropicVarianceDyadicTailMagnetization_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b))
    {zj : ℕ→Paper.Overlap×AnisotropicParameter n} {z : Paper.Overlap×AnisotropicParameter n}
    (hz : Tendsto zj atTop (𝓝 z)) :
    Tendsto (fun j=>anisotropicFiniteTailMagnetization (anisotropicReplaceVariance D i (bj j))
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (zj j).1 (zj j).2) atTop
      (𝓝 (anisotropicMeasureTailMagnetization (anisotropicReplaceVariance D i b) μ z.1 z.2)) := by
  have hd:=tendsto_anisotropicVarianceDyadicTailDifferential_moving D μ i hb ht hz
  have hh:=(anisotropicResponseMap n).continuous.tendsto _ |>.comp hd
  simpa only [anisotropicFiniteTailMagnetization,anisotropicFiniteTailPotential,
    anisotropicDyadicTailPotential,Paper.parisiGridRSBScheme,Nat.add_assoc,
    anisotropicMeasureTailMagnetization,Function.comp_def,Nat.reduceAdd] using hh

theorem tendsto_anisotropicVarianceFiniteDrift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (r : ℝ≥0) (hr : (μ:Measure Paper.Overlap) {q | (q:ℝ)=(r:ℝ)}=0)
    (p : Couplings n×ℝ) (y : Field n) :
    Tendsto (fun j=>anisotropicWhitenedFiniteDrift (anisotropicReplaceVariance D i (bj j))
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g r p y) atTop
      (𝓝 (anisotropicWhitenedDrift (anisotropicReplaceVariance D i b) μ g r p y)) := by
  have hN:=(continuousAt_anisotropicReplaceVariance_noiseMap D i b hb).tendsto.comp ht
  have hU:=(continuousAt_anisotropicReplaceVariance_unitInput D i b hb).tendsto.comp ht
  let q : Paper.Overlap:=projIcc (0:ℝ) 1 zero_le_one r
  have hP : Tendsto (fun j=>anisotropicDisorderInjection n g+
      anisotropicUnitInput (anisotropicReplaceVariance D i (bj j)) y) atTop
      (𝓝 (anisotropicDisorderInjection n g+anisotropicUnitInput (anisotropicReplaceVariance D i b) y)) :=
    tendsto_const_nhds.add ((((ContinuousLinearMap.apply ℝ (AnisotropicParameter n)) y).continuous.tendsto _).comp hU)
  have hz : Tendsto (fun j=>(q,anisotropicDisorderInjection n g+
      anisotropicUnitInput (anisotropicReplaceVariance D i (bj j)) y)) atTop
      (𝓝 (q,anisotropicDisorderInjection n g+anisotropicUnitInput (anisotropicReplaceVariance D i b) y)) :=
    tendsto_const_nhds.prodMk_nhds hP
  have hM:=tendsto_anisotropicVarianceDyadicTailMagnetization_moving D μ i hb ht hz
  have hCDF:=FRSB.tendsto_parisiCDF_of_level_null
    ((FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex) hr
  have hNM:=((isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=Field n) (F:=Field n)).continuous.tendsto _).comp
    (hN.prodMk_nhds hM)
  have hh:=hCDF.smul hNM
  simpa only [anisotropicWhitenedFiniteDrift,anisotropicWhitenedDrift,
    anisotropicUnitInput,ContinuousLinearMap.comp_apply,q,FRSB.parisiSchemeMeasure_grid_eq,Function.comp_def] using hh

theorem tendstoUniformlyOn_anisotropicVarianceFiniteRestartState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    TendstoUniformlyOn (fun j=>fun r=>anisotropicFiniteRestartState
      (anisotropicReplaceVariance D i (bj j)) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      g q (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i (bj j)) x) r sample)
      (fun r=>anisotropicRestartState (anisotropicReplaceVariance D i b) μ g q
        (anisotropicInverseNoiseMap (anisotropicReplaceVariance D i b) x) r sample)
      atTop (Icc (0:ℝ≥0) (vectorRestartHorizon q)) := by
  let E:=anisotropicReplaceVariance D i b
  let Dj:=fun j=>anisotropicReplaceVariance D i (bj j)
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let d:=fun j=>anisotropicFiniteRestartDriftData (Dj j) (sj j) g q
  let e:=anisotropicRestartDriftData E μ g q
  let T:=vectorRestartHorizon q
  let y0:=anisotropicInverseNoiseMap E x
  let x0:=fun j=>anisotropicInverseNoiseMap (Dj j) x
  let Y:=fun s : ℝ=>vectorAdditiveState e 1 y0 T s.toNNReal sample
  have hY : Continuous Y:=(continuous_vectorAdditiveState e 1 y0 T sample).comp continuous_real_toNNReal
  let a:=fun j=>fun s : ℝ=>‖(d j).drift s.toNNReal sample.1 (Y s)-e.drift s.toNNReal sample.1 (Y s)‖
  have hameas j : Measurable (a j):=
    ((d j).measurable.comp (continuous_real_toNNReal.measurable.prodMk
      (measurable_const.prodMk hY.measurable))).sub
      (e.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hY.measurable))) |>.norm
  have hab j s : a j s≤(d j).bound+e.bound:=
    (norm_sub_le _ _).trans (add_le_add ((d j).norm_le _ _ _) (e.norm_le _ _ _))
  have hai j : IntervalIntegrable (a j) volume 0 T:=
    (intervalIntegrable_const (c:=((d j).bound:ℝ)+(e.bound:ℝ))).mono_fun'
      (hameas j).aestronglyMeasurable (.of_forall fun s=>by
        change ‖a j s‖≤(d j).bound+e.bound
        rw [Real.norm_of_nonneg (show 0≤a j s from norm_nonneg _)]
        exact hab j s)
  have hN:=(continuousAt_anisotropicReplaceVariance_noiseMap D i b hb).tendsto.comp ht
  have hbound : Tendsto (fun j=>((d j).bound:ℝ)) atTop (𝓝 (e.bound:ℝ)) := by
    simpa only [d,e,Dj,E,anisotropicFiniteRestartDriftData,anisotropicRestartDriftData,
      vectorFixedRestartDriftData,anisotropicWhitenedFiniteDriftData,anisotropicWhitenedDriftData,
      anisotropicWhitenedFiniteDriftBound,anisotropicWhitenedDriftBound,NNReal.coe_mul,coe_nnnorm,Function.comp_def]
      using hN.norm.mul_const ((Real.sqrt (n:ℝ)).toNNReal:ℝ)
  have hnull : ∀ᵐ s ∂(volume:Measure ℝ),(μ:Measure Paper.Overlap) {v | (v:ℝ)=(q:ℝ)+s}=0 :=
    (measurePreserving_add_left (volume:Measure ℝ) (q:ℝ)).quasiMeasurePreserving.ae
      (FRSB.ae_parisi_level_null μ)
  have hlim : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) T),Tendsto (fun j=>a j s) atTop (𝓝 0) := by
    filter_upwards [hnull.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem measurableSet_Ioc]
      with s hs hsin
    have htime : (((q:ℝ).toNNReal+s.toNNReal:ℝ≥0):ℝ)=(q:ℝ)+s := by
      simp only [NNReal.coe_add,Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ hsin.1.le]
    have hd:=tendsto_anisotropicVarianceFiniteDrift D μ i hb ht g
      ((q:ℝ).toNNReal+s.toNNReal) (by simpa only [htime] using hs) 0 (Y s)
    have hh:=(hd.sub_const (anisotropicWhitenedDrift E μ g ((q:ℝ).toNNReal+s.toNNReal) 0 (Y s))).norm
    simpa only [a,d,e,Dj,sj,E,anisotropicFiniteRestartDriftData,anisotropicRestartDriftData,
      vectorFixedRestartDriftData,anisotropicWhitenedFiniteDriftData,anisotropicWhitenedDriftData,sub_self,norm_zero] using hh
  have hI : Tendsto (fun j=>∫s in (0:ℝ)..(T:ℝ),a j s) atTop (𝓝 0) := by
    have hh:=tendsto_integral_filter_of_dominated_convergence
      (μ:=volume.restrict (Ioc (0:ℝ) T)) (fun _=>(2*(e.bound:ℝ)+1))
      (.of_forall fun j=>(hameas j).aestronglyMeasurable)
      (by
        filter_upwards [hbound.eventually (gt_mem_nhds (show (e.bound:ℝ)<(e.bound:ℝ)+1 by linarith))] with j hj
        exact .of_forall fun s=>by
          rw [Real.norm_of_nonneg (show 0≤a j s from norm_nonneg _)]
          exact (hab j s).trans (by linarith)) (integrable_const _) hlim
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg,integral_zero] using hh
  have hx:=(continuousAt_anisotropicReplaceVariance_inverseNoiseMap D i b hb).tendsto.comp ht
  have hδ : Tendsto (fun j=>‖x0 j-y0‖+∫s in (0:ℝ)..(T:ℝ),a j s) atTop (𝓝 0) := by
    simpa only [x0,y0,E,Dj,ContinuousLinearMap.apply_apply,sub_self,norm_zero,zero_add,Function.comp_def] using (((((ContinuousLinearMap.apply ℝ (Field n)) x).continuous.tendsto _).comp hx).sub_const y0).norm.add hI
  have hL:=(continuousAt_anisotropicReplaceVariance_whitenedDriftLip D i b hb).tendsto.comp ht
  have hexp : Tendsto (fun j=>Real.exp (((d j).spatialLip:ℝ)*(T:ℝ))) atTop
      (𝓝 (Real.exp ((anisotropicWhitenedDriftLip E:ℝ)*(T:ℝ)))) := by
    simpa only [d,Dj,anisotropicFiniteRestartDriftData,vectorFixedRestartDriftData,
      anisotropicWhitenedFiniteDriftData,anisotropicWhitenedFiniteDriftLip,
      anisotropicWhitenedDriftLip,Function.comp_def,E] using
        (Real.continuous_exp.tendsto _).comp (hL.mul_const (T:ℝ))
  have htotal:=hδ.mul hexp
  simp only [zero_mul] at htotal
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [htotal.eventually (gt_mem_nhds hε)] with j hj
  intro r hr
  rw [dist_comm,dist_eq_norm]
  have hh:=norm_vectorAdditiveState_sub_le_of_initial_pathDrift (d j) e 1 (x0 j) y0 T sample
    (a j) (hai j) (fun s _=>norm_nonneg _)
    (fun s _=>by simp only [a,Y,Real.toNNReal_coe];exact le_rfl) r hr.2
  apply hh.trans_lt
  apply lt_of_le_of_lt _ hj
  apply mul_le_mul_of_nonneg_left _
    (add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg T.coe_nonneg (fun s _=>norm_nonneg _)))
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (show (r:ℝ)≤T from hr.2) (d j).spatialLip.coe_nonneg

end QuantitativeFollowup
