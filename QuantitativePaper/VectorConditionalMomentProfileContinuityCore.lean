module
public import QuantitativePaper.VectorTemperatureDensityContinuity
public import QuantitativePaper.VectorMeasureStateConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-! Pointwise convergence of the actual terminal observables, adapted spin
means and initial potential under weak convergence of the profile. The state
and gradient are the constructed same-driver objects. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
variable {ν : J→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure}

theorem tendsto_vectorMeasureState_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (r:ℝ≥0) (hr:r≤1)
    (sample:VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorMeasureState (ν j) β t ht r sample) l
      (𝓝 (vectorMeasureState μ β t ht r sample)):=by
  have hh:=tendstoUniformlyOn_vectorMeasureState_of_weak (n:=n) β t ht hν
  exact hh.tendsto_at (x:=(r,sample)) ⟨⟨by positivity,hr⟩,Set.mem_univ _⟩

theorem tendsto_vectorMeasureTerminalObservable_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (d:Configuration n→ℝ)
    (sample:VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorMeasureTerminalObservable (ν j) β t ht d sample) l
      (𝓝 (vectorMeasureTerminalObservable μ β t ht d sample)):=by
  have hX:=tendsto_vectorMeasureState_of_weak β t ht hν 1 le_rfl sample
  have hz:Tendsto (fun j=>(sample.1,vectorMeasureState (ν j) β t ht 1 sample)) l
      (𝓝 (sample.1,vectorMeasureState μ β t ht 1 sample)):=
    tendsto_const_nhds.prodMk_nhds hX
  have hh:=((continuous_vectorTerminalMean_joint β t d).tendsto
    (sample.1,vectorMeasureState μ β t ht 1 sample)).comp hz
  exact hh

theorem tendsto_vectorMeasureSpinMean_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (q:Paper.Overlap)
    (sample:VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorMeasureSpinMean (ν j) β t ht q sample) l
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample)):=by
  have hr:(q:ℝ).toNNReal≤1:=by
    simpa using Real.toNNReal_le_toNNReal q.property.2
  have hX:=tendsto_vectorMeasureState_of_weak β t ht hν _ hr sample
  have hz:Tendsto (fun j=>(q,(sample.1,vectorMeasureState (ν j) β t ht (q:ℝ).toNNReal sample))) l
      (𝓝 (q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))):=
    tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hX)
  have hgrad:=tendstoUniformly_vectorMeasureGradient_of_weak (n:=n) β t ht hν
  have hc:ContinuousAt (fun z:Paper.Overlap×VectorParameter n=>
      vectorMeasureGradient μ β t z.1 z.2.1 z.2.2)
      (q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)):=
    (continuous_vectorMeasureGradient μ β t ht).continuousAt
  have hh:=hgrad.tendsto_comp hc hz
  exact hh

theorem tendsto_vectorBasePairObservable_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (i k:Fin n) (sample:VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorBasePairObservable (ν j) β t ht i k sample) l
      (𝓝 (vectorBasePairObservable μ β t ht i k sample)):=
  tendsto_vectorMeasureTerminalObservable_of_weak β t ht hν _ sample

theorem tendsto_vectorBaseMeanProduct_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (q:Paper.Overlap) (i k:Fin n)
    (sample:VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorBaseMeanProduct (ν j) β t ht q i k sample) l
      (𝓝 (vectorBaseMeanProduct μ β t ht q i k sample)):=by
  have hX:=tendsto_vectorMeasureSpinMean_of_weak β t ht hν q sample
  exact (((EuclideanSpace.proj i).continuous.tendsto _).comp hX).mul
    (((EuclideanSpace.proj k).continuous.tendsto _).comp hX)

theorem tendsto_vectorMeasurePotential_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (p:Couplings n×ℝ) (x:Field n) :
    Tendsto (fun j=>vectorMeasurePotential (ν j) β t p x) l
      (𝓝 (vectorMeasurePotential μ β t p x)):=by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb:Tendsto (fun j=>(n:ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance (ν j) μ) l (𝓝 0):=by
    simpa only [mul_zero] using
      (FRSB.tendsto_parisiCDFDistance_of_tendsto hν).const_mul ((n:ℝ)*((1-t)*β^2))
  exact squeeze_zero (fun _=>dist_nonneg)
    (fun j=>by simpa only [Real.dist_eq] using
      vectorMeasurePotential_CDFDistance_abs_sub_le (ν j) μ β t ht p x) hb

theorem vectorMeasurePotential_profile_local_bound (β t:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) :
    ∀ᶠj in l,∀p:Couplings n×ℝ,
      |vectorMeasurePotential (ν j) β t p 0|≤
        (|vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1)+vectorDisorderNormConstant n β 1*‖p‖:=by
  have hb:=((tendsto_vectorMeasurePotential_of_weak (n:=n) β t ht.le hν (0,0) 0).abs).eventually
    (gt_mem_nhds (by linarith:|vectorMeasurePotential (n:=n) μ β t (0,0) 0|<
      |vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1))
  filter_upwards [hb] with j hj
  intro p
  have hd:=(vectorMeasurePotential_disorder_bound (ν j) β t ht.le p (0:Field n)).trans
    ((vectorDisorderEnvelope_le_norm n β t p).trans
      (mul_le_mul_of_nonneg_right (vectorDisorderNormConstant_le_one_time n β t ht.le) (norm_nonneg _)))
  have he:=abs_add_le (vectorMeasurePotential (n:=n) (ν j) β t (0,0) 0)
    (vectorMeasurePotential (ν j) β t p 0-vectorMeasurePotential (n:=n) (ν j) β t (0,0) 0)
  rw [add_sub_cancel] at he
  linarith

end QuantitativePaper
