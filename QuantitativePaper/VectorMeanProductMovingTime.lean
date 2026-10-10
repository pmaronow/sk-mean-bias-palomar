module
public import QuantitativePaper.VectorConditionalPairMovingTime

@[expose] public section

/-! Actual adapted mean-products and their tilted expectations converge
under simultaneous weak profile convergence and moving physical time. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n:ℕ} {J:Type*} {l:Filter J} [l.IsCountablyGenerated]
variable {ν:J→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure}
variable {qj:J→Paper.Overlap} {q:Paper.Overlap}

theorem tendsto_vectorMeasureState_of_weak_and_time (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (hq:Tendsto qj l (𝓝 q)) (sample:VectorDisorderBrownianSample n):
    Tendsto (fun j=>vectorMeasureState (ν j) β t ht (qj j:ℝ).toNNReal sample) l
      (𝓝 (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)):=by
  let z:Paper.Overlap→ℝ≥0×VectorDisorderBrownianSample n:=fun r=>((r:ℝ).toNNReal,sample)
  have hz:z⁻¹' (Icc (0:ℝ≥0) 1×ˢ univ)=univ:=by
    ext r
    simp only [mem_preimage,mem_prod,mem_Icc,mem_univ,and_true,iff_true,z]
    exact ⟨by positivity,by simpa using Real.toNNReal_le_toNNReal r.property.2⟩
  have hu:TendstoUniformly
      (fun j=>fun r:Paper.Overlap=>vectorMeasureState (ν j) β t ht (r:ℝ).toNNReal sample)
      (fun r:Paper.Overlap=>vectorMeasureState μ β t ht (r:ℝ).toNNReal sample) l:=by
    simpa only [hz,Function.comp_def,z,tendstoUniformlyOn_univ] using
      (tendstoUniformlyOn_vectorMeasureState_of_weak (n:=n) β t ht hν).comp z
  have hc:Continuous (fun r:Paper.Overlap=>vectorMeasureState μ β t ht (r:ℝ).toNNReal sample):=
    (continuous_vectorMeasureState μ β t ht sample).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)
  exact hu.tendsto_comp hc.continuousAt hq

theorem tendsto_vectorMeasureSpinMean_of_weak_and_time (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (hq:Tendsto qj l (𝓝 q)) (sample:VectorDisorderBrownianSample n):
    Tendsto (fun j=>vectorMeasureSpinMean (ν j) β t ht (qj j) sample) l
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample)):=by
  have hX:=tendsto_vectorMeasureState_of_weak_and_time β t ht hν hq sample
  have hz:Tendsto (fun j=>(qj j,(sample.1,vectorMeasureState (ν j) β t ht (qj j:ℝ).toNNReal sample))) l
      (𝓝 (q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))):=
    hq.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hX)
  have hgrad:=tendstoUniformly_vectorMeasureGradient_of_weak (n:=n) β t ht hν
  have hc:ContinuousAt (fun z:Paper.Overlap×VectorParameter n=>
      vectorMeasureGradient μ β t z.1 z.2.1 z.2.2)
      (q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)):=
    (continuous_vectorMeasureGradient μ β t ht).continuousAt
  have hh:=hgrad.tendsto_comp hc hz
  exact hh

theorem tendsto_vectorBaseMeanProduct_toLp_of_weak_and_time (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (hq:Tendsto qj l (𝓝 q)) (i k:Fin n):
    Tendsto (fun j=>(memLp_vectorBaseMeanProduct (ν j) β t ht (qj j) i k).toLp
      (vectorBaseMeanProduct (ν j) β t ht (qj j) i k)) l
      (𝓝 ((memLp_vectorBaseMeanProduct μ β t ht q i k).toLp
        (vectorBaseMeanProduct μ β t ht q i k))):=by
  apply temperatureDensity_toLp_tendsto_of_dominated
    (fun j=>vectorBaseMeanProduct (ν j) β t ht (qj j) i k)
    (vectorBaseMeanProduct μ β t ht q i k)
    (fun j=>memLp_vectorBaseMeanProduct (ν j) β t ht (qj j) i k)
    (memLp_vectorBaseMeanProduct μ β t ht q i k) (fun _=>1)
    (by simpa using integrable_const (1:ℝ) (μ:=vectorDisorderBrownianMeasure n))
    (.of_forall fun j=>.of_forall (vectorBaseMeanProduct_bound (ν j) β t ht (qj j) i k))
    (.of_forall (vectorBaseMeanProduct_bound μ β t ht q i k))
  exact .of_forall fun sample=>by
    have hX:=tendsto_vectorMeasureSpinMean_of_weak_and_time β t ht hν hq sample
    exact (((EuclideanSpace.proj i).continuous.tendsto _).comp hX).mul
      (((EuclideanSpace.proj k).continuous.tendsto _).comp hX)

theorem integral_vectorBaseMeanProduct_eq_base (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) (i k:Fin n):
    (∫sample,vectorBaseMeanProduct μ β t ht q i k sample
      ∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
    ∫sample,vectorBaseOuterWeight μ β t a sample*vectorBaseMeanProduct μ β t ht q i k sample
      ∂vectorDisorderBrownianMeasure n:=by
  rw [vectorMeasureDisorderTilt]
  have hd:Measurable (fun sample:VectorDisorderBrownianSample n=>
      ENNReal.ofReal (vectorMeasureOuterWeight μ β t a sample.1)):=
    ((measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    simp only [smul_eq_mul]
    have hpos:0≤vectorMeasureOuterWeight (n:=n) μ β t a sample.1:=
      div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t a ht).le
    rw [ENNReal.toReal_ofReal hpos]
    rfl

theorem tendsto_integral_vectorBaseMeanProduct_of_weak_and_time (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) (hq:Tendsto qj l (𝓝 q)) (i k:Fin n):
    Tendsto (fun j=>∫sample,vectorBaseMeanProduct (ν j) β t ht.le (qj j) i k sample
      ∂vectorMeasureDisorderTilt (n:=n) (ν j) β t a) l
      (𝓝 (∫sample,vectorBaseMeanProduct μ β t ht.le q i k sample
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a)):=by
  have hw:=tendsto_vectorBaseOuterWeight_toLp_of_weak (n:=n) β t a ht hν
  have hM:=tendsto_vectorBaseMeanProduct_toLp_of_weak_and_time β t ht.le hν hq i k
  have hp:=((continuous_fst.inner continuous_snd:
      Continuous (fun z:Lp ℝ 2 (vectorDisorderBrownianMeasure n)×Lp ℝ 2 (vectorDisorderBrownianMeasure n)=>
        inner ℝ z.1 z.2)).tendsto
      ((memLp_vectorBaseOuterWeight μ β t a ht.le).toLp (vectorBaseOuterWeight μ β t a),
        (memLp_vectorBaseMeanProduct μ β t ht.le q i k).toLp (vectorBaseMeanProduct μ β t ht.le q i k))).comp
      (hw.prodMk_nhds hM)
  have hi (ν:Paper.ParisiMeasure) (r:Paper.Overlap):
      inner ℝ ((memLp_vectorBaseOuterWeight (n:=n) ν β t a ht.le).toLp (vectorBaseOuterWeight ν β t a))
        ((memLp_vectorBaseMeanProduct ν β t ht.le r i k).toLp (vectorBaseMeanProduct ν β t ht.le r i k))=
      ∫sample,vectorBaseMeanProduct ν β t ht.le r i k sample∂vectorMeasureDisorderTilt ν β t a:=by
    rw [L2.inner_def,integral_vectorBaseMeanProduct_eq_base ν β t a ht.le r i k]
    apply integral_congr_ae
    filter_upwards [(memLp_vectorBaseOuterWeight ν β t a ht.le).coeFn_toLp,
      (memLp_vectorBaseMeanProduct ν β t ht.le r i k).coeFn_toLp] with sample hw hM
    simp only [RCLike.inner_apply,conj_trivial,hw,hM,mul_comm]
  simpa only [Function.comp_def,hi] using hp

end QuantitativePaper
