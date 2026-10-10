module
public import QuantitativePaper.VectorBrownianConditionalMovingTime

@[expose] public section

/-! Genuine convergence of the tilted raw conditional spin-pair square
moment with simultaneous weak profile convergence and moving conditioning
time. This is the second-pair moment in the interpolation defect. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128

section General
variable {Ω:Type*} [mΩ:MeasurableSpace Ω] {P:Measure Ω} [IsProbabilityMeasure P]
variable {J:Type*} {l:Filter J}

theorem tendsto_weighted_conditional_square_of_moving_L2
    (Vj:J→MeasurableSpace Ω) (V:MeasurableSpace Ω)
    (hVj:∀j,Vj j ≤ mΩ) (hV:V ≤ mΩ)
    (fj wj:J→Ω→ℝ) (f w:Ω→ℝ)
    (hfj:∀j,MemLp (fj j) 2 P) (hf:MemLp f 2 P)
    (hwj:∀j,MemLp (wj j) 2 P) (hw:MemLp w 2 P)
    (hc:Tendsto (fun j=>conditionalBaseL2 (mΩ:=mΩ) (Vj j) (hVj j) ((hfj j).toLp (fj j))) l
      (𝓝 (conditionalBaseL2 (mΩ:=mΩ) V hV (hf.toLp f))))
    (hwlim:Tendsto (fun j=>(hwj j).toLp (wj j)) l (𝓝 (hw.toLp w)))
    (hfjb:∀j,∀ᵐx ∂P,‖fj j x‖≤1) (hfb:∀ᵐx ∂P,‖f x‖≤1):
    Tendsto (fun j=>∫x,wj j x*(P[fj j|Vj j] x)^2∂P) l
      (𝓝 (∫x,w x*(P[f|V] x)^2∂P)):=by
  letI:MeasurableSpace Ω:=mΩ
  let cj:J→Lp ℝ 2 P:=fun j=>conditionalBaseL2 (mΩ:=mΩ) (Vj j) (hVj j) ((hfj j).toLp (fj j))
  let c:Lp ℝ 2 P:=conditionalBaseL2 (mΩ:=mΩ) V hV (hf.toLp f)
  let sq:Lp ℝ 2 P→Lp ℝ 2 P:=lipschitzWith_conditionalCovarianceSquareClip.compLp
    conditionalCovarianceSquareClip_zero
  have hs:Tendsto (fun j=>sq (cj j)) l (𝓝 (sq c)):=
    (lipschitzWith_conditionalCovarianceSquareClip.continuous_compLp
      conditionalCovarianceSquareClip_zero).continuousAt.tendsto.comp hc
  have hp:=((continuous_fst.inner continuous_snd:
      Continuous (fun z:Lp ℝ 2 P×Lp ℝ 2 P=>inner ℝ z.1 z.2)).tendsto
      (hw.toLp w,sq c)).comp (hwlim.prodMk_nhds hs)
  have hj (j:J):(sq (cj j):Ω→ℝ)=ᵐ[P] fun x=>(P[fj j|Vj j] x)^2:=by
    filter_upwards [lipschitzWith_conditionalCovarianceSquareClip.coeFn_compLp
      conditionalCovarianceSquareClip_zero (cj j),
      conditionalBaseL2_ae (mΩ:=mΩ) (Vj j) (hVj j) (fj j) (hfj j),
      ae_bdd_norm_condExp_of_ae_bdd_norm (m:=Vj j) (hfjb j)] with x hs hce hb
    rw [hs]
    dsimp only [cj]
    simp only [Function.comp_def,hce]
    apply conditionalCovarianceSquareClip_eq
    simpa only [Real.norm_eq_abs] using hb.trans (by norm_num : (1:ℝ)≤2)
  have he:(sq c:Ω→ℝ)=ᵐ[P] fun x=>(P[f|V] x)^2:=by
    filter_upwards [lipschitzWith_conditionalCovarianceSquareClip.coeFn_compLp
      conditionalCovarianceSquareClip_zero c,
      conditionalBaseL2_ae (mΩ:=mΩ) V hV f hf,
      ae_bdd_norm_condExp_of_ae_bdd_norm (m:=V) hfb] with x hs hce hb
    rw [hs]
    dsimp only [c]
    simp only [Function.comp_def,hce]
    apply conditionalCovarianceSquareClip_eq
    simpa only [Real.norm_eq_abs] using hb.trans (by norm_num : (1:ℝ)≤2)
  have hi (A B:Lp ℝ 2 P):inner ℝ A B=∫x,A x*B x∂P:=by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial,mul_comm]
  have hje (j:J):inner ℝ ((hwj j).toLp (wj j)) (sq (cj j))=
      ∫x,wj j x*(P[fj j|Vj j] x)^2∂P:=by
    rw [hi]
    exact integral_congr_ae ((hwj j).coeFn_toLp.mul (hj j))
  have hve:inner ℝ (hw.toLp w) (sq c)=∫x,w x*(P[f|V] x)^2∂P:=by
    rw [hi]
    exact integral_congr_ae (hw.coeFn_toLp.mul he)
  simpa only [Function.comp_def,hje,hve] using hp

end General
variable {n:ℕ} {J:Type*} {l:Filter J} [l.IsCountablyGenerated]
variable {ν:J→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure}

theorem vectorMeasureRawPair_square_eq_base (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) (i k:Fin n):
    (∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i k+
      vectorBaseMeanProduct μ β t ht q i k sample)^2
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
    ∫sample,vectorBaseOuterWeight μ β t a sample*
      ((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i k|
        vectorBrownianFiltration n (q:ℝ).toNNReal] sample)^2
        ∂vectorDisorderBrownianMeasure n:=by
  have he:=vectorMeasureTerminalObservable_condExp_eq_base (n:=n) μ β t a ht q
    (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ k))
  have hh:(∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i k+
      vectorBaseMeanProduct μ β t ht q i k sample)^2∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
      ∫sample,((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i k|
        vectorBrownianFiltration n (q:ℝ).toNNReal] sample)^2∂vectorMeasureDisorderTilt μ β t a:=by
    apply integral_congr_ae
    filter_upwards [he] with sample hs
    simp only [vectorMeasureSpinCovariance,vectorBasePairObservable,vectorBaseMeanProduct,hs,sub_add_cancel]
  rw [hh,vectorMeasureDisorderTilt]
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

theorem tendsto_vectorMeasureRawPair_square_of_weak_and_time
    (β t a:ℝ) (ht:t<1) (hν:Tendsto ν l (𝓝 μ))
    {qj:J→Paper.Overlap} {q:Paper.Overlap} (hq:Tendsto qj l (𝓝 q)) (i k:Fin n):
    Tendsto (fun j=>∫sample,(vectorMeasureSpinCovariance (ν j) β t a ht.le (qj j) sample i k+
      vectorBaseMeanProduct (ν j) β t ht.le (qj j) i k sample)^2
        ∂vectorMeasureDisorderTilt (n:=n) (ν j) β t a) l
      (𝓝 (∫sample,(vectorMeasureSpinCovariance μ β t a ht.le q sample i k+
        vectorBaseMeanProduct μ β t ht.le q i k sample)^2
          ∂vectorMeasureDisorderTilt (n:=n) μ β t a)):=by
  simp_rw [vectorMeasureRawPair_square_eq_base]
  exact tendsto_weighted_conditional_square_of_moving_L2
    (fun j=>vectorBrownianFiltration n (qj j:ℝ).toNNReal)
    (vectorBrownianFiltration n (q:ℝ).toNNReal)
    (fun j=>(vectorBrownianFiltration n).le _) ((vectorBrownianFiltration n).le _)
    (fun j=>vectorBasePairObservable (ν j) β t ht.le i k)
    (fun j=>vectorBaseOuterWeight (ν j) β t a)
    (vectorBasePairObservable μ β t ht.le i k) (vectorBaseOuterWeight μ β t a)
    (fun j=>memLp_vectorBasePairObservable (ν j) β t ht.le i k)
    (memLp_vectorBasePairObservable μ β t ht.le i k)
    (fun j=>memLp_vectorBaseOuterWeight (ν j) β t a ht.le)
    (memLp_vectorBaseOuterWeight μ β t a ht.le)
    (tendsto_conditionalBaseL2_vectorBasePairObservable_of_weak_and_time β t ht.le hν hq i k)
    (tendsto_vectorBaseOuterWeight_toLp_of_weak β t a ht hν)
    (fun j=>.of_forall (vectorBasePairObservable_bound (ν j) β t ht.le i k))
    (.of_forall (vectorBasePairObservable_bound μ β t ht.le i k))

end QuantitativePaper
