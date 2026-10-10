module
public import QuantitativeFollowup.VectorQuantileBinSquareTail
public import QuantitativeFollowup.VectorSelfOverlapSquareTail
public import FourPapersCommon.ReciprocalIntervalTail
public import FourPapersCommon.LogMomentConstants

@[expose] public section

/-! Actual integrated square-tail estimate on each monotone level bin. The
reciprocal tail is integrated after a genuine boundary strip of width 1/M. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_bin_tail_integral (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2))
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioc (0:ℝ) (1-s))
    (a θ : ℝ) (hθ : 0<θ)
    (hRange : ∀w∈I,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+θ/4)) :
    (∫v in I,vectorSelfOverlapSquareTail (n:=n) μ β t s ht.le θ (parisiFreeQuantile μ s v))≤
      34*(1/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2))) :=by
  let M:=(n:ℝ)*((1-t)*β^2)
  let ε:=1/(M*s)
  let up : ℝ→ℝ:=fun v=>vectorSelfOverlapUpperSquareTail (n:=n) μ β t s ht.le θ (parisiFreeQuantile μ s v)
  let dn : ℝ→ℝ:=fun v=>vectorSelfOverlapLowerSquareTail (n:=n) μ β t s ht.le θ (parisiFreeQuantile μ s v)
  let tail : ℝ→ℝ:=fun v=>vectorSelfOverlapSquareTail (n:=n) μ β t s ht.le θ (parisiFreeQuantile μ s v)
  have hMp : 0<M:=lt_of_lt_of_le zero_lt_one hM
  have hε : 0<ε:=one_div_pos.mpr (mul_pos hMp hs.1)
  have hup : Measurable up:=(measurable_vectorSelfOverlapUpperSquareTail μ β t s ht.le θ).comp (parisiFreeQuantile_measurable μ s)
  have hdn : Measurable dn:=(measurable_vectorSelfOverlapLowerSquareTail μ β t s ht.le θ).comp (parisiFreeQuantile_measurable μ s)
  have htail : Measurable tail:=(measurable_vectorSelfOverlapSquareTail μ β t s ht.le θ).comp (parisiFreeQuantile_measurable μ s)
  have hupBound (v : ℝ) : 0≤up v ∧ up v≤1:=
    (vectorSelfOverlap_one_sided_square_tail_bounds hn μ β t s ht.le θ _).1
  have hdnBound (v : ℝ) : 0≤dn v ∧ dn v≤1:=
    (vectorSelfOverlap_one_sided_square_tail_bounds hn μ β t s ht.le θ _).2
  have hfinite : volume I≠∞:=
    (lt_of_le_of_lt (measure_mono hDom) (by rw [Real.volume_Ioc];exact ENNReal.ofReal_lt_top)).ne
  have hRpos : 0≤34*ε*Real.log (2*M):=by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith)
  by_cases hv : 0<volume.real I
  · have hb : BddBelow I:=⟨0,fun v hv=>(hDom hv).1.le⟩
    have ha : BddAbove I:=⟨1-s,fun v hv=>(hDom hv).2⟩
    have hne : I.Nonempty:=nonempty_of_measureReal_ne_zero hv.ne'
    have hin : Ioo (sInf I) (sSup I)⊆I:=
      (show IsConnected I from ⟨hne,hI.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
    have hlr : sInf I<sSup I:=by
      rw [volume_ordConnected_eq_endpoints I hI hb ha] at hv
      by_contra h
      rw [max_eq_right (sub_nonpos.mpr (not_lt.mp h))] at hv
      exact lt_irrefl _ hv
    have hlen : sSup I-sInf I≤1:=by
      have hl:=le_csInf hne (fun _ h=>(hDom h).1.le)
      have hr:=csSup_le hne (fun _ h=>(hDom h).2)
      linarith [hs.1]
    have hT : ∀ᵐw ∂volume.restrict I,s≤Paper.parisiCDF μ (parisiFreeQuantile μ s w):=by
      filter_upwards [ae_restrict_mem hI.measurableSet] with w hw
      have he:=parisiCDF_freeQuantile_lower μ s ⟨hs.1.le,by linarith [hs.2]⟩ (hDom hw)
      linarith [(hDom hw).1]
    have hpoint (v : ℝ) (hv : v∈Ioo (sInf I) (sSup I)) :
        up v≤16*ε/(sSup I-v) ∧ dn v≤16*ε/(v-sInf I) :=by
      have he:=vector_quantile_bin_one_sided_square_tails hn μ s β t hβ ht
        ⟨hs.1,by linarith [hs.2]⟩ hμ hmin I hI hDom a (θ/4) s θ
        (by positivity) hs.1 hθ (by linarith) hRange hT (hin hv) hv
      exact he
    have hu:=integral_right_reciprocal_tail_bound up hup (sInf I) (sSup I) (16*ε) M
      hlr.le hlen (by positivity) hM hupBound (fun v hv=>(hpoint v hv).1)
    have hd:=integral_left_reciprocal_tail_bound dn hdn (sInf I) (sSup I) (16*ε) M
      hlr.le hlen (by positivity) hM hdnBound (fun v hv=>(hpoint v hv).2)
    have hiUp : IntegrableOn up (Ioo (sInf I) (sSup I)):=
      Integrable.of_bound hup.aestronglyMeasurable 1 (.of_forall fun v=>by rw [Real.norm_of_nonneg (hupBound v).1];exact (hupBound v).2)
    have hiDn : IntegrableOn dn (Ioo (sInf I) (sSup I)):=
      Integrable.of_bound hdn.aestronglyMeasurable 1 (.of_forall fun v=>by rw [Real.norm_of_nonneg (hdnBound v).1];exact (hdnBound v).2)
    rw [setIntegral_congr_set (ordConnected_ae_eq_open_interval I hI hb ha)]
    have heSum : tail=up+dn:=by
      funext v
      exact vectorSelfOverlapSquareTail_eq_sum hn μ β t s ht.le θ hθ.le _
    change (∫v in Ioo (sInf I) (sSup I),tail v)≤_
    rw [heSum]
    simp only [Pi.add_apply]
    have heAdd:=integral_add hiUp hiDn
    rw [heAdd]
    apply (show (∫v in Ioo (sInf I) (sSup I),up v)+(∫v in Ioo (sInf I) (sSup I),dn v)≤2/M+32*ε*Real.log M by
      convert add_le_add hu hd using 1 <;> ring).trans
    exact bin_tail_constant_bound M s hM hs
  · have he : volume I=0:=(measureReal_eq_zero_iff hfinite).mp (le_antisymm (not_lt.mp hv) measureReal_nonneg)
    rw [Measure.restrict_eq_zero.mpr he,integral_zero_measure]
    exact hRpos

end QuantitativeFollowup
