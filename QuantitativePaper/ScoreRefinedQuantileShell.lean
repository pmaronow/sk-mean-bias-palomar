module
public import QuantitativePaper.ScoreQuantileRefinementIntegral
public import QuantitativePaper.ScoreQuantileVarianceDecomposition
public import QuantitativePaper.VectorScoreRange
public import FourPapersCommon.ScoreRefinementPowers

@[expose] public section

/-! Literal refined quantile-shell bound for the terminal-spin score L.
The conditional covariance is integrated using actual threshold windows;
the remaining term is the variance of the actual conditional mean S/2. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem score_shell_scale_identity (M u : ℝ) (hM : 0 < M) (hu : 0 < u) :
    u*(M*u^2)^(-(3/4:ℝ))=M^(-(3/4:ℝ))*u^(-(1/2:ℝ)) := by
  have hp : (u^2)^(-(3/4:ℝ))=u^((2:ℝ)*(-(3/4:ℝ))):=by
    rw [Real.rpow_mul hu.le,Real.rpow_two]
  rw [Real.mul_rpow hM.le (sq_nonneg u),hp]
  calc
    _=M^(-(3/4:ℝ))*(u^(1:ℝ)*u^((2:ℝ)*(-(3/4:ℝ)))):=by rw [Real.rpow_one];ring
    _=_:=by rw [←Real.rpow_add hu];norm_num

theorem score_reciprocal_shell_power (M u m : ℝ) (hM : 0 < M) (hu : 0 < u)
    (hm : 0 ≤ m) (hmu : m ≤ u) :
    (1/(M*u))^(3/4:ℝ)*m^(1/4:ℝ) ≤ M^(-(3/4:ℝ))*u^(-(1/2:ℝ)) := by
  have he : (1/(M*u))=M^(-1:ℝ)*u^(-1:ℝ):=by
    rw [Real.rpow_neg_one,Real.rpow_neg_one]
    field_simp
  calc
    _ ≤ (1/(M*u))^(3/4:ℝ)*u^(1/4:ℝ):=by gcongr
    _=_:=by
      rw [he,Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hM.le,
        ←Real.rpow_mul hu.le,mul_assoc,←Real.rpow_add hu]
      norm_num

theorem integrableOn_score_quantile_variance (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (β t a s : ℝ) (hβ : β≠0) (ht : t < 1) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I)] :
    IntegrableOn (fun v=>variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le
      (parisiFreeQuantile μ s v)) (vectorMeasureSpinPathLaw μ β t a ht.le)) I := by
  apply Integrable.of_bound
    ((measurable_scoreVariance_via_total hn μ β t a hβ ht).comp
      (parisiFreeQuantile_measurable μ s)).aestronglyMeasurable 1
  refine .of_forall fun v=>?_ 
  simp only [Function.comp_def]
  rw [Real.norm_of_nonneg (variance_nonneg _ _)]
  exact variance_vectorMeasureOverlapScore_le_one μ β t a ht.le _

theorem vector_mean_direction_covariance_shell_threshold (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t < 1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (J : Set ℝ) (hJ : J.OrdConnected) (hDom : J⊆Ioo (0:ℝ) (1-s))
    (m u : ℝ) (hm : 0 < m) (hlen : volume.real J=m) (hmu : m ≤ u)
    (hThreshold : ∀ᵐv ∂volume.restrict J,u ≤ Paper.parisiCDF μ (parisiFreeQuantile μ s v))
    (hMu : 1 ≤ (n:ℝ)*((1-t)*β^2)*u^2) :
    (∫v in J,vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)) ≤ 
      7176*(((n:ℝ)*((1-t)*β^2))^(-(3/4:ℝ))*u^(-(1/2:ℝ))) := by
  let M:=(n:ℝ)*((1-t)*β^2)
  have hM:0 < M:=mul_pos (Nat.cast_pos.mpr hn)
    (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hu:0 < u:=hm.trans_le hmu
  have hb:BddBelow J:=⟨0,fun v hv=>(hDom hv).1.le⟩
  have ha:BddAbove J:=⟨1-s,fun v hv=>(hDom hv).2.le⟩
  have heq:=ordConnected_ae_eq_open_interval J hJ hb ha
  have hlen':sSup J-sInf J=m:=by
    have hv:=volume_ordConnected_eq_endpoints J hJ hb ha
    rw [hlen] at hv
    have hp:sInf J < sSup J:=by
      by_contra h
      rw [max_eq_right (sub_nonpos.mpr (not_lt.mp h))] at hv
      linarith
    rw [max_eq_left (sub_nonneg.mpr hp.le)] at hv
    exact hv.symm
  have hne:J.Nonempty:=by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h,measureReal_empty] at hlen
    linarith
  have hin:Ioo (sInf J) (sSup J)⊆J:=
    (show IsConnected J from ⟨hne,hJ.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  have hT:=hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hin))
  have hh:=vector_mean_direction_covariance_interval_threshold_raw hn μ s β t hβ ht hs hμ hmin
    (sInf J) (sSup J) u (by linarith) hu
    (le_csInf hne (fun v hv=>(hDom hv).1.le))
    (csSup_le hne (fun v hv=>(hDom hv).2.le)) hT
  rw [←setIntegral_congr_set heq,hlen'] at hh
  have hε:0 < 1/(M*u):=by positivity
  have h1:= (integral_score_reciprocal_window (1/(M*u)) m hε hm).2
  have he:2/(M*u)=2*(1/(M*u)):=by ring
  change (∫v in J,vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)) ≤ 
    (∫x in Ioo (0:ℝ) m,min 1 ((2/(M*u))/x))+m*(112*(1+logPlus (M*u^2))^2/(M*u^2)) at hh
  rw [he] at hh
  have h2:=score_reciprocal_shell_power M u m hM hu hm.le hmu
  have h3:=score_logarithmic_residual_shell M u m hM hu hm.le hmu hMu
  have h4:m*(112*(1+logPlus (M*u^2))^2/(M*u^2)) ≤ 7168*M^(-(3/4:ℝ))*u^(-(1/2:ℝ)):=by
    convert h3 using 1 <;>ring
  change _ ≤ 7176*(M^(-(3/4:ℝ))*u^(-(1/2:ℝ)))
  exact hh.trans (by nlinarith)

/-- The refined shell estimate for the actual terminal-spin score, with a
universal constant and the literal essential quantile-image diameter. -/
theorem vector_refined_score_quantile_shell (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t < 1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (J : Set ℝ) (hJ : J.OrdConnected) (hDom : J⊆Ioo (0:ℝ) (1-s))
    (m u : ℝ) (hm : 0 < m) (hlen : volume.real J=m) (hmu : m ≤ u)
    (hThreshold : ∀ᵐv ∂volume.restrict J,u ≤ Paper.parisiCDF μ (parisiFreeQuantile μ s v)) :
    (∫v in J,variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
      (vectorMeasureSpinPathLaw μ β t s ht.le)) ≤
      8192*((((n:ℝ)*((1-t)*β^2))^(-(3/4:ℝ)))*u^(-(1/2:ℝ))+
        (((n:ℝ)*((1-t)*β^2))^(-(2/3:ℝ)))*u^(-(1/3:ℝ))*
          (parisiQuantileImageDiameter μ s J)^(2/3:ℝ)) := by
  let M:=(n:ℝ)*((1-t)*β^2)
  let T1:=M^(-(3/4:ℝ))*u^(-(1/2:ℝ))
  let T2:=M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*(parisiQuantileImageDiameter μ s J)^(2/3:ℝ)
  have hM:0 < M:=mul_pos (Nat.cast_pos.mpr hn)
    (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hu:0 < u:=hm.trans_le hmu
  have hT1:0 ≤ T1:=by positivity
  have hell:=parisiQuantileImageDiameter_nonneg_of_positive_interval μ s J hJ hDom (hlen.symm ▸ hm)
  have hT2:0 ≤ T2:=by positivity
  let :=isFiniteMeasure_of_le (volume.restrict (Ioc (0:ℝ) (1-s)))
    (Measure.restrict_mono_set volume (hDom.trans Ioo_subset_Ioc_self))
  let L:ℝ→ℝ:=fun v=>variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le
    (parisiFreeQuantile μ s v)) (vectorMeasureSpinPathLaw μ β t s ht.le)
  let C:ℝ→ℝ:=fun v=>vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)
  let S:ℝ→ℝ:=fun v=>variance (vectorSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
    (vectorMeasureSpinPathLaw μ β t s ht.le)
  have hiL:IntegrableOn L J:=integrableOn_score_quantile_variance hn μ β t s s hβ ht J
  have hiC:IntegrableOn C J:=by
    apply Integrable.of_bound
      ((measurable_vectorMeanDirectionCovariance μ β t s hβ ht).comp
        (parisiFreeQuantile_measurable μ s)).aestronglyMeasurable 1
    refine .of_forall fun v=>?_ 
    simp only [Function.comp_def]
    rw [Real.norm_of_nonneg (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t s hβ ht _).1]
    exact (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t s hβ ht _).2
  have hiS:IntegrableOn S J:=integrableOn_variance_vectorSelfOverlap hn μ β t s ht.le J s
  change (∫v in J,L v) ≤ 8192*(T1+T2)
  by_cases hX:1 ≤ M*u^2
  · have hc:=vector_mean_direction_covariance_shell_threshold hn μ s β t hβ ht hs hμ hmin
      J hJ hDom m u hm hlen hmu hThreshold hX
    change (∫v in J,C v) ≤ 7176*T1 at hc
    have hsvar:=vector_refined_quantile_shell hn μ s β t hβ ht hs hμ hmin
      J hJ hDom m u hm hlen hmu hThreshold
    change (∫v in J,S v) ≤ 2560*(T1+T2) at hsvar
    have he:(∫v in J,L v)=(∫v in J,C v)+(1/4)*(∫v in J,S v):=by
      rw [show L=(fun v=>C v+(1/4)*S v) from by
        funext v
        exact variance_vectorMeasureOverlapScore_eq_mean_covariance μ β t s hβ ht _,
        integral_add hiC (hiS.const_mul (1/4)),integral_const_mul]
    rw [he]
    nlinarith
  · have hx:0 < M*u^2:=mul_pos hM (sq_pos_of_pos hu)
    have hp:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (le_of_not_ge hX)
      (by norm_num : -(3/4:ℝ) ≤ 0)
    have hule:u ≤ T1:=by
      change u ≤ M^(-(3/4:ℝ))*u^(-(1/2:ℝ))
      rw [←score_shell_scale_identity M u hM hu]
      nlinarith
    have hb:=integral_mono hiL (integrable_const (1:ℝ))
      (fun v=>variance_vectorMeasureOverlapScore_le_one μ β t s ht.le (parisiFreeQuantile μ s v))
    rw [setIntegral_const,hlen,smul_eq_mul,mul_one] at hb
    exact hb.trans (by nlinarith)

end QuantitativePaper
