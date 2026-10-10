module
public import QuantitativePaper.ScoreQuantileRefinementResidual
public import FourPapersCommon.ReciprocalStripIntegration

@[expose] public section

/-! Actual threshold-shell integration of the terminal score's conditional
covariance. Earlier windows lie inside the same threshold interval; no
self-overlap variance is substituted for the score covariance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_mean_direction_covariance_interval_threshold_raw (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (l r u : ℝ) (hlr : l<r) (hu : 0<u) (hl : 0≤l) (hr : r≤1-s)
    (hThreshold : ∀ᵐv ∂volume.restrict (Ioo l r),
      u≤Paper.parisiCDF μ (parisiFreeQuantile μ s v)) :
    (∫v in Ioo l r,vectorMeanDirectionCovariance (n:=n) μ β t s ht.le
      (parisiFreeQuantile μ s v))≤
      (∫x in Ioo (0:ℝ) (r-l),min 1 ((2/((n:ℝ)*((1-t)*β^2)*u))/x))+
        (r-l)*(112*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
          ((n:ℝ)*((1-t)*β^2)*u^2)) := by
  let M:=(n:ℝ)*((1-t)*β^2)
  let C:=112*(1+logPlus (M*u^2))^2/(M*u^2)
  let f:ℝ→ℝ:=fun v=>vectorMeanDirectionCovariance (n:=n) μ β t s ht.le
    (parisiFreeQuantile μ s v)
  let g:ℝ→ℝ:=fun v=>min 1 ((2/(M*u))/(v-l))
  have hM:0<M:=mul_pos (Nat.cast_pos.mpr hn)
    (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hC:0≤C:=by positivity
  have hf:Measurable f:=(measurable_vectorMeanDirectionCovariance μ β t s hβ ht).comp
    (parisiFreeQuantile_measurable μ s)
  have hg:Measurable g:=measurable_const.min
    (measurable_const.div (measurable_id.sub_const l))
  have hi:IntegrableOn f (Ioo l r):=Integrable.of_bound hf.aestronglyMeasurable 1
    (.of_forall fun v=>by
      rw [Real.norm_of_nonneg (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t s hβ ht _).1]
      exact (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t s hβ ht _).2)
  have hig:IntegrableOn g (Ioo l r):=by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_of_nonneg (by dsimp only [g];exact le_min zero_le_one (div_nonneg (by positivity) (sub_nonneg.mpr hv.1.le)))]
    exact min_le_left _ _
  have hbound:∀ᵐv ∂volume.restrict (Ioo l r),f v≤g v+C:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hx:0<v-l:=sub_pos.mpr hv.1
    have hwin:Ioc (v-(v-l)) v⊆Ioo l r:=by
      intro w hw
      refine ⟨?_,hw.2.trans_lt hv.2⟩
      linarith [hw.1]
    have hT:=hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hwin))
    have hb:=vector_mean_direction_covariance_window_threshold hn μ s β t v (v-l) u hβ ht hs hμ hmin
      ⟨hl.trans_lt hv.1,(hv.2.trans_le hr).le⟩ hx (by linarith) hu
      (hwin.trans (fun w hw=>⟨hl.trans_lt hw.1,(hw.2.trans_le hr).le⟩)) hT
    have he:2/(M*u*(v-l))=(2/(M*u))/(v-l):=by rw [div_div]
    change f v≤2/(M*u*(v-l))+C at hb
    rw [he] at hb
    by_cases ha:1≤(2/(M*u))/(v-l)
    · rw [show g v=1 from min_eq_left ha]
      linarith [(vectorMeanDirectionCovariance_nonneg_le_one hn μ β t s hβ ht
        (parisiFreeQuantile μ s v)).2]
    · rw [show g v=(2/(M*u))/(v-l) from min_eq_right (le_of_not_ge ha)]
      exact hb
  have hh:=integral_mono_ae hi (hig.add (integrable_const C)) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add hig (integrable_const C),setIntegral_const,Real.volume_real_Ioo,
    max_eq_left (sub_nonneg.mpr hlr.le),smul_eq_mul] at hh
  rw [show (∫v in Ioo l r,g v)=(∫x in Ioo (0:ℝ) (r-l),min 1 ((2/(M*u))/x)) from
    integral_translated_truncated_reciprocal l r (2/(M*u)) hlr.le] at hh
  exact hh

end QuantitativePaper
