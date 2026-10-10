module
public import Paper.ParisiCDFGrid

@[expose] public section

/-! The actual CDF L¹ distance is bounded by the mean displacement of
any coupling. This is proved by the upper-triangle indicators and Fubini,
including all atoms; no optimal-transport identity is assumed. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem integral_abs_upperIndicator_sub (x y : ℝ)
    (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    (∫t in (0:ℝ)..1,|(if x≤t then (1:ℝ) else 0)-(if y≤t then (1:ℝ) else 0)|)=|x-y| := by
  have hi (z : ℝ) : IntervalIntegrable (fun t : ℝ=>if z≤t then (1:ℝ) else 0) volume 0 1 := by
    apply IntervalIntegrable.mono_fun' (g:=fun _=>(1:ℝ)) intervalIntegrable_const
    · exact (measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable
    · filter_upwards with t
      split <;>norm_num
  by_cases hxy : x≤y
  · have he : (fun t : ℝ=>|(if x≤t then (1:ℝ) else 0)-(if y≤t then (1:ℝ) else 0)|)=
        (fun t=>(if x≤t then (1:ℝ) else 0)-(if y≤t then (1:ℝ) else 0)) := by
      funext t
      apply abs_of_nonneg
      split_ifs with hxt hyt hyt <;>norm_num at *
      linarith
    rw [he,intervalIntegral.integral_sub (hi x) (hi y),integral_upperIndicator x hx,
      integral_upperIndicator y hy,abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · have hyx : y≤x:=(lt_of_not_ge hxy).le
    have he : (fun t : ℝ=>|(if x≤t then (1:ℝ) else 0)-(if y≤t then (1:ℝ) else 0)|)=
        (fun t=>(if y≤t then (1:ℝ) else 0)-(if x≤t then (1:ℝ) else 0)) := by
      funext t
      rw [abs_sub_comm]
      apply abs_of_nonneg
      split_ifs with hyt hxt hxt <;>norm_num at *
      linarith
    rw [he,intervalIntegral.integral_sub (hi y) (hi x),integral_upperIndicator y hy,
      integral_upperIndicator x hx,abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

theorem parisiCDFDistance_le_coupling (μ ν : Paper.ParisiMeasure)
    (P : Measure (Paper.Overlap×Paper.Overlap)) [IsProbabilityMeasure P]
    (hfst : P.map Prod.fst=(μ:Measure Paper.Overlap))
    (hsnd : P.map Prod.snd=(ν:Measure Paper.Overlap)) :
    parisiCDFDistance μ ν≤∫p,|(p.1:ℝ)-(p.2:ℝ)|∂P := by
  let F : ℝ×(Paper.Overlap×Paper.Overlap)→ℝ:=fun p=>
    (if (p.2.1:ℝ)≤p.1 then 1 else 0)-(if (p.2.2:ℝ)≤p.1 then 1 else 0)
  have hm : Measurable F := by
    exact (measurable_const.ite (measurableSet_le
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)) measurable_fst) measurable_const).sub
      (measurable_const.ite (measurableSet_le
        (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)) measurable_fst) measurable_const)
  have hb : ∀p,‖F p‖≤2 := by
    intro p
    dsimp only [F]
    split_ifs <;>norm_num
  have hi : Integrable F ((volume.restrict (Ioc (0:ℝ) 1)).prod P):=
    (integrable_const (2:ℝ)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hc (t : ℝ) : parisiCDF μ t-parisiCDF ν t=∫p,F (t,p)∂P := by
    rw [parisiCDF_eq_integral_upperIndicator μ t,parisiCDF_eq_integral_upperIndicator ν t,
      ←hfst,←hsnd,integral_map measurable_fst.aemeasurable,
      integral_map measurable_snd.aemeasurable]
    · have hix : Integrable (fun p : Paper.Overlap×Paper.Overlap=>if (p.1:ℝ)≤t then (1:ℝ) else 0) P:=
        (integrable_const (1:ℝ)).mono' ((measurable_const.ite (measurableSet_le
          (measurable_subtype_coe.comp measurable_fst) measurable_const) measurable_const).aestronglyMeasurable)
          (by filter_upwards with p;split_ifs <;>norm_num)
      have hiy : Integrable (fun p : Paper.Overlap×Paper.Overlap=>if (p.2:ℝ)≤t then (1:ℝ) else 0) P:=
        (integrable_const (1:ℝ)).mono' ((measurable_const.ite (measurableSet_le
          (measurable_subtype_coe.comp measurable_snd) measurable_const) measurable_const).aestronglyMeasurable)
          (by filter_upwards with p;split_ifs <;>norm_num)
      exact (integral_sub hix hiy).symm
    all_goals
      exact (measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const)
        measurable_const).aestronglyMeasurable
  unfold parisiCDFDistance
  rw [intervalIntegral.integral_of_le (zero_le_one: (0:ℝ)≤1)]
  calc
    _≤∫t in Ioc (0:ℝ) 1,∫p,|F (t,p)|∂P := by
      apply integral_mono_ae (parisiCDF_abs_diff_intervalIntegrable μ ν 0 1).1 hi.norm.integral_prod_left
      filter_upwards with t
      rw [hc,←Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _=∫p,(∫t in Ioc (0:ℝ) 1,|F (t,p)|)∂P:=integral_integral_swap hi.norm
    _=_:=by
      apply integral_congr_ae
      filter_upwards with p
      rw [←intervalIntegral.integral_of_le (zero_le_one: (0:ℝ)≤1)]
      exact integral_abs_upperIndicator_sub _ _ p.1.property p.2.property

end FourPapersCommon
