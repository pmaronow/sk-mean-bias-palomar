module
public import QuantitativeFollowup.ParisiFreeQuantile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Actual inverse-CDF integral bounds for a positive prescribed root
mass. These deterministic estimates are used by the posterior and
overlap estimates, independently of any claimed variance bound. -/
noncomputable section
open MeasureTheory Set Paper QuantitativePaper
namespace QuantitativeFollowup

theorem integral_inverse_shift (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) :
    (∫ v in Ioc (0:ℝ) (1-s), 1/(s+v)) = -Real.log s := by
  have hm : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hn (v : ℝ) (hv : v∈Icc (0:ℝ) (1-s)) : s+v≠0 := ne_of_gt (by linarith [hs.1,hv.1])
  have hc : ContinuousOn (fun v : ℝ => 1/(s+v)) (Icc 0 (1-s)) := by
    fun_prop (disch := intro v hv; exact hn v hv)
  have hi : IntervalIntegrable (fun v : ℝ => 1/(s+v)) volume 0 (1-s) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hm] using hc)
  have hd (v : ℝ) (hv : v∈uIcc (0:ℝ) (1-s)) :
      HasDerivAt (fun v : ℝ => Real.log (s+v)) (1/(s+v)) v := by
    have hv' : v∈Icc (0:ℝ) (1-s) := by simpa only [uIcc_of_le hm] using hv
    simpa only [id_eq] using ((hasDerivAt_id v).const_add s).log (hn v hv')
  rw [←intervalIntegral.integral_of_le hm,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

theorem integral_inverse_square_shift (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) :
    (∫ v in Ioc (0:ℝ) (1-s), 1/(s+v)^2)=s⁻¹-1 := by
  have hm : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hn (v : ℝ) (hv : v∈Icc (0:ℝ) (1-s)) : s+v≠0 := ne_of_gt (by linarith [hs.1,hv.1])
  have hc : ContinuousOn (fun v : ℝ => 1/(s+v)^2) (Icc 0 (1-s)) := by
    fun_prop (disch := intro v hv; exact pow_ne_zero 2 (hn v hv))
  have hi : IntervalIntegrable (fun v : ℝ => 1/(s+v)^2) volume 0 (1-s) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hm] using hc)
  have hd (v : ℝ) (hv : v∈uIcc (0:ℝ) (1-s)) :
      HasDerivAt (fun v : ℝ => -(s+v)⁻¹) (1/(s+v)^2) v := by
    have hv' : v∈Icc (0:ℝ) (1-s) := by simpa only [uIcc_of_le hm] using hv
    convert (((hasDerivAt_id v).const_add s).inv (hn v hv')).neg using 1
    · rfl
    · simp only [id_eq]
      ring
  rw [←intervalIntegral.integral_of_le hm]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [sub_eq_add_neg,add_comm]

theorem integral_parisiFree_inverse (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) :
    (∫ q, 1/parisiCDF μ (q:ℝ) ∂parisiFreeMeasure μ s) ≤ -Real.log s := by
  have hs' : s∈Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hf : Measurable (fun q : Paper.Overlap => 1/parisiCDF μ (q:ℝ)) :=
    measurable_const.div ((parisiCDF_measurable μ).comp measurable_subtype_coe)
  have hb (q : Paper.Overlap) : |1/parisiCDF μ (q:ℝ)| ≤ 1/s := by
    have hc := scalarFloor_cdf_lower hμ q.property.1
    rw [abs_of_pos (one_div_pos.mpr (hs.1.trans_le hc))]
    exact one_div_le_one_div_of_le hs.1 hc
  have hi : Integrable (fun q : Paper.Overlap => 1/parisiCDF μ (q:ℝ))
      (parisiFreeMeasure μ s) := by
    apply Integrable.mono' (integrable_const (1/s)) hf.aestronglyMeasurable
    exact .of_forall (fun q => by simpa only [Real.norm_eq_abs] using hb q)
  rw [integral_parisiFreeMeasure μ s _ hf]
  have hi' : Integrable (fun v => 1/parisiCDF μ (parisiFreeQuantile μ s v:ℝ))
      (volume.restrict (Ioc (0:ℝ) (1-s))) := by
    rw [←parisiFreeQuantile_map μ s] at hi
    exact (integrable_map_measure hf.aestronglyMeasurable
      (parisiFreeQuantile_measurable μ s).aemeasurable).mp hi
  have hn (v : ℝ) (hv : v∈Icc (0:ℝ) (1-s)) : s+v≠0 := ne_of_gt (by linarith [hs.1,hv.1])
  have hc : ContinuousOn (fun v : ℝ => 1/(s+v)) (Icc 0 (1-s)) := by
    fun_prop (disch := intro v hv; exact hn v hv)
  have hj : IntegrableOn (fun v : ℝ => 1/(s+v)) (Ioc 0 (1-s)) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc
    _ ≤ ∫ v in Ioc (0:ℝ) (1-s),1/(s+v) := by
      apply integral_mono_ae hi' hj
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact one_div_le_one_div_of_le (by linarith [hs.1,hv.1])
        (parisiCDF_freeQuantile_lower μ s hs' hv)
    _ = -Real.log s := integral_inverse_shift s hs

theorem integral_parisiFree_inverse_square (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) :
    (∫ q, 1/(parisiCDF μ (q:ℝ))^2 ∂parisiFreeMeasure μ s) ≤ s⁻¹-1 := by
  have hs' : s∈Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hf : Measurable (fun q : Paper.Overlap => 1/(parisiCDF μ (q:ℝ))^2) := by
    exact measurable_const.div (((parisiCDF_measurable μ).comp measurable_subtype_coe).pow_const 2)
  have hb (q : Paper.Overlap) : |1/(parisiCDF μ (q:ℝ))^2| ≤ 1/s^2 := by
    have hc := scalarFloor_cdf_lower hμ q.property.1
    have hsp : 0<s^2 := sq_pos_of_pos hs.1
    rw [abs_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le hsp
    nlinarith [hs.1,sq_nonneg (parisiCDF μ (q:ℝ)-s)]
  have hi : Integrable (fun q : Paper.Overlap => 1/(parisiCDF μ (q:ℝ))^2)
      (parisiFreeMeasure μ s) := by
    apply Integrable.mono' (integrable_const (1/s^2)) hf.aestronglyMeasurable
    exact .of_forall (fun q => by simpa only [Real.norm_eq_abs] using hb q)
  rw [integral_parisiFreeMeasure μ s _ hf]
  have hi' : Integrable (fun v => 1/(parisiCDF μ (parisiFreeQuantile μ s v:ℝ))^2)
      (volume.restrict (Ioc (0:ℝ) (1-s))) := by
    rw [←parisiFreeQuantile_map μ s] at hi
    exact (integrable_map_measure hf.aestronglyMeasurable
      (parisiFreeQuantile_measurable μ s).aemeasurable).mp hi
  have hn (v : ℝ) (hv : v∈Icc (0:ℝ) (1-s)) : s+v≠0 := ne_of_gt (by linarith [hs.1,hv.1])
  have hc : ContinuousOn (fun v : ℝ => 1/(s+v)^2) (Icc 0 (1-s)) := by
    fun_prop (disch := intro v hv; exact pow_ne_zero 2 (hn v hv))
  have hj : IntegrableOn (fun v : ℝ => 1/(s+v)^2) (Ioc 0 (1-s)) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc
    _ ≤ ∫ v in Ioc (0:ℝ) (1-s),1/(s+v)^2 := by
      apply integral_mono_ae hi' hj
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hq := parisiCDF_freeQuantile_lower μ s hs' hv
      have hp : 0<s+v := by linarith [hs.1,hv.1]
      apply one_div_le_one_div_of_le (sq_pos_of_pos hp)
      nlinarith [sq_nonneg (parisiCDF μ (parisiFreeQuantile μ s v:ℝ)-(s+v))]
    _ = s⁻¹-1 := integral_inverse_square_shift s hs

theorem integral_parisiFree_inverse_square_le_inv (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) :
    (∫ q, 1/(parisiCDF μ (q:ℝ))^2 ∂parisiFreeMeasure μ s) ≤ s⁻¹ :=
  (integral_parisiFree_inverse_square μ s hs hμ).trans (by linarith)

end QuantitativeFollowup
