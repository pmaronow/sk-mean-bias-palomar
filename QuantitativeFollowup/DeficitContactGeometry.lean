module
public import QuantitativeFollowup.TransportDeficitTaylor
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Paper.JTVariational

@[expose] public section

/-! Continuous deficit geometry, including the two physical endpoints.
No differentiability of the mean overlap is needed for fixed-point contact
or for exclusion of the upper endpoint. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

theorem hasDerivAt_transportDeficit (S : ℝ→ℝ) (hS : Continuous S) (q : ℝ) :
    HasDerivAt (transportDeficit S) (q-S q) q := by
  have h:=hS.sub continuous_id
  change HasDerivAt (fun q=>∫p in q..1,S p-p) (q-S q) q
  convert intervalIntegral.integral_hasDerivAt_left (h.intervalIntegrable q 1)
    h.stronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt using 1 <;>
    first | rfl | (simp only [Pi.sub_apply,id_eq];ring)

theorem right_endpoint_minimum_derivative_nonneg (f : ℝ→ℝ) (d : ℝ)
    (hd : HasDerivAt f d 0) (hmin : ∀r∈Icc (0:ℝ) 1,f 0≤f r) : 0≤d := by
  have hslope:=(hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0:ℝ)∉Ioi (0:ℝ))).mp
    (hd.hasDerivWithinAt (s:=Ioi (0:ℝ)))
  apply ge_of_tendsto hslope
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r hr hr1
  rw [slope_def_field,sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hmin r ⟨hr.le,hr1.le⟩)) hr.le

theorem transportDeficit_argmin_contact (S : ℝ→ℝ) (hS : Continuous S)
    (hS0 : 0≤S 0) (hS1 : S 1<1) (q : Paper.Overlap)
    (hq : q∈Paper.overlapArgmin (fun q : Paper.Overlap=>transportDeficit S q)) :
    (q:ℝ)<1 ∧ S q=q := by
  have hmin : ∀r∈Icc (0:ℝ) 1,transportDeficit S q≤transportDeficit S r :=
    fun r hr=>hq ⟨r,hr⟩
  have hq1 : (q:ℝ)<1 := by
    by_contra hn
    have he : (q:ℝ)=1:=le_antisymm q.property.2 (le_of_not_gt hn)
    have hd : HasDerivAt (fun r=>transportDeficit S (1-r)) (S 1-1) 0 := by
      have hg : HasDerivAt (fun r:ℝ=>1-r) (-1) 0 := by
        convert! (hasDerivAt_const 0 (1:ℝ)).sub (hasDerivAt_id 0) using 1 <;>
          simp only [sub_zero,zero_sub,Pi.sub_apply,id_eq]
      have hf : HasDerivAt (transportDeficit S) (1-S 1) ((fun r:ℝ=>1-r) 0) := by
        simpa only [sub_zero] using hasDerivAt_transportDeficit S hS 1
      convert! hf.comp 0 hg using 1 <;> first | rfl | ring
    have hh:=right_endpoint_minimum_derivative_nonneg _ _ hd (fun r hr=>by
      simpa only [sub_zero,he] using hmin (1-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩)
    linarith
  refine ⟨hq1,?_⟩
  by_cases hq0 : (q:ℝ)=0
  · have hd:=hasDerivAt_transportDeficit S hS 0
    have hh:=right_endpoint_minimum_derivative_nonneg _ _ hd (fun r hr=>by
      simpa only [hq0] using hmin r hr)
    rw [hq0]
    linarith
  · have hqpos : 0<(q:ℝ):=lt_of_le_of_ne q.property.1 (Ne.symm hq0)
    have hlocal : IsLocalMin (transportDeficit S) (q:ℝ):=
      (show IsMinOn (transportDeficit S) (Icc (0:ℝ) 1) (q:ℝ) from hmin).isLocalMin
        (Icc_mem_nhds hqpos hq1)
    have hz:=hlocal.hasDerivAt_eq_zero (hasDerivAt_transportDeficit S hS q)
    linarith

end QuantitativeFollowup
