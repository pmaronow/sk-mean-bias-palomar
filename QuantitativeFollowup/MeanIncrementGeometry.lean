module
public import QuantitativeFollowup.DeficitContactGeometry

@[expose] public section

/-! The factor-two mean-increment bound towards a deficit minimum. The
comparison point is S(r), which need not lie in the support. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem transportDeficit_difference (S : ℝ→ℝ) (hS : Continuous S) (a b : ℝ) :
    transportDeficit S a-transportDeficit S b=∫u in a..b,S u-u := by
  have h:=(hS.sub continuous_id)
  have he:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (h.intervalIntegrable a b)
    (h.intervalIntegrable b 1)
  change (∫u in a..b,S u-u)+transportDeficit S b=transportDeficit S a at he
  linarith

theorem integral_const_sub_id (x a b : ℝ) :
    (∫u in a..b,x-u)=x*(b-a)-(b^2-a^2)/2 := by
  rw [intervalIntegral.integral_sub (μ:=volume) (f:=fun _u:ℝ=>x) (g:=fun u:ℝ=>u) (intervalIntegrable_const :
    IntervalIntegrable (fun _u:ℝ=>x) volume a b) (continuous_id.intervalIntegrable a b),
    intervalIntegral.integral_const,integral_id,smul_eq_mul]
  ring

theorem mean_increment_towards_deficit_minimum (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1))
    (hunit : ∀u∈Icc (0:ℝ) 1,0≤S u ∧ S u≤1)
    (q r : ℝ) (hq : q∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1)
    (hfixed : S q=q)
    (hmin : ∀y∈Icc (0:ℝ) 1,transportDeficit S q≤transportDeficit S y) :
    |S r-S q|≤2*|r-q| := by
  let ξ:=S r
  have hξ : ξ∈Icc (0:ℝ) 1:=hunit r hr
  have hg:Continuous (fun u=>S u-u):=hS.sub continuous_id
  have hcomparison : 0≤transportDeficit S ξ-transportDeficit S q:=
    sub_nonneg.mpr (hmin ξ hξ)
  by_cases hrq : r≤q
  · have hSrq : ξ≤q:=by simpa only [hfixed] using hmono hr hq hrq
    rw [hfixed,abs_of_nonpos (sub_nonpos.mpr hSrq),abs_of_nonpos (sub_nonpos.mpr hrq)]
    by_cases hξr : r≤ξ
    · dsimp only [ξ] at hξr hSrq
      linarith
    · have hξr' : ξ≤r:=le_of_not_ge hξr
      have h1:=intervalIntegral.integral_mono_on (μ:=volume) hξr'
        (hg.intervalIntegrable ξ r) ((continuous_const.sub continuous_id).intervalIntegrable ξ r)
        (fun u hu=>sub_le_sub_right (hmono ⟨hξ.1.trans hu.1,hu.2.trans hr.2⟩ hr hu.2) u)
      change (∫u in ξ..r,S u-u)≤∫u in ξ..r,ξ-u at h1
      rw [integral_const_sub_id] at h1
      have h2:=intervalIntegral.integral_mono_on (μ:=volume) hrq
        (hg.intervalIntegrable r q) ((continuous_const.sub continuous_id).intervalIntegrable r q)
        (fun u hu=>sub_le_sub_right (hmono ⟨hr.1.trans hu.1,hu.2.trans hq.2⟩ hq hu.2) u)
      simp only [hfixed,Pi.sub_apply,id_eq] at h2
      rw [integral_const_sub_id] at h2
      rw [transportDeficit_difference S hS ξ q] at hcomparison
      have he:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hg.intervalIntegrable ξ r)
        (hg.intervalIntegrable r q)
      change (∫u in ξ..r,S u-u)+(∫u in r..q,S u-u)=(∫u in ξ..q,S u-u) at he
      have hsquare : (r-ξ)^2≤(q-r)^2:=by nlinarith
      have hdist : r-ξ≤q-r:=by nlinarith [sub_nonneg.mpr hξr',sub_nonneg.mpr hrq]
      change -(ξ-q)≤2*-(r-q)
      linarith
  · have hqr : q≤r:=le_of_not_ge hrq
    have hSqr : q≤ξ:=by simpa only [hfixed] using hmono hq hr hqr
    rw [hfixed,abs_of_nonneg (sub_nonneg.mpr hSqr),abs_of_nonneg (sub_nonneg.mpr hqr)]
    by_cases hrξ : ξ≤r
    · dsimp only [ξ] at hrξ hSqr
      linarith
    · have hrξ' : r≤ξ:=le_of_not_ge hrξ
      have h1:=intervalIntegral.integral_mono_on (μ:=volume) hqr
        ((continuous_const.sub continuous_id).intervalIntegrable q r) (hg.intervalIntegrable q r)
        (fun u hu=>sub_le_sub_right (hmono hq ⟨hq.1.trans hu.1,hu.2.trans hr.2⟩ hu.1) u)
      simp only [hfixed,Pi.sub_apply,id_eq] at h1
      rw [integral_const_sub_id] at h1
      have h2:=intervalIntegral.integral_mono_on (μ:=volume) hrξ'
        ((continuous_const.sub continuous_id).intervalIntegrable r ξ) (hg.intervalIntegrable r ξ)
        (fun u hu=>sub_le_sub_right (hmono hr ⟨hr.1.trans hu.1,hu.2.trans hξ.2⟩ hu.1) u)
      change (∫u in r..ξ,ξ-u)≤∫u in r..ξ,S u-u at h2
      rw [integral_const_sub_id] at h2
      rw [transportDeficit_difference S hS ξ q,intervalIntegral.integral_symm q ξ] at hcomparison
      have he:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hg.intervalIntegrable q r)
        (hg.intervalIntegrable r ξ)
      change (∫u in q..r,S u-u)+(∫u in r..ξ,S u-u)=(∫u in q..ξ,S u-u) at he
      have hsquare : (ξ-r)^2≤(r-q)^2:=by nlinarith
      have hdist : ξ-r≤r-q:=by nlinarith [sub_nonneg.mpr hrξ',sub_nonneg.mpr hqr]
      change ξ-q≤2*(r-q)
      linarith

end QuantitativeFollowup
