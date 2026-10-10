module
public import QuantitativeFollowup.UniformNoiseMoments
public import QuantitativeFollowup.ScalarKernelBasics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! A genuine Taylor bound for the integrated deficit of a monotone unit
second moment. The reflected bound includes both physical endpoints,
and the uniform perturbation then gives the exact `h²/6` cost. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def transportDeficit (S : ℝ→ℝ) (q : ℝ) : ℝ := ∫p in q..1,S p-p

theorem continuous_transportDeficit (S : ℝ→ℝ) (hS : Continuous S) :
    Continuous (transportDeficit S) := by
  have hc := (intervalIntegral.continuous_primitive (μ:=volume)
    (fun a b => (hS.sub continuous_id).intervalIntegrable a b) 1).neg
  convert hc using 1
  funext q
  exact intervalIntegral.integral_symm 1 q

theorem monotone_integral_ge_tangent (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1)) (q y : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    S q*(y-q) ≤ ∫p in q..y,S p := by
  by_cases hqy : q≤y
  · have hh:=intervalIntegral.integral_mono_on (μ:=volume) hqy
      (intervalIntegrable_const : IntervalIntegrable (fun _p : ℝ=>S q) volume q y)
      (hS.intervalIntegrable q y) (fun p hp=>hmono hq ⟨hq.1.trans hp.1,hp.2.trans hy.2⟩ hp.1)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh
  · have hyq : y≤q:=le_of_not_ge hqy
    have hh:=intervalIntegral.integral_mono_on (μ:=volume) hyq (hS.intervalIntegrable y q)
      (intervalIntegrable_const : IntervalIntegrable (fun _p : ℝ=>S q) volume y q)
      (fun p hp=>hmono ⟨hy.1.trans hp.1,hp.2.trans hq.2⟩ hq hp.2)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
    have heq : (∫p in q..y,S p)=-(∫p in y..q,S p) := intervalIntegral.integral_symm y q
    rw [heq]
    nlinarith

theorem transportDeficit_taylor (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1)) (q y : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    transportDeficit S y ≤ transportDeficit S q+(q-S q)*(y-q)+(y-q)^2/2 := by
  have ht:=monotone_integral_ge_tangent S hS hmono q y hq hy
  have hi:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((hS.sub continuous_id).intervalIntegrable q y)
    ((hS.sub continuous_id).intervalIntegrable y 1)
  change (∫p in q..y,S p-p)+(∫p in y..1,S p-p)=(∫p in q..1,S p-p) at hi
  rw [intervalIntegral.integral_sub (μ:=volume) (f:=S) (g:=fun p : ℝ=>p) (hS.intervalIntegrable q y)
    (continuous_id.intervalIntegrable q y),integral_id] at hi
  change (∫p in q..y,S p)-(y^2-q^2)/2+transportDeficit S y=transportDeficit S q at hi
  nlinarith

theorem transportDeficit_reflected_taylor (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1))
    (hbound : ∀q∈Icc (0:ℝ) 1,0≤S q ∧ S q≤1) (q u : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (hy : overlapReflection (q+u)∈Icc (0:ℝ) 1) :
    transportDeficit S (overlapReflection (q+u)) ≤
      transportDeficit S q+(q-S q)*u+u^2/2 := by
  have ht:=transportDeficit_taylor S hS hmono q (overlapReflection (q+u)) hq hy
  have hb:=hbound q hq
  unfold overlapReflection at ht ⊢
  split_ifs with hz
  · simp only [ite_eq_left hz] at ht
    by_cases hz0 : 0≤q+u
    · rw [abs_of_nonneg hz0] at ht ⊢
      nlinarith
    · have hneg : q+u<0:=lt_of_not_ge hz0
      rw [abs_of_neg hneg] at ht ⊢
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.1 hneg.le]
  · simp only [ite_eq_right hz] at ht
    have hpos : 0<q+u-1:=by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) hpos.le]

theorem transportDeficit_reflected_uniform_bound (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1))
    (hbound : ∀q∈Icc (0:ℝ) 1,0≤S q ∧ S q≤1)
    (h : ℝ) (hh : h∈Ioc (0:ℝ) (1/2)) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    (∫u,transportDeficit S (overlapReflection (q+u))∂symmetricUniformLaw h)-
      transportDeficit S q≤h^2/6 := by
  exact reflected_uniform_taylor_average_le h hh q hq (transportDeficit S)
    (continuous_transportDeficit S hS) (q-S q)
    (fun u hu=>transportDeficit_reflected_taylor S hS hmono hbound q u hq
      (overlapReflection_mem hq hh hu))

end QuantitativeFollowup
