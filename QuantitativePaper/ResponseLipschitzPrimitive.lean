module
public import QuantitativePaper.ResponseLipschitzTest
public import FourPapersCommon.IntegrablePrimitiveLipschitzFTC

@[expose] public section

/-! Genuine Lipschitz tests of an integrable primitive, including the
squared test. Their a.e. derivatives suffice for the endpoint formula. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 500000

theorem response_Lipschitz_tested_interval (F H : ℝ→ℝ) (a b : ℝ) (hab : a≤b)
    (hH : IntervalIntegrable H volume a b)
    (hrep : ∀x∈Icc a b,F x-F a=∫q in a..x,H q) (w : ResponseLipschitzTest) :
    w.value b*F b-w.value a*F a=∫q in a..b,w.slope q*F q+w.value q*H q :=
  lipschitz_weighted_FTC_of_integrable_primitive F H w.value a b hab hH hrep
    w.lipschitzBound w.lipschitz.lipschitzOnWith

theorem response_squared_Lipschitz_tested_interval (F H : ℝ→ℝ) (a b : ℝ) (hab : a≤b)
    (hH : IntervalIntegrable H volume a b)
    (hrep : ∀x∈Icc a b,F x-F a=∫q in a..x,H q) (w : ResponseLipschitzTest) :
    (w.value b)^2*F b-(w.value a)^2*F a=
      ∫q in a..b,2*w.slope q*w.value q*F q+(w.value q)^2*H q :=by
  have hF:=absolutelyContinuousOnInterval_of_integrable_primitive F H a b hab hH hrep
  have hw:=w.absolutelyContinuous a b
  have hw2 : AbsolutelyContinuousOnInterval (fun q=>(w.value q)^2) a b:=by
    simpa only [pow_two] using hw.fun_mul hw
  calc
    _ = ∫q in a..b,deriv (fun q=>(w.value q)^2) q*F q+(w.value q)^2*deriv F q:=
      (hw2.integral_deriv_mul_eq_sub hF).symm
    _ = _ :=by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hw.ae_differentiableAt,
        ae_hasDerivAt_of_integrable_primitive F H a b hab hH hrep,
        volume.ae_ne b] with q hd hFq hqb hq
      have hqu : q∈uIcc a b:=uIoc_subset_uIcc hq
      rw [uIoc_of_le hab] at hq
      have hp : deriv (fun q=>(w.value q)^2) q = 2*(w.value q)*deriv w.value q:=by
        change deriv (w.value^2) q = _
        simpa using ((hd hqu).hasDerivAt.pow 2).deriv
      rw [(hFq ⟨hq.1,lt_of_le_of_ne hq.2 hqb⟩).deriv,hp]
      simp only [ResponseLipschitzTest.slope]
      ring
end QuantitativePaper
