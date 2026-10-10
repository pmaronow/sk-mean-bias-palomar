module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-! A genuine positive exponential moment bound from an actual upper tail
bound. The weighted layer-cake integral retains the probability measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem exponential_primitive_interval (a x : ℝ) :
    (∫v in (0:ℝ)..x,a*Real.exp (a*v))=Real.exp (a*x)-1 := by
  have hd (v : ℝ) : HasDerivAt (fun y : ℝ=>Real.exp (a*y)) (a*Real.exp (a*v)) v:=by
    simpa only [id_eq,mul_comm,mul_one] using ((hasDerivAt_id v).const_mul a).exp
  have hc : Continuous (fun v : ℝ=>a*Real.exp (a*v)):=by fun_prop
  simpa only [mul_zero,Real.exp_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _=>hd v) (hc.intervalIntegrable 0 x)

theorem upper_tail_positive_exponential_integral (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYm : Measurable Y) (hY : ∀w,0 ≤ Y w)
    (d a : ℝ) (ha : 0<a) (had : a<d)
    (hI : Integrable (fun w=>Real.exp (a*Y w)) P)
    (hTail : ∀u : ℝ,0<u → P.real {w | u ≤ Y w} ≤ 3*Real.exp (-d*u)) :
    (∫w,Real.exp (a*Y w) ∂P) ≤ 1+3*a/(d-a) := by
  let g : ℝ → ℝ:=fun v=>a*Real.exp (a*v)
  have hgCont : Continuous g:=(Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul a
  have hLayer:=lintegral_comp_eq_lintegral_meas_le_mul P
    (.of_forall hY) hYm.aemeasurable (fun t _=>hgCont.intervalIntegrable 0 t)
    (.of_forall fun _=>by dsimp only [g];positivity)
  simp_rw [show ∀w,(∫v in (0:ℝ)..Y w,g v)=Real.exp (a*Y w)-1 from
    fun w=>exponential_primitive_interval a (Y w)] at hLayer
  have hL : (∫⁻w,ENNReal.ofReal (Real.exp (a*Y w)-1) ∂P) ≤
      ∫⁻u in Ioi (0:ℝ),ENNReal.ofReal (3*a*Real.exp ((a-d)*u)) := by
    rw [hLayer]
    apply setLIntegral_mono' measurableSet_Ioi
    intro u hu
    have hT:=ENNReal.ofReal_le_ofReal (hTail u hu)
    rw [ofReal_measureReal] at hT
    apply (mul_le_mul hT le_rfl zero_le zero_le).trans_eq
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp only [g]
    calc
      _=(3*a)*(Real.exp (-d*u)*Real.exp (a*u)):=by ring
      _=_:=by rw [←Real.exp_add];congr 2 <;> ring
  have hNonneg : ∀w,0 ≤ Real.exp (a*Y w)-1:=fun w=>by
    have hh:=Real.one_le_exp_iff.mpr (mul_nonneg ha.le (hY w))
    linarith
  have hMajorInt : IntegrableOn (fun u : ℝ=>3*a*Real.exp ((a-d)*u)) (Ioi 0):=
    (integrableOn_exp_mul_Ioi (by linarith : a-d<0) 0).const_mul (3*a)
  have hSubInt : Integrable (fun w=>Real.exp (a*Y w)-1) P:=hI.sub (integrable_const 1)
  rw [←ofReal_integral_eq_lintegral_ofReal hSubInt (.of_forall hNonneg),
    ←ofReal_integral_eq_lintegral_ofReal hMajorInt (.of_forall fun u=>by positivity)] at hL
  have he : (∫u in Ioi (0:ℝ),3*a*Real.exp ((a-d)*u))=3*a/(d-a):=by
    rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : a-d<0) 0]
    norm_num only [mul_zero,Real.exp_zero]
    field_simp [ne_of_gt (sub_pos.mpr had),ne_of_lt (sub_neg.mpr had)]
    <;> ring
  rw [he,integral_sub hI (integrable_const 1),integral_const] at hL
  norm_num only [probReal_univ,smul_eq_mul,one_mul] at hL
  have hb:=ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 3*a/(d-a)) |>.mp hL
  linarith

end FourPapersCommon
