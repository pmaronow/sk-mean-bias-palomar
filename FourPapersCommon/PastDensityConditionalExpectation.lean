module
public import FourPapersCommon.ConditionalKernelWeight
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! A density measurable in the conditioning past does not alter conditional
expectations. The proof transports the actual set-integral characterization
of conditional expectation; no Bayes formula is postulated. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
set_option maxHeartbeats 1000000

theorem condExp_withDensity_of_pastWeight (m : MeasurableSpace Ω) (hm : m≤mΩ)
    (w f : Ω→ℝ) (hw : StronglyMeasurable[m] w) (hwn : ∀x,0≤w x)
    (hf : Integrable f P) (hwf : Integrable (w*f) P)
    [IsFiniteMeasure (P.withDensity (fun x=>ENNReal.ofReal (w x)))] :
    (P.withDensity (fun x=>ENNReal.ofReal (w x)))[f|m]
      =ᵐ[P.withDensity (fun x=>ENNReal.ofReal (w x))] P[f|m] := by
  letI : MeasurableSpace Ω:=mΩ
  let Q:=P.withDensity (fun x=>ENNReal.ofReal (w x))
  have hwm : Measurable w:=(hw.mono hm).measurable
  have hd : Measurable (fun x=>ENNReal.ofReal (w x)):=hwm.ennreal_ofReal
  have htop : ∀ᵐx∂P,ENNReal.ofReal (w x)<⊤:=.of_forall fun _=>ENNReal.ofReal_lt_top
  have hreal (g : Ω→ℝ) : (fun x=>(ENNReal.ofReal (w x)).toReal • g x)=w*g := by
    funext x
    simp only [ENNReal.toReal_ofReal (hwn x),smul_eq_mul,Pi.mul_apply]
  have hiF : Integrable f Q := by
    apply (integrable_withDensity_iff_integrable_smul' hd htop).mpr
    simpa only [hreal] using hwf
  have he:=condExp_mul_of_stronglyMeasurable_left hw hwf hf
  have hiCE : Integrable (w*P[f|m]) P:=integrable_condExp.congr he
  have hiQCE : Integrable (P[f|m]) Q := by
    apply (integrable_withDensity_iff_integrable_smul' hd htop).mpr
    simpa only [hreal] using hiCE
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hiF
  · intro A _ _
    exact hiQCE.integrableOn
  · intro A hA _
    have hAg : MeasurableSet A:=hm A hA
    have hL : (∫x in A,P[f|m] x∂Q)=∫x in A,(w*P[f|m]) x∂P := by
      dsimp only [Q]
      rw [restrict_withDensity hAg,
        integral_withDensity_eq_integral_toReal_smul hd
          (.of_forall fun _=>ENNReal.ofReal_lt_top),hreal]
    have hR : (∫x in A,f x∂Q)=∫x in A,(w*f) x∂P := by
      dsimp only [Q]
      rw [restrict_withDensity hAg,
        integral_withDensity_eq_integral_toReal_smul hd
          (.of_forall fun _=>ENNReal.ofReal_lt_top),hreal]
    rw [hL,hR]
    calc
      _=∫x in A,P[w*f|m] x∂P :=
        setIntegral_congr_ae hAg (he.symm.mono fun _ hx _=>hx)
      _=_ := setIntegral_condExp hm hwf hA
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

end FourPapersCommon
