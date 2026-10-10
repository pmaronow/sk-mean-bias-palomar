module
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-! Actual minimum envelopes: uniform Lipschitz bounds and derivative contact.
No continuity or differentiability of a selected minimizer is required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 500000

theorem lipschitzOnWith_minimum_envelope {ι : Type*}
    (F : ℝ→ι→ℝ) (f : ℝ→ℝ) (S : Set ι) (T : Set ℝ) (K : NNReal)
    (hle : ∀t∈T,∀i∈S,f t≤F t i)
    (hatt : ∀t∈T,∃i∈S,F t i=f t)
    (hlip : ∀i∈S,LipschitzOnWith K (fun t=>F t i) T) :
    LipschitzOnWith K f T := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  obtain ⟨i,hi,hix⟩:=hatt x hx
  obtain ⟨j,hj,hjy⟩:=hatt y hy
  have hxy : F x j-F y j≤(K : ℝ)*dist x y:=
    (le_abs_self _).trans (by simpa only [Real.dist_eq] using (hlip j hj).dist_le_mul x hx y hy)
  have hyx : F y i-F x i≤(K : ℝ)*dist x y:=
    (le_abs_self _).trans (by simpa only [Real.dist_eq,abs_sub_comm] using (hlip i hi).dist_le_mul y hy x hx)
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hle x hx j hj,hle y hy i hi]

theorem hasDerivAt_minimum_envelope_contact
    (f g : ℝ→ℝ) (T : Set ℝ) (t df dg : ℝ)
    (hT : T∈𝓝 t) (hle : ∀r∈T,f r≤g r) (heq : f t=g t)
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) : df=dg := by
  have hm : IsLocalMin (fun r=>g r-f r) t:=by
    filter_upwards [hT] with r hr
    rw [←heq,sub_self]
    exact sub_nonneg.mpr (hle r hr)
  have hh:=hm.hasDerivAt_eq_zero (hg.sub hf)
  linarith

theorem lipschitz_envelope_endpoint_integral (f : ℝ→ℝ) (a b : ℝ) (K : NNReal)
    (hf : LipschitzOnWith K f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b ∧
      (∀ᵐ t : ℝ,t∈uIcc a b→DifferentiableAt ℝ f t) ∧
      (∫t in a..b,deriv f t)=f b-f a := by
  have hAC:=hf.absolutelyContinuousOnInterval
  exact ⟨hAC.intervalIntegrable_deriv,hAC.ae_differentiableAt,hAC.integral_deriv_eq_sub⟩

end FourPapersCommon
