module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The literal finite inverse-square integral behind the quantile trace cutoff. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 900000

theorem shifted_inverse_square_interval_integral (M s a b : ℝ) (hM : 0<M)
    (hab : a≤b) (ha : 0<s+a) :
    IntervalIntegrable (fun v=>1/(M*(s+v)^2)) volume a b ∧
      (∫v in a..b,1/(M*(s+v)^2))=1/(M*(s+a))-1/(M*(s+b)) := by
  have hp (v : ℝ) (hv : v∈Icc a b) : 0<s+v:=by linarith [hv.1]
  have hc : ContinuousOn (fun v=>1/(M*(s+v)^2)) (Icc a b):=by
    apply continuousOn_const.div (continuous_const.mul ((continuous_const.add continuous_id).pow 2)).continuousOn
    intro v hv
    exact mul_ne_zero hM.ne' (sq_pos_of_pos (hp v hv)).ne'
  have hi : IntervalIntegrable (fun v=>1/(M*(s+v)^2)) volume a b:=by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  let f : ℝ→ℝ:=fun v=>(-1/M)*(s+v)⁻¹
  have hf : ContinuousOn f (Icc a b):=by
    apply continuousOn_const.mul
    exact (continuous_const.add continuous_id).continuousOn.inv₀ (fun v hv=>(hp v hv).ne')
  have hd (v : ℝ) (hv : v∈Ioo a b) : HasDerivAt f (1/(M*(s+v)^2)) v:=by
    have hbase:=((hasDerivAt_const v s).add (hasDerivAt_id v)).inv (hp v (Ioo_subset_Icc_self hv)).ne'
    convert hbase.const_mul (-1/M) using 1
    · rfl
    · dsimp only [Pi.add_apply,id_eq]
      field_simp <;> ring
  refine ⟨hi,?_⟩
  have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf hd hi
  rw [he]
  dsimp only [f]
  field_simp
  ring

end FourPapersCommon
