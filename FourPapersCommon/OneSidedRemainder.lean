module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A genuine first-order remainder criterion on a closed probability
mixing interval. The error may vanish slower than linearly. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon

theorem hasDerivWithinAt_Icc_zero_of_error_bound (f : ℝ → ℝ) (d : ℝ) (error : ℝ → ℝ)
    (he : Tendsto error (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0))
    (hn : ∀lam ∈ Icc (0 : ℝ) 1,0 ≤ error lam)
    (hb : ∀lam ∈ Icc (0 : ℝ) 1,‖f lam-f 0-lam*d‖ ≤ lam*error lam) :
    HasDerivWithinAt f d (Icc (0 : ℝ) 1) 0 := by
  rw [hasDerivWithinAt_iff_tendsto]
  simp only [sub_zero,smul_eq_mul]
  apply squeeze_zero'
    (Eventually.of_forall (fun lam => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)))
    _ he
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  by_cases hzero : lam = 0
  · simp only [hzero,norm_zero,inv_zero,zero_mul]
    simpa only [hzero] using hn lam hlam
  · have hh := mul_le_mul_of_nonneg_left (hb lam hlam) (inv_nonneg.mpr (norm_nonneg lam))
    have heq : ‖lam‖⁻¹*(lam*error lam)=error lam := by
      rw [Real.norm_of_nonneg hlam.1]
      field_simp [hzero]
    exact hh.trans_eq heq

end FourPapersCommon
