module
public import FourPapersCommon.MovingCutoffPowers

@[expose] public section

/-! The actual moving cutoff and the three regimes of its sharp rate. -/
noncomputable section
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def movingQuantileCutoff (M s : ℝ) : ℝ:=max s (M^(-(1/2:ℝ)))

theorem moving_cutoff_square_identity (M : ℝ) (hM : 0<M) :
    M*(M^(-(1/2:ℝ)))^2=1 := by
  have he : (M^(-(1/2:ℝ)))^2=M^(-1:ℝ):=by
    rw [←Real.rpow_mul_natCast hM.le]
    norm_num
  rw [he,Real.rpow_neg_one,mul_inv_cancel₀ hM.ne']

theorem moving_cutoff_rate_identity (M : ℝ) (hM : 0<M) :
    M^(-(2/3:ℝ))*(M^(-(1/2:ℝ)))^(-(1/3:ℝ))=M^(-(1/2:ℝ)) := by
  rw [←Real.rpow_mul hM.le,←Real.rpow_add hM]
  norm_num

theorem movingQuantileCutoff_supercritical (M s : ℝ) (hM : 0<M) (hs : 0<s) :
    0<movingQuantileCutoff M s ∧ 1≤M*(movingQuantileCutoff M s)^2 := by
  have ha : 0≤M^(-(1/2:ℝ)):=by positivity
  refine ⟨hs.trans_le (le_max_left _ _),?_⟩
  rw [←moving_cutoff_square_identity M hM]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha (le_max_right _ _) 2) hM.le

theorem movingQuantileCutoff_below_one (M s : ℝ) (hM : 1<M) (hs : s<1) :
    movingQuantileCutoff M s<1:=
  max_lt hs (Real.rpow_lt_one_of_one_lt_of_neg hM (by norm_num))

theorem movingQuantileCutoff_rate_eq_min (M s : ℝ) (hM : 0<M) (hs : 0<s) :
    M^(-(2/3:ℝ))*(movingQuantileCutoff M s)^(-(1/3:ℝ))=
      min (M^(-(1/2:ℝ))) (M^(-(2/3:ℝ))*s^(-(1/3:ℝ))) := by
  let a:=M^(-(1/2:ℝ))
  have ha : 0<a:=by dsimp only [a];positivity
  have hid : M^(-(2/3:ℝ))*a^(-(1/3:ℝ))=a:=moving_cutoff_rate_identity M hM
  unfold movingQuantileCutoff
  by_cases hsa : s≤a
  · rw [max_eq_right hsa,hid,min_eq_left]
    change a≤M^(-(2/3:ℝ))*s^(-(1/3:ℝ))
    rw [←hid]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hs hsa (by norm_num : -(1/3:ℝ)≤0)) (by positivity)
  · have has : a≤s:=(not_le.mp hsa).le
    rw [max_eq_left has,min_eq_right]
    change M^(-(2/3:ℝ))*s^(-(1/3:ℝ))≤a
    rw [←hid]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha has (by norm_num : -(1/3:ℝ)≤0)) (by positivity)

theorem movingQuantileCutoff_initial_length (M s : ℝ) (hM : 0<M) (hs : 0≤s) :
    movingQuantileCutoff M s-s≤M^(-(2/3:ℝ))*(movingQuantileCutoff M s)^(-(1/3:ℝ)) := by
  unfold movingQuantileCutoff
  by_cases hsa : s≤M^(-(1/2:ℝ))
  · rw [max_eq_right hsa,moving_cutoff_rate_identity M hM]
    linarith
  · rw [max_eq_left (not_le.mp hsa).le,sub_self]
    positivity

theorem moving_rate_subcritical (M s : ℝ) (hM : M∈Set.Ioc (0:ℝ) 1)
    (hs : s∈Set.Ioc (0:ℝ) 1) :
    min 1 (min (M^(-(1/2:ℝ))) (M^(-(2/3:ℝ))*s^(-(1/3:ℝ))))=1 := by
  have hA : 1≤M^(-(1/2:ℝ)):=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hM.1 hM.2 (by norm_num)
  have hB : 1≤M^(-(2/3:ℝ)):=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hM.1 hM.2 (by norm_num)
  have hC : 1≤s^(-(1/3:ℝ)):=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs.1 hs.2 (by norm_num)
  exact min_eq_left (le_min hA (by nlinarith))

end FourPapersCommon
