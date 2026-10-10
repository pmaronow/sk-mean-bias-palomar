module
public import QuantitativeFollowup.SmallIntervalNormalization

@[expose] public section

/-! Logarithmic and thermal absorption for the stable cavity interval.
The native contraction is a separate input to these scalar reducers. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

def followupCavityStableLogConstant (C : ℝ) : ℝ := 1+2*Real.log (8*C)

def followupCavityStableDefectConstant (β C : ℝ) : ℝ :=
  2*C*(2*β^2+457*(smallIntervalLogConstant β)^2+
    425*smallIntervalLogConstant β*followupCavityStableLogConstant C)+
      913*(smallIntervalLogConstant β)^2

theorem followupCavityStableLogConstant_pos (C : ℝ) (hC : 1 ≤ C) :
    0 < followupCavityStableLogConstant C := by
  have h := Real.log_nonneg (show 1 ≤ 8*C by linarith)
  unfold followupCavityStableLogConstant
  linarith

theorem followupCavityStableDefectConstant_pos (β C : ℝ)
    (hβ : 1 < β) (hC : 1 ≤ C) :
    0 < followupCavityStableDefectConstant β C := by
  have hL := smallIntervalLogConstant_pos β hβ
  have hK := followupCavityStableLogConstant_pos C hC
  unfold followupCavityStableDefectConstant
  positivity

theorem followupCavityStable_log_reciprocal (N C rho : ℝ)
    (hN : 2 ≤ N) (hC : 1 ≤ C) (hr : 0 < rho) (hNr : N⁻¹ ≤ rho) :
    Real.log (2/((1/(4*C))*rho)) ≤
      followupCavityStableLogConstant C*Real.log (2+N) := by
  have hNp : 0 < N := by linarith
  have hCp : 0 < C := by linarith
  have hprod : 1 ≤ N*rho := by
    have hh : 1 ≤ rho*N := (div_le_iff₀ hNp).mp (by simpa only [one_div] using hNr)
    simpa only [mul_comm] using hh
  have harg : 2/((1/(4*C))*rho)=(8*C)/rho := by field_simp;ring
  rw [harg]
  have hratio : (8*C)/rho ≤ (8*C)*N := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 8*C)]
  have hl := Real.log_le_log (div_pos (by positivity : 0 < 8*C) hr) hratio
  rw [Real.log_mul (by positivity : (8*C)≠0) hNp.ne'] at hl
  have hNlog := Real.log_le_log hNp (by linarith : N ≤ 2+N)
  have htwo := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ) ≤ 2+N)
  have hhalf : (1/2:ℝ) ≤ Real.log (2+N) :=
    (lt_trans (by norm_num) Real.log_two_gt_d9).le.trans htwo
  have hKlog : 0 ≤ Real.log (8*C) := Real.log_nonneg (by linarith)
  have hm := mul_nonneg hKlog (by linarith : 0 ≤ 2*Real.log (2+N)-1)
  unfold followupCavityStableLogConstant
  nlinarith

theorem followupCavityStable_thermal_absorption
    (β C rho V A J H E0 E1 : ℝ) (hβ : 0 < β) (hC : 1 ≤ C) (hr : 0 < rho)
    (hbase : (3*rho/4)*V ≤ C*(β⁻¹*E0+A+J+H))
    (hthird : H ≤ (1/(4*C))*rho*V+β⁻¹*E1) :
    rho*(β*V) ≤ 2*C*(E0+β*A+β*J+E1) := by
  have hCp : 0 < C := by linarith
  have hs : β*C*H ≤ (rho/4)*(β*V)+C*E1 := by
    calc
      _ ≤ β*C*((1/(4*C))*rho*V+β⁻¹*E1) :=
        mul_le_mul_of_nonneg_left hthird (mul_nonneg hβ.le hCp.le)
      _ = _ := by field_simp [hβ.ne',hCp.ne'] <;> ring
  have hb : (3*rho/4)*(β*V) ≤ C*E0+C*(β*A)+C*(β*J)+β*C*H := by
    have hh := mul_le_mul_of_nonneg_left hbase hβ.le
    convert hh using 1 <;> field_simp [hβ.ne'] <;> ring
  nlinarith only [hb,hs]

end QuantitativeFollowup
