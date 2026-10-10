module
public import QuantitativeFollowup.FollowupCavityContractionTrace

@[expose] public section

/-! The sharp source contraction margin and its exact scalar absorption.
The trace identity is a separate mathematical input to the algebraic reducer;
this leaf alone does not assert the native covariance derivative identity. -/
noncomputable section
open Set
namespace QuantitativeFollowup

theorem followupCavity_effective_response_gap_three_quarters (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) (ρ/4)) :
    followupCavityAlpha n β ρ / followupCavityD n β ρ * (1+ε) ≤ 1-3*ρ/4 := by
  have h := followupCavityAlpha_div_D_mem_contraction_interval hn β ρ hβ hρ
  calc
    _ ≤ (1-ρ)*(1+ε) := mul_le_mul_of_nonneg_right h.2 (by linarith [hε.1])
    _ ≤ (1-ρ)*(1+ρ/4) := mul_le_mul_of_nonneg_left (by linarith [hε.2])
      (by linarith [hρ.2])
    _ ≤ _ := by nlinarith [sq_nonneg ρ]

theorem cavityContraction_scalar_absorption (V Vminus θ C E δ η : ℝ)
    (hV : 0 ≤ V) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hδ : 0 ≤ δ)
    (hrest : Vminus ≤ V+C*E+δ)
    (hfull : V ≤ η+θ*Vminus+C*E) :
    (1-θ)*V ≤ η+2*C*E+δ := by
  have h := mul_le_mul_of_nonneg_left hrest hθ
  have hce := mul_nonneg hC hE
  have hsmall := mul_le_mul_of_nonneg_right hθ1 (add_nonneg hce hδ)
  nlinarith

theorem cavityContraction_three_quarters_absorption (V Vminus θ C E δ η ρ : ℝ)
    (hV : 0 ≤ V) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (hθρ : θ ≤ 1-3*ρ/4)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hrest : Vminus ≤ V+C*E+δ)
    (hfull : V ≤ η+θ*Vminus+C*E) :
    (3*ρ/4)*V ≤ η+2*C*E+δ := by
  have h := cavityContraction_scalar_absorption V Vminus θ C E δ η hV hθ
    (by linarith) hC hE hδ hrest hfull
  exact (mul_le_mul_of_nonneg_right (by linarith : 3*ρ/4 ≤ 1-θ) hV).trans h

theorem cavityContraction_absorb_third_moment (V A J H error ρ C κ : ℝ)
    (hV : 0 ≤ V) (hρ : 0 ≤ ρ) (hC : 0 ≤ C)
    (hκ : C*κ ≤ 1/4)
    (hbase : (3*ρ/4)*V ≤ C*(error+A+J+H))
    (hthird : H ≤ κ*ρ*V+error) :
    ρ*V ≤ 2*C*(2*error+A+J) := by
  have hb := mul_le_mul_of_nonneg_left hthird hC
  have hs := mul_le_mul_of_nonneg_right hκ (mul_nonneg hρ hV)
  nlinarith

end QuantitativeFollowup
