module
public import QuantitativeFollowup.FollowupCavityParameters
public import QuantitativeFollowup.StandardSKOffDiagonalState

@[expose] public section

/-! At u=1 every physical incident coupling equals the rest coupling.
The resulting model is the genuine zero-diagonal SK interpolation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 300000

theorem followupCavitySpinModel_one_eq_offDiagonal (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩ =
      standardSKOffDiagonalModel (n+1) β (1-ρ) hβ.ne' (by linarith [hρ.1]) := by
  have hv : (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).variance =
      (standardSKOffDiagonalModel (n+1) β (1-ρ) hβ.ne' (by linarith [hρ.1])).variance := by
    funext i
    simp only [followupCavitySpinModel,followupCavityB_one,followupCavityC,
      standardSKOffDiagonalModel]
    split_ifs <;> ring
  have hc : (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).coupling =
      (standardSKOffDiagonalModel (n+1) β (1-ρ) hβ.ne' (by linarith [hρ.1])).coupling := by
    funext e
    by_cases he : e.1.1=e.1.2
    · simp [followupCavitySpinModel,standardSKOffDiagonalModel,he]
    · rw [followupCavitySpinModel_coupling_one n hn β ρ hβ hρ e he]
      simp only [standardSKOffDiagonalModel,he,ite_false,followupCavityRestCoupling,
        Nat.cast_add,Nat.cast_one]
  cases hD : followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩
  cases hE : standardSKOffDiagonalModel (n+1) β (1-ρ) hβ.ne' (by linarith [hρ.1])
  simp only [hD,hE] at hv hc
  cases hv
  cases hc
  rfl

end QuantitativeFollowup
