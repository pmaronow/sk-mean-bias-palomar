module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowCentering
public import QuantitativeFollowup.FollowupCavityNodeBModel

@[expose] public section

/-! The actual independent-endpoint covariance vanishes, and hence the
centered product has zero integral under the complete outer posterior.
Only the last variance is replaced in deriving this product law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem last_variance_at_base (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    cavityLastVarianceModel n β ρ hβ hρ (D.variance (Fin.last n)) (D.variance_pos (Fin.last n))=D :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  have he:cavityLastVarianceModel n β ρ hβ hρ (D.variance (Fin.last n)) (D.variance_pos (Fin.last n))=
      anisotropicReplaceVariance D (Fin.last n) (D.variance (Fin.last n)):=by
    have hb:=D.variance_pos (Fin.last n)
    unfold cavityLastVarianceModel anisotropicReplaceVariance
    dsimp only [D] at hb ⊢
    simp only [hb,and_true]
  rw [he,anisotropicReplaceVariance_self]

theorem cavityFixedRowCovariance_independent_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    cavityFixedRowCovariance (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) s a d 0=0 :=by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  have hz:=cavityFixedRowCovariance_lastVariance_zero s n β ρ hβ hρ
    (D.variance (Fin.last n)) (D.variance_pos (Fin.last n)) a d hd
  dsimp only at hz
  rw [last_variance_at_base n β ρ hβ hρ] at hz
  exact hz

theorem cavityFixedRowOuterCovariance_independent_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    cavityFixedRowOuterCovariance (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) s a d 0=0 :=by
  have hz:=cavityFixedRowCovariance_independent_zero s n β ρ hβ hρ a d hd
  rw [cavityFixedRowCovariance_eq_outer _ s a d hd] at hz
  simpa only [Function.comp_apply, map_zero] using hz

end QuantitativeFollowup
