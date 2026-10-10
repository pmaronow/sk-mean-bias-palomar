module
public import QuantitativeFollowup.NativeCenteredFreeEnergy
public import QuantitativeFollowup.Targets
public import QuantitativePaper.UniformEnergyVarianceLower

@[expose] public section

/-! Literal negative fractional-pressure comparison follows from actual
Chen variance control, true mean centering and native Parisi nonnegativity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem native_negative_fractional_gap_bounds (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (s : ℝ) (hs : s<0) :
    0≤parisiLimit β-cgf (logPartition n β) (couplingLaw n) s/((n:ℝ)*s) ∧
    parisiLimit β-cgf (logPartition n β) (couplingLaw n) s/((n:ℝ)*s)≤
      finiteBias n β+|s|/(2*(n:ℝ))*freeEnergyVariance n β := by
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn
  have hDen : 0 < -(n:ℝ)*s:=mul_pos_of_neg_of_neg (neg_neg_of_pos hNp) hs
  have he : parisiLimit β-cgf (logPartition n β) (couplingLaw n) s/((n:ℝ)*s)=
      finiteBias n β+centeredFreeEnergyCGF n β s/(-(n:ℝ)*s):=by
    rw [centeredFreeEnergyCGF_eq_cgf_sub_mean]
    unfold finiteBias pressure
    field_simp [hNp.ne',hs.ne]
    <;> ring
  have hBias : 0≤finiteBias n β:=by
    unfold finiteBias parisiLimit
    exact (uniform_quantitative_parisi_pressure n hn β hβ).1
  have hNonneg:=centeredFreeEnergyCGF_nonneg n β s hβ.ne'
  have hBound:=native_centered_free_energy_cgf_negative_variance_bound n β hβ s hs
  have hQuot:=div_le_div_of_nonneg_right hBound hDen.le
  have hScale : (s^2/2*freeEnergyVariance n β)/(-(n:ℝ)*s)=
      |s|/(2*(n:ℝ))*freeEnergyVariance n β:=by
    rw [abs_of_neg hs]
    field_simp [hNp.ne',hs.ne]
    <;> ring
  rw [hScale] at hQuot
  rw [he]
  exact ⟨add_nonneg hBias (div_nonneg hNonneg hDen.le),by linarith only [hQuot]⟩

end QuantitativeFollowup
