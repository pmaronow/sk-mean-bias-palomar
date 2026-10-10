module
public import QuantitativeFollowup.FollowupCavityThreeEndpointPhysical
public import QuantitativeFollowup.FollowupCavityThreeNativeComparison

@[expose] public section

/-! Actual positive comparison transfers the deleted-rest three-descendant
thermal budget from the completed SK endpoint to every physical cavity law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_three_deleted_square_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hfloor:a≤Paper.parisiCDF μ 0)
    (q:Paper.Overlap) (u:ℝ) (hu:u∈Icc (0:ℝ) 1) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q)≤
      16*Real.exp (43*β^2)*
        (foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
          foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
          1/((n+1:ℕ):ℝ)^2) := by
  have hc:=cavityThreeDescendant_positive_comparison hn β ρ hβ hρ μ a ha hfloor q
    (fun σ=>(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) σ/(n:ℝ))^2)
    (fun σ=>sq_nonneg _) u 1 hu ⟨zero_le_one,le_rfl⟩
  have he:=followup_cavity_one_deleted_three_square_le hn μ β ρ a hβ hρ q
  exact hc.trans (by
    convert mul_le_mul_of_nonneg_left he (Real.exp_pos (43*β^2)).le using 1 <;> ring)

theorem followup_cavity_three_deleted_half_square_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hfloor:a≤Paper.parisiCDF μ 0)
    (q:Paper.Overlap) (u:ℝ) (hu:u∈Icc (0:ℝ) 1) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q)/2≤
      8*Real.exp (43*β^2)*
        (foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
          foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
          1/((n+1:ℕ):ℝ)^2) := by
  have h:=followup_cavity_three_deleted_square_le hn μ β ρ a hβ hρ ha hfloor q u hu
  linarith

end QuantitativeFollowup
