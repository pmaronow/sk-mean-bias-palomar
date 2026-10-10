module
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeEstimate
public import QuantitativeFollowup.CavityTransferredThermalBudget
public import QuantitativeFollowup.FollowupCavityDecouplingThreeMoment

@[expose] public section

/-! Literal transfer of the genuine signed rest response to the full SK
thermal budgets. Actual independent-endpoint terminal moments, positive
comparison and diagonal-completion transport are proved dependencies. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FRSB
variable {n:ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavitySignedResponseWeightedA_J_physical_transfer (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a β0:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (hβ0:β0≠0) (ha:a∈Icc (0:ℝ) 1) (hμ:μ∈scalarFloor a) :
    cavitySignedResponseWeightedA (followupCavityRestSpinModel n β ρ hβ hρ) μ a β0+
      cavitySignedResponseWeightedJ (followupCavityRestSpinModel n β ρ hβ hρ) μ a β0 Finset.univ≤
      8*Real.exp (43*β^2)*
        ((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q∂parisiFreeMeasure μ a)+
          followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
          1/((n+1:ℕ):ℝ)^2) := by
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let ν:=parisiFreeMeasure μ a
  let A:=cavitySignedResponseCovarianceTraceMoment D μ a
  let J:=cavitySignedResponseCovarianceMoment D μ a Finset.univ
  let Γ:=fun q:Paper.Overlap=>Gamma β0 μ q
  have hsum:Integrable (fun q:Paper.Overlap=>A q+J q) ν := by
    have hi:=(integrable_cavityThreeDescendant_normalized_difference_square
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a (n:ℝ)
      (Finset.univ.erase (Fin.last n)) ν).div_const 2
    exact hi.congr (.of_forall fun q=>followup_cavity_zero_deleted_three_half_square μ n β ρ hβ hρ a q)
  have hΓ:Measurable Γ:=
    ((continuousOn_Gamma β0 hβ0 μ).comp_continuous continuous_subtype_val (fun q=>q.property)).measurable
  have hA0 (q:Paper.Overlap):0≤A q:=(cavitySignedResponseCovarianceTraceMoment_bounds D μ a q).1
  have hJ0 (q:Paper.Overlap):0≤J q:=cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ q
  have hiA:Integrable (fun q:Paper.Overlap=>Γ q*A q) ν :=
    hsum.mono' (hΓ.mul (measurable_cavitySignedResponseCovarianceTraceMoment D μ a)).aestronglyMeasurable
      (.of_forall fun q=>by
        rw [Real.norm_of_nonneg (mul_nonneg (scalarGamma_nonneg β0 μ q) (hA0 q))]
        exact (mul_le_mul_of_nonneg_right (scalarGamma_le_one β0 μ q q.property) (hA0 q)).trans
          (by simpa only [one_mul] using le_add_of_nonneg_right (hJ0 q)))
  have hiJ:Integrable (fun q:Paper.Overlap=>Γ q*J q) ν :=
    hsum.mono' (hΓ.mul (measurable_cavitySignedResponseCovarianceMoment D μ a Finset.univ)).aestronglyMeasurable
      (.of_forall fun q=>by
        rw [Real.norm_of_nonneg (mul_nonneg (scalarGamma_nonneg β0 μ q) (hJ0 q))]
        exact (mul_le_mul_of_nonneg_right (scalarGamma_le_one β0 μ q q.property) (hJ0 q)).trans
          (by simpa only [one_mul] using le_add_of_nonneg_left (hA0 q)))
  have hmono:=integral_mono (hiA.add hiJ) hsum (fun q=>by
    have h:=mul_le_mul_of_nonneg_right (scalarGamma_le_one β0 μ q q.property) (add_nonneg (hA0 q) (hJ0 q))
    dsimp only [Pi.add_apply]
    nlinarith only [h])
  simp only [Pi.add_apply] at hmono
  rw [integral_add hiA hiJ] at hmono
  have hb:=followup_cavity_three_deleted_integrated_thermal_budget hn μ β ρ a hβ hρ ha
    (scalarFloor_cdf_lower hμ (by norm_num)) 0 ⟨le_rfl,zero_le_one⟩
  simp_rw [followup_cavity_zero_deleted_three_half_square] at hb
  exact hmono.trans hb

theorem followup_cavity_signed_response_physical_transfer (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a β0:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (hβ0:β0≠0) (ha:a∈Icc (0:ℝ) 1) (hμ:μ∈scalarFloor a) :
    followupCavityAlpha n β ρ*
      |∫p,cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a β0 hβ0 p
        ∂parisiFreeMeasure μ a|≤
      192*β^2*Real.exp (43*β^2)*
        ((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q∂parisiFreeMeasure μ a)+
          followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
          1/((n+1:ℕ):ℝ)^2) := by
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hnative:=cavitySignedResponse_T_native_integral_bound D hn μ a β0 hβ0 ha hμ
  have htransfer:=cavitySignedResponseWeightedA_J_physical_transfer hn μ β ρ a β0 hβ hρ hβ0 ha hμ
  have hA:0≤cavitySignedResponseWeightedA D μ a β0:=
    integral_nonneg fun p=>mul_nonneg (scalarGamma_nonneg β0 μ p)
      (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).1
  have habs : |∫p,cavitySignedResponseT D μ a β0 hβ0 p∂parisiFreeMeasure μ a|≤
      192*Real.exp (43*β^2)*
        ((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q∂parisiFreeMeasure μ a)+
          followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
          1/((n+1:ℕ):ℝ)^2) := by
    dsimp only [D] at hnative hA
    nlinarith only [hnative,htransfer,hA]
  have hα:followupCavityAlpha n β ρ≤β^2 := by
    have hd:=(followupCavityD_window n hn β ρ ⟨hρ.1.le,hρ.2⟩).2
    have hc:0≤followupCavityC β ρ:=mul_nonneg (sq_nonneg β) hρ.1.le
    unfold followupCavityD at hd
    linarith
  exact (mul_le_mul_of_nonneg_right hα (abs_nonneg _)).trans
    (by convert mul_le_mul_of_nonneg_left habs (sq_nonneg β) using 1 <;> ring)

end QuantitativeFollowup
