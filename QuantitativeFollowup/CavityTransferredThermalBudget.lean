module
public import QuantitativeFollowup.FollowupCavityThreeEndpointIntegral
public import QuantitativeFollowup.SupportingSourceNormalization
public import QuantitativePaper.VectorReplicaDefectMeasurability

@[expose] public section

/-! Honest nonnegativity and free-measure integrability of the two actual
full-system thermal budgets, and the integrated three-descendant transfer
in the literal separate A and J notation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem foundationThermalTrace_nonneg (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) :
    0≤foundationThermalTrace (n:=n) μ β t a ht q := by
  unfold foundationThermalTrace
  apply div_nonneg _ (sq_nonneg _)
  apply integral_nonneg
  intro sample
  change 0≤Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
    vectorMeasureSpinCovariance μ β t a ht q sample)
  rw [symmetric_matrix_square_trace _ (vectorMeasureSpinCovariance_symmetric μ β t a ht q sample)]
  positivity

theorem foundationMeanCovariance_nonneg (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (hβ:β≠0) (ht:t<1) (q:Paper.Overlap) :
    0≤foundationMeanCovariance (n:=n) μ β t a ht.le q := by
  apply integral_nonneg_of_ae
  have he:=(measurePreserving_vectorMeasureSpinPathLaw_fst (n:=n) μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasureCovarianceQuadratic_nonneg (n:=n) μ β t a hβ ht q)
  filter_upwards [he] with z hz
  exact div_nonneg (hz _) (sq_nonneg _)

theorem integrable_foundationThermalTrace_and_meanCovariance (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (hβ:β≠0) (ht:t<1) (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (foundationThermalTrace (n:=n) μ β t a ht.le) ν ∧
      Integrable (foundationMeanCovariance (n:=n) μ β t a ht.le) ν := by
  let A:=foundationThermalTrace (n:=n) μ β t a ht.le
  let J:=foundationMeanCovariance (n:=n) μ β t a ht.le
  let D:=standardSKOffDiagonalModel n β t hβ ht
  have hi:=integrable_foundationThermalAndMeanCovariance (n:=n) μ β t a hβ ht ν
  have hmA:Measurable A:=
    (measurable_integral_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t a ht.le).div_const _
  have hmB:Measurable (fun q:Paper.Overlap=>A q+J q) := by
    dsimp only [A,J]
    simp_rw [foundationThermalAndMeanCovariance_eq_offDiagonal μ β t a hβ ht]
    exact (measurable_cavitySignedResponseCovarianceTraceMoment D μ a).add
      (measurable_cavitySignedResponseCovarianceMoment D μ a Finset.univ)
  have hmJ:Measurable J := by
    have he:J=(fun q:Paper.Overlap=>A q+J q-A q):=by funext q;ring
    rw [he]
    exact hmB.sub hmA
  constructor
  · exact hi.mono' hmA.aestronglyMeasurable (.of_forall fun q=>by
      rw [Real.norm_of_nonneg (foundationThermalTrace_nonneg μ β t a ht.le q)]
      exact le_add_of_nonneg_right (foundationMeanCovariance_nonneg μ β t a hβ ht q))
  · exact hi.mono' hmJ.aestronglyMeasurable (.of_forall fun q=>by
      rw [Real.norm_of_nonneg (foundationMeanCovariance_nonneg μ β t a hβ ht q)]
      exact le_add_of_nonneg_left (foundationThermalTrace_nonneg μ β t a ht.le q))

theorem followup_cavity_three_deleted_integrated_thermal_budget (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hfloor:a≤Paper.parisiCDF μ 0)
    (u:ℝ) (hu:u∈Icc (0:ℝ) 1) :
    (∫q:Paper.Overlap,(∫z,
      (cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q)/2
      ∂parisiFreeMeasure μ a)≤
      8*Real.exp (43*β^2)*
        ((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q∂parisiFreeMeasure μ a)+
          followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
          1/((n+1:ℕ):ℝ)^2) := by
  have hi:=integrable_foundationThermalTrace_and_meanCovariance (n:=n+1) μ β (1-ρ) a
    hβ.ne' (by linarith[hρ.1]) (parisiFreeMeasure μ a)
  have h:=followup_cavity_three_deleted_integrated_half_square_le hn μ β ρ a hβ hρ ha hfloor u hu
  rw [integral_add hi.1 hi.2] at h
  exact h

end QuantitativeFollowup
