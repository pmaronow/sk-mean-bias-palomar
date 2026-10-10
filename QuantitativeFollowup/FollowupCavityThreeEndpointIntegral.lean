module
public import QuantitativeFollowup.FollowupCavityThreeEndpointTransfer
public import QuantitativeFollowup.CavityThreeDescendantMomentRegularity
public import QuantitativeFollowup.ThreeDescendantResponseMoments

@[expose] public section

/-! Integrated genuine three-descendant thermal transfer. The actual full
system trace/energy curve is integrable by its normalized posterior law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem foundationThermalAndMeanCovariance_eq_offDiagonal
    (μ:Paper.ParisiMeasure) (β t a:ℝ) (hβ:β≠0) (ht:t<1) (q:Paper.Overlap) :
    foundationThermalTrace (n:=n) μ β t a ht.le q+
      foundationMeanCovariance (n:=n) μ β t a ht.le q=
      cavitySignedResponseCovarianceTraceMoment (standardSKOffDiagonalModel n β t hβ ht) μ a q+
        cavitySignedResponseCovarianceMoment (standardSKOffDiagonalModel n β t hβ ht) μ a Finset.univ q := by
  have h1:=standardSKOffDiagonalThreeDescendant_integral μ β t a hβ ht q
    (fun σ:CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing Finset.univ σ/(n:ℝ))^2)
  have h2:=cavityThreeDescendantLaw_normalized_difference_square
    (standardSKOffDiagonalModel n β t hβ ht) μ a q
  have h3:=cavityVectorThreeDescendantLaw_normalized_difference_square (n:=n) μ β t a hβ ht q
  linarith

theorem integrable_foundationThermalAndMeanCovariance (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (hβ:β≠0) (ht:t<1) (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>foundationThermalTrace (n:=n) μ β t a ht.le q+
      foundationMeanCovariance (n:=n) μ β t a ht.le q) ν := by
  have hi:=(integrable_cavityThreeDescendant_normalized_difference_square
    (standardSKOffDiagonalModel n β t hβ ht) μ a (n:ℝ) Finset.univ ν).div_const 2
  exact hi.congr (.of_forall fun q=>by
    dsimp only
    rw [cavityThreeDescendantLaw_normalized_difference_square,
      ←foundationThermalAndMeanCovariance_eq_offDiagonal μ β t a hβ ht q]
    ring)

theorem followup_cavity_three_deleted_integrated_half_square_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hfloor:a≤Paper.parisiCDF μ 0)
    (u:ℝ) (hu:u∈Icc (0:ℝ) 1) :
    (∫q:Paper.Overlap,(∫z,
      (cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q)/2
      ∂parisiFreeMeasure μ a)≤
      8*Real.exp (43*β^2)*
        ((∫q:Paper.Overlap,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
          foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q
          ∂parisiFreeMeasure μ a)+1/((n+1:ℕ):ℝ)^2) := by
  let ν:=parisiFreeMeasure μ a
  let B:=fun q:Paper.Overlap=>foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
    foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q
  let c:=1/((n+1:ℕ):ℝ)^2
  have hi:= (integrable_cavityThreeDescendant_normalized_difference_square
    (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (n:ℝ)
      (Finset.univ.erase (Fin.last n)) ν).div_const 2
  have hB:Integrable B ν:=integrable_foundationThermalAndMeanCovariance μ β (1-ρ) a
    hβ.ne' (by linarith[hρ.1]) ν
  have hb:=integral_mono hi ((hB.add (integrable_const c)).const_mul (8*Real.exp (43*β^2)))
    (fun q=>followup_cavity_three_deleted_half_square_le hn μ β ρ a hβ hρ ha hfloor q u hu)
  rw [integral_const_mul] at hb
  simp only [Pi.add_apply] at hb
  rw [integral_add hB (integrable_const c),integral_const] at hb
  have hm:ν.real univ≤1 := by
    dsimp only [ν]
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
    linarith[ha.1]
  have hc:0≤c:=by dsimp only [c];positivity
  have hmassc:ν.real univ • c≤c := by
    simpa only [smul_eq_mul,one_mul] using mul_le_mul_of_nonneg_right hm hc
  have hend:(∫q,B q∂ν)+ν.real univ • c≤(∫q,B q∂ν)+c :=
    add_le_add le_rfl hmassc
  exact hb.trans (mul_le_mul_of_nonneg_left
    hend
    (by positivity))

end QuantitativeFollowup
