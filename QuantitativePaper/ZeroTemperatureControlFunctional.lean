module
public import QuantitativePaper.ZeroTemperatureControlLower
public import QuantitativePaper.ZeroTemperatureControlScaling
public import QuantitativePaper.ZeroTemperatureControlTruncation
public import QuantitativePaper.ScalarVariational

@[expose] public section

/-! Actual scalar functional comparison and integrable-profile completion.
These are properties of the constructed control value, rather than assumed
zero-temperature convergence conclusions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

theorem zeroControlEndpoint_congr_Ioo (γ η : ℝ→ℝ) (he : EqOn γ η (Ioo (0:ℝ) 1))
    (x : ℝ) (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) :
    zeroControlEndpoint γ x A ω=zeroControlEndpoint η x A ω := by
  unfold zeroControlEndpoint
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)]
  intro q hq
  dsimp only
  rw [he hq]

theorem zeroControlCost_congr_Ioo (γ η : ℝ→ℝ) (he : EqOn γ η (Ioo (0:ℝ) 1))
    (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) :
    zeroControlCost γ A ω=zeroControlCost η A ω := by
  unfold zeroControlCost
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)]
  intro q hq
  dsimp only
  rw [he hq]

theorem zeroTemperatureValue_congr_Ioo (γ η : ℝ→ℝ) (he : EqOn γ η (Ioo (0:ℝ) 1))
    (x : ℝ) : zeroTemperatureValue γ x=zeroTemperatureValue η x := by
  have ho : ∀A,zeroControlObjective γ x A=zeroControlObjective η x A := by
    intro A
    apply integral_congr_ae
    exact .of_forall fun ω=>by
      unfold zeroControlPayoff
      rw [zeroControlEndpoint_congr_Ioo γ η he,zeroControlCost_congr_Ioo γ η he]
  unfold zeroTemperatureValue zeroControlValues
  simp_rw [ho]

theorem zeroTemperatureFunctional_congr_Ioo (γ η : ℝ→ℝ)
    (he : EqOn γ η (Ioo (0:ℝ) 1)) :
    zeroTemperatureFunctional γ=zeroTemperatureFunctional η := by
  unfold zeroTemperatureFunctional
  rw [zeroTemperatureValue_congr_Ioo γ η he]
  congr 2
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)]
  intro q hq
  dsimp only
  rw [he hq]

theorem zeroTemperatureFunctional_difference_bound (γ η : ℝ→ℝ)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hiη : IntervalIntegrable η volume (0:ℝ) 1) :
    ‖zeroTemperatureFunctional γ-zeroTemperatureFunctional η‖≤2*zeroProfileDistance γ η := by
  have hv:=zeroTemperatureValue_difference_bound γ η hγ hη hiγ hiη 0
  have hc : ‖(∫q in (0:ℝ)..1,q*γ q)-(∫q in (0:ℝ)..1,q*η q)‖≤zeroProfileDistance γ η := by
    rw [←intervalIntegral.integral_sub
      (intervalIntegrable_zeroTemperatureCorrection γ hγ hiγ)
      (intervalIntegrable_zeroTemperatureCorrection η hη hiη)]
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ (hiγ.sub hiη).norm
    exact .of_forall fun q hq=>by
      rw [show q*γ q-q*η q=q*(γ q-η q) by ring,norm_mul,Real.norm_of_nonneg hq.1.le]
      exact (mul_le_mul_of_nonneg_right hq.2 (norm_nonneg _)).trans_eq (one_mul _)
  have he : zeroTemperatureFunctional γ-zeroTemperatureFunctional η=
      (zeroTemperatureValue γ 0-zeroTemperatureValue η 0)-
      (1/2:ℝ)*((∫q in (0:ℝ)..1,q*γ q)-(∫q in (0:ℝ)..1,q*η q)) := by
    unfold zeroTemperatureFunctional
    ring
  rw [he]
  have hh:=norm_sub_le (zeroTemperatureValue γ 0-zeroTemperatureValue η 0)
    ((1/2:ℝ)*((∫q in (0:ℝ)..1,q*γ q)-(∫q in (0:ℝ)..1,q*η q)))
  rw [norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))] at hh
  exact hh.trans (by linarith)

theorem tendsto_zeroTemperatureFunctional_truncation (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hγ0 : ∀ᵐ q ∂volume,q∈Ioc (0:ℝ) 1→0≤γ q) :
    Tendsto (fun R:ℝ=>zeroTemperatureFunctional (zeroProfileTruncation γ R)) atTop
      (𝓝 (zeroTemperatureFunctional γ)) := by
  rw [←tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (fun R=>zeroTemperatureFunctional_difference_bound _ γ
    (measurable_zeroProfileTruncation γ hγ R) hγ
    (intervalIntegrable_zeroProfileTruncation γ hγ hiγ R) hiγ)
  convert! (tendsto_zeroProfileDistance_truncation γ hγ hiγ hγ0).const_mul (2:ℝ) using 1 <;> simp

theorem zeroTemperatureFunctional_parisi_sandwich (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) :
    zeroTemperatureFunctional (fun q=>β*parisiCDF μ q) ≤ scalarParisiFunctional β μ/β ∧
      scalarParisiFunctional β μ/β≤zeroTemperatureFunctional (fun q=>β*parisiCDF μ q)+Real.log 2/β := by
  have hh:=zeroTemperatureValue_parisi_sandwich β hβ μ 0
  have he : scalarParisiFunctional β μ/β=
      (Real.log 2+parisiPotential β μ (0,0))/β-
      (1/2:ℝ)*(∫q in (0:ℝ)..1,q*(β*parisiCDF μ q)) := by
    unfold scalarParisiFunctional parisiPDEFunctional parisiFunctional
    have hi : (∫q in (0:ℝ)..1,q*(β*parisiCDF μ q))=
        β*(∫q in (0:ℝ)..1,q*parisiCDF μ q) := by
      simp_rw [show ∀q:ℝ,q*(β*parisiCDF μ q)=β*(q*parisiCDF μ q) by intro q;ring]
      rw [intervalIntegral.integral_const_mul]
    rw [hi]
    field_simp
    <;> ring
  simp only [mul_zero] at hh
  rw [he]
  unfold zeroTemperatureFunctional
  constructor <;> linarith [hh.1,hh.2]

end QuantitativePaper
