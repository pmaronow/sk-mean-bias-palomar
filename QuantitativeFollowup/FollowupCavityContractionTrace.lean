module
public import QuantitativeFollowup.FollowupCavityRestResponseTrace
public import QuantitativeFollowup.FollowupCavityParameters

@[expose] public section

/-! Genuine trace domination and the physical cavity contraction factor.
These leaves use the stated scalar quadratic-order hypothesis; they do
not assume or assert the separate native zero-row derivative identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityRestResponseTrace_le_of_quadratic_order
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) (K : ℝ)
    (hJ : ∀f : endpointFixedL2 (parisiFreeMeasure μ a),
      inner ℝ f (scalarResponseL2Operator β hβ μ a ha hμ f) ≤ K*‖f‖^2) :
    cavityRestResponseTrace D β hβ μ a ha hμ ≤ K*cavityRestVariance D μ a := by
  let J:=scalarResponseL2Operator β hβ μ a ha hμ
  let X:=cavityRestEndpointProcess D μ a
  have hx:=memLp_cavityRestEndpointProcess D μ a
  have hn:=hx.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hm : AEStronglyMeasurable (fun ω=>inner ℝ (X ω) (J (X ω)))
      (anisotropicMeasureSampleLaw D μ a):=
    hx.aestronglyMeasurable.inner (J.continuous.comp_aestronglyMeasurable hx.aestronglyMeasurable)
  have hb (ω : AnisotropicDisorderBrownianSample n) :
      ‖inner ℝ (X ω) (J (X ω))‖≤‖J‖*‖X ω‖^2 := by
    calc
      _≤‖X ω‖*‖J (X ω)‖:=norm_inner_le_norm _ _
      _≤‖X ω‖*(‖J‖*‖X ω‖):=mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _=_:=by ring
  have hi : Integrable (fun ω=>inner ℝ (X ω) (J (X ω))) (anisotropicMeasureSampleLaw D μ a):=
    (hn.const_mul ‖J‖).mono' hm (.of_forall hb)
  have h:=integral_mono hi (hn.const_mul K) (fun ω=>hJ (X ω))
  simpa only [integral_const_mul,←cavityRestVariance_eq_integral_norm_sq D μ a hone,
    cavityRestResponseTrace,J,X] using h

theorem followupCavityAlpha_div_D_mem_contraction_interval
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    followupCavityAlpha n β ρ/followupCavityD n β ρ ∈ Icc (0:ℝ) (1-ρ) := by
  have hw:=followupCavityD_window n hn β ρ ⟨hρ.1.le,hρ.2⟩
  have hd : 0<followupCavityD n β ρ:=(by positivity : 0<β^2/2).trans_le hw.1
  constructor
  · exact div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) hd.le
  · apply (div_le_iff₀ hd).mpr
    have hc:=mul_le_mul_of_nonneg_left hw.2 hρ.1.le
    have he : followupCavityD n β ρ=β^2*ρ+followupCavityAlpha n β ρ:=rfl
    nlinarith only [hc,he]

theorem followupCavity_effective_response_gap
    (hn : 0<n) (β ρ ε : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (hε : ε∈Icc (0:ℝ) (ρ/4)) :
    followupCavityAlpha n β ρ/followupCavityD n β ρ*(1+ε) ≤ 1-ρ/2 := by
  have hr:=followupCavityAlpha_div_D_mem_contraction_interval hn β ρ hβ hρ
  have hm:=mul_le_mul_of_nonneg_right hr.2 (by linarith [hε.1] : 0≤1+ε)
  have he:=mul_le_mul_of_nonneg_left hε.2 (sub_nonneg.mpr hρ.2)
  nlinarith only [hm,he,sq_nonneg ρ,hρ.1.le]

end QuantitativeFollowup
