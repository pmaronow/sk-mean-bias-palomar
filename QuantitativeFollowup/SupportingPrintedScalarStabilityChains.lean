module
public import QuantitativeFollowup.ScalarTransportFunctionalBasics
public import Paper.ParisiSelectedGFubini
public import Paper.ParisiCurvature
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Literal scalar spatial bounds, right first variation, and convex
transport support. These are the actual Parisi solution and functional;
the harmless terminal constant log 2 has no spatial derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper

theorem supporting_printed_scalar_spatial_bounds (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    |parisiGradient β μ (q,x)|≤1 ∧
      0≤parisiHessian β μ (q,x) ∧
      parisiHessian β μ (q,x)≤1-parisiGradient β μ (q,x)^2 ∧
      1-parisiGradient β μ (q,x)^2≤1 := by
  refine ⟨?_,(parisiHessian_pos β hβ μ q x hq).le,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using norm_parisiGradient_le_one β μ (q,x)
  · linarith [parisiHessian_add_gradient_sq_le_one β hβ μ (q,x)]
  · linarith [sq_nonneg (parisiGradient β μ (q,x))]

theorem supporting_printed_scalar_first_variation (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) :
    HasDerivWithinAt (fun θ=>scalarParisiFunctional β (parisiMix μ ν θ))
      (β^2/2*(∫q in (0:ℝ)..1,(Gamma β μ q-q)*
        (parisiCDF ν q-parisiCDF μ q))) (Ioi (0:ℝ)) 0 := by
  have hd := hasDerivWithinAt_parisiPDEFunctional_mix_G β 0 hβ μ ν
  rw [integral_selectedParisiG_sub_eq_cdf] at hd
  change HasDerivWithinAt (fun θ=>scalarParisiFunctional β (parisiMix μ ν θ)) _ _ _ at hd
  apply hd.congr_deriv
  congr 1
  apply intervalIntegral.integral_congr
  intro q _
  dsimp only
  rw [←Gamma_eq_selectedSecondMoment β hβ μ q]
  ring

theorem supporting_printed_scalar_first_variation_limit (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) :
    Tendsto (fun θ=>(scalarParisiFunctional β (parisiMix μ ν θ)-
      scalarParisiFunctional β μ)/θ) (𝓝[>] (0:ℝ))
      (𝓝 (β^2/2*(∫q in (0:ℝ)..1,(Gamma β μ q-q)*
        (parisiCDF ν q-parisiCDF μ q)))) := by
  have H := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0:ℝ)∉Ioi (0:ℝ) by simp)).mp
      (supporting_printed_scalar_first_variation β hβ μ ν)
  convert H using 1
  funext θ
  rw [slope_def_field,parisiMix_zero,sub_zero]

theorem supporting_printed_scalar_transport_convex_chain (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (θ : ℝ) :
    β^2/2*(∫q : Paper.Overlap,
      scalarGammaTail β μ (scalarLevelTransport φ θ q)-scalarGammaTail β μ q
        ∂(μ:Measure Paper.Overlap)) ≤
      scalarTransportFunctional β μ φ θ-scalarTransportFunctional β μ φ 0 := by
  have hleft : Integrable (fun q : Paper.Overlap=>
      scalarGammaTail β μ (scalarLevelTransport φ θ q)) (μ:Measure Paper.Overlap) := by
    have hc := continuous_selectedParisiG_overlap β 0 hβ μ
    have he (q : Paper.Overlap) : scalarGammaTail β μ q =
        (β^2/2)⁻¹*selectedParisiG β 0 hβ μ q := by
      rw [selectedParisiG_eq_scalarGammaTail β hβ μ]
      field_simp
    apply integrable_overlap_continuous
    have htail : Continuous (fun q : Paper.Overlap=>scalarGammaTail β μ q) := by
      simp_rw [he]
      exact continuous_const.mul hc
    exact htail.comp (continuous_scalarLevelTransport_parameter φ θ)
  have hright : Integrable (fun q : Paper.Overlap=>scalarGammaTail β μ q)
      (μ:Measure Paper.Overlap) := by
    apply integrable_overlap_continuous
    have he (q : Paper.Overlap) : scalarGammaTail β μ q =
        (β^2/2)⁻¹*selectedParisiG β 0 hβ μ q := by
      rw [selectedParisiG_eq_scalarGammaTail β hβ μ]
      field_simp
    simp_rw [he]
    exact continuous_const.mul (continuous_selectedParisiG_overlap β 0 hβ μ)
  rw [integral_sub hleft hright]
  exact scalarTransportFunctional_convex_support β hβ μ φ θ

end QuantitativeFollowup
