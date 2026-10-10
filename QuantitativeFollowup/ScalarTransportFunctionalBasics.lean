module
public import QuantitativeFollowup.ScalarStepResponse
public import Paper.ParisiFirstVariation
public import Paper.ParisiMixConvexity

@[expose] public section

/-! Deterministic normalization and the actual convex supporting inequality
for scalar overlap transports. The first variation is the proved PDE/state
first variation, not an assumed transport-Hessian formula. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarGammaTail (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  ∫ r in q..1, Gamma β μ r-r

def scalarTransportFunctional (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) : ℝ :=
  scalarParisiFunctional β (scalarTransportMeasure μ φ u)

theorem scalar_cdf_correction_eq_second_moment (μ : Paper.ParisiMeasure) :
    (∫ r in (0:ℝ)..1, r*parisiCDF μ r)=
      (1-(∫ q : Paper.Overlap,(q:ℝ)^2 ∂(μ:Measure Paper.Overlap)))/2 := by
  have hi : IntegrableOn (fun r : ℝ=>r) (Ioc (0:ℝ) 1) volume :=
    (continuous_id.intervalIntegrable 0 1).1
  have hh := parisiCDF_tail_pairing μ (fun r : ℝ=>r) hi
  simp only [integral_id] at hh
  have hsq : Integrable (fun q : Paper.Overlap=>(q:ℝ)^2) (μ:Measure Paper.Overlap) :=
    integrable_overlap_continuous (continuous_subtype_val.pow 2) μ
  have hleft : (∫ q : Paper.Overlap,(1-(q:ℝ)^2)/2 ∂(μ:Measure Paper.Overlap))=
      (1-(∫ q : Paper.Overlap,(q:ℝ)^2 ∂(μ:Measure Paper.Overlap)))/2 := by
    rw [integral_div,integral_sub (integrable_const 1) hsq]
    simp
  simp only [one_pow] at hh
  exact hh.symm.trans hleft

theorem scalarTransportFunctional_eq_second_moment (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) :
    scalarTransportFunctional β μ φ u=Real.log 2+
      parisiPotential β (scalarTransportMeasure μ φ u) (0,0)-β^2/4+
      β^2/4*(∫q : Paper.Overlap,(scalarLevelTransport φ u q:ℝ)^2 ∂(μ:Measure Paper.Overlap)) := by
  rw [scalarTransportFunctional,scalarParisiFunctional,parisiPDEFunctional,Paper.parisiFunctional,
    scalar_cdf_correction_eq_second_moment]
  have hmap : (∫q : Paper.Overlap,(q:ℝ)^2
      ∂(scalarTransportMeasure μ φ u:Measure Paper.Overlap))=
      ∫q : Paper.Overlap,(scalarLevelTransport φ u q:ℝ)^2 ∂(μ:Measure Paper.Overlap) := by
    rw [scalarTransportMeasure,ProbabilityMeasure.toMeasure_map]
    exact integral_map (continuous_scalarLevelTransport_parameter φ u).measurable.aemeasurable
      (continuous_subtype_val.pow 2).aestronglyMeasurable
  rw [hmap]
  ring

theorem selectedParisiG_eq_scalarGammaTail (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (q : ℝ) :
    selectedParisiG β 0 hβ μ q=β^2/2*scalarGammaTail β μ q := by
  unfold selectedParisiG parisiG scalarGammaTail
  rw [intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  change selectedParisiSecondMoment β 0 hβ μ r-r=Gamma β μ r-r
  rw [←Gamma_eq_selectedSecondMoment β hβ μ r]

theorem scalarParisiFunctional_convex_support (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) :
    β^2/2*((∫q : Paper.Overlap,scalarGammaTail β μ q ∂(ν:Measure Paper.Overlap))-
      ∫q : Paper.Overlap,scalarGammaTail β μ q ∂(μ:Measure Paper.Overlap))≤
      scalarParisiFunctional β ν-scalarParisiFunctional β μ := by
  have hd := hasDerivWithinAt_parisiPDEFunctional_mix_G β 0 hβ μ ν
  have hc := (convexOn_parisiPDEFunctional_mix β 0 μ ν).le_slope_of_hasDerivWithinAt_Ioi
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (1:ℝ)∈Icc 0 1) (by norm_num) hd
  simp only [slope_def_field,parisiMix_zero,parisiMix_one,sub_zero,div_one] at hc
  simp only [selectedParisiG_eq_scalarGammaTail β hβ μ,integral_const_mul] at hc
  simpa only [scalarParisiFunctional,mul_sub] using hc

theorem scalarTransportFunctional_convex_support (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (u : ℝ) :
    β^2/2*((∫q : Paper.Overlap,scalarGammaTail β μ (scalarLevelTransport φ u q)
      ∂(μ:Measure Paper.Overlap))-
      ∫q : Paper.Overlap,scalarGammaTail β μ q ∂(μ:Measure Paper.Overlap))≤
      scalarTransportFunctional β μ φ u-scalarTransportFunctional β μ φ 0 := by
  have hc := scalarParisiFunctional_convex_support β hβ μ (scalarTransportMeasure μ φ u)
  have hm : (∫q : Paper.Overlap,scalarGammaTail β μ q
      ∂(scalarTransportMeasure μ φ u:Measure Paper.Overlap))=
      ∫q : Paper.Overlap,scalarGammaTail β μ (scalarLevelTransport φ u q)
        ∂(μ:Measure Paper.Overlap) := by
    rw [scalarTransportMeasure,ProbabilityMeasure.toMeasure_map]
    have hg : Continuous (fun q : Paper.Overlap=>scalarGammaTail β μ q) := by
      have he : (fun q : Paper.Overlap=>scalarGammaTail β μ q)=
          fun q : Paper.Overlap=> (β^2/2)⁻¹*selectedParisiG β 0 hβ μ q := by
        funext q
        rw [selectedParisiG_eq_scalarGammaTail β hβ μ]
        field_simp
      rw [he]
      exact continuous_const.mul (continuous_selectedParisiG_overlap β 0 hβ μ)
    exact integral_map (continuous_scalarLevelTransport_parameter φ u).measurable.aemeasurable
      hg.aestronglyMeasurable
  rw [hm] at hc
  simpa only [scalarTransportFunctional,scalarTransportMeasure_zero] using hc

end QuantitativeFollowup
