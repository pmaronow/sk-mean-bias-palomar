module
public import QuantitativeFollowup.ScalarTransportVariationBounds
public import QuantitativeFollowup.ParameterSpatialInterchange

@[expose] public section

/-! The parameter derivative of the actual transported-node magnetization,
proved from the actual potential partials by finite-interval FTC. No mixed
partial or joint second parameter regularity is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem continuous_scalarTransportPotentialVariation (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (q : Paper.Overlap) :
    Continuous (fun z : ℝ×ℝ=>scalarTransportPotentialVariation β μ φ z.1 q z.2) := by
  have hμ : Continuous (fun z : ℝ×ℝ=>scalarTransportMeasure μ φ z.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk continuous_fst)
  have hq : Continuous (fun z : ℝ×ℝ=>(scalarLevelTransport φ z.1 q:ℝ)) :=
    continuous_subtype_val.comp ((continuous_scalarLevelTransport φ).comp (continuous_fst.prodMk continuous_const))
  have harg : Continuous (fun z : ℝ×ℝ=>
      (scalarTransportMeasure μ φ z.1,((scalarLevelTransport φ z.1 q:ℝ),z.2))) :=
    hμ.prodMk (hq.prodMk continuous_snd)
  have hM := (continuous_parisiGradient_measure_joint β).comp harg
  have hH := (continuous_parisiHessian_measure_joint β hβ).comp harg
  have hi : Continuous (fun z : ℝ×ℝ=>
      ∫r in Ioi q,φ r*scalarTransportFutureSquare β μ φ z.1 q r z.2 ∂(μ:Measure Paper.Overlap)) := by
    have hf : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap=>
        φ z.2*scalarTransportFutureSquare β μ φ z.1.1 q z.2 z.1.2) := by
      have ha : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap=>(z.1,(q,z.2))) := by fun_prop
      have hg : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap=>
          scalarTransportFutureSquare β μ φ z.1.1 q z.2 z.1.2) := by
        simpa only [Function.comp_def] using (continuous_scalarTransportFutureSquare_joint β μ φ).comp ha
      exact (φ.continuous.comp continuous_snd).mul hg
    apply continuous_of_dominated (μ:=(μ:Measure Paper.Overlap).restrict (Ioi q)) (bound:=fun _=>‖φ‖)
    · intro z
      exact (hf.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
    · intro z
      exact .of_forall fun r=>by
        rw [norm_mul]
        exact (mul_le_mul (φ.norm_coe_le_norm r) (scalarTransportFutureSquare_norm_le β μ φ z.1 q r z.2)
          (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    · exact integrable_const _
    · exact .of_forall fun r=>hf.comp (continuous_id.prodMk continuous_const)
  simpa only [scalarTransportPotentialVariation,Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.pow_apply] using
    (((hH.add ((hM.pow 2).const_mul (Paper.parisiCDF μ q))).const_mul (φ q)).add hi).const_mul (-(β^2/2))

theorem hasDerivAt_scalarTransportBoundaryGradient_variation (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    HasDerivAt (fun v=>scalarTransportBoundaryGradient s β φ (k+2-J) v x)
      (scalarTransportPotentialVariationSpatial β (Paper.parisiSchemeMeasure s) φ u
        (scalarSchemeTransportNode s (k+2-J)) x) u := by
  let q:=scalarSchemeTransportNode s (k+2-J)
  let F:=scalarTransportNodePotential s β φ (k+2-J)
  let P:=scalarTransportBoundaryGradient s β φ (k+2-J)
  let D:=fun v y=>scalarTransportPotentialVariation β (Paper.parisiSchemeMeasure s) φ v q y
  let E:=fun v y=>scalarTransportPotentialVariationSpatial β (Paper.parisiSchemeMeasure s) φ v q y
  apply hasDerivAt_spatialDerivative_of_parameterPartials F P D E (-δ) δ u x
    (scalarTransportVariationSpatialBound β φ) (abs_lt.mp hu)
  · exact (continuous_scalarTransportPotentialVariation β hβ.ne' _ φ q).continuousOn
  · exact (continuous_scalarTransportPotentialVariationSpatial β hβ.ne' _ φ q).continuousOn
  · intro v hv y
    exact hasDerivAt_scalarTransportNodePotential_variation s β hβ φ L hφ h0 h1 δ v y
      hδ hsmall (abs_lt.mpr hv) J hJ
  · intro v hv y
    exact Paper.hasDerivAt_parisiPotential_spatial_all β _ _ y
      (scalarLevelTransport φ v q).property
  · intro v hv y
    exact hasDerivAt_scalarTransportPotentialVariation_spatial β hβ.ne' _ φ L hφ h0 h1 v
      (scalarTransport_parameter_small L δ v hsmall (abs_lt.mpr hv).le) q y
  · intro v hv y
    exact norm_scalarTransportPotentialVariationSpatial_le β _ φ v q y

end QuantitativeFollowup
