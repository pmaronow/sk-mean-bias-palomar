module
public import HexagonPaper.EdgeLikelihoodStoppedProfileLimit
public import HexagonPaper.EdgeLikelihoodStoppedEndpoints

@[expose] public section

/-! Direct continuous-path binding of `eq:cav-edge-likelihood`. The reference
is the actual affine Brownian path with the model's positive diagonal
covariance, and the diffusion is the actual native restarted Picard path.
The profile is arbitrary, and the printed open-interval exponent retains
both endpoint atoms through the right CDF at the start and left CDF at the
end. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgePrintedLikelihood (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (
    edgeLeftCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)-
    Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)-
    ∫r in Ioo q h,anisotropicMeasureTailPotential D μ r (Z r) ∂parisiFreeMeasure μ a))

theorem measurable_edgeStoppedLikelihood_path (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) :
    Measurable (edgeStoppedLikelihood D μ q h) := by
  have he : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>Z h) := continuous_eval_const _
  have hc : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>
      anisotropicMeasureTailPotential D μ h (Z h)-edgeStoppedAction D μ q h Z) :=
    ((edgeTailPotentialMap D μ).continuous.comp (continuous_const.prodMk he)).sub
      (edgeStoppedAction_lipschitz D μ q h).continuous
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hc).measurable

theorem edge_stopped_continuous_path_likelihood_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q h : Paper.Overlap)
    (hqh : q≤h) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D μ g q h x)=
      ((vectorDisorderBrownianMeasure n).map (edgeStoppedReferencePath D g q h x)).withDensity
        (edgeStoppedLikelihood D μ q h) := by
  rw [←map_withDensity_pullback _ _ (measurable_edgeStoppedReferencePath D g q h x)
    _ (measurable_edgeStoppedLikelihood_path D μ q h)]
  exact edge_stopped_continuous_path_likelihood D μ g q h hqh x

theorem edge_continuous_path_likelihood_printed (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (hqh : q<h) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D μ g q h x)=
      ((vectorDisorderBrownianMeasure n).map (edgeStoppedReferencePath D g q h x)).withDensity
        (edgePrintedLikelihood D μ a q h) := by
  have he : edgeStoppedLikelihood D μ q h=edgePrintedLikelihood D μ a q h := by
    funext Z
    exact edgeStoppedLikelihood_eq_printed_free_endpoints D μ a ha hμ q h hqh Z
  rw [←he]
  exact edge_stopped_continuous_path_likelihood_density D μ g q h hqh.le x

theorem edge_printed_likelihood_normalized (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (hqh : q<h) (x : Field n) :
    (∫⁻Z,edgePrintedLikelihood D μ a q h Z
      ∂(vectorDisorderBrownianMeasure n).map (edgeStoppedReferencePath D g q h x))=1 := by
  have he:=congrArg (fun P : Measure C(Paper.Overlap,AnisotropicParameter n)=>P univ)
    (edge_continuous_path_likelihood_printed D μ a ha hμ g q h hqh x)
  rw [Measure.map_apply (measurable_edgeStoppedDiffusionPath D μ g q h x) MeasurableSet.univ,
    preimage_univ,measure_univ,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at he
  exact he.symm

end HexagonPaper
