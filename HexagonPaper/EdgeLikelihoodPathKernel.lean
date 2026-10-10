module
public import HexagonPaper.EdgeLikelihoodPathKernelBasic

@[expose] public section

/-! Genuine physical and reference complete-edge path kernels. Their RN
identity follows from the arbitrary-profile actual edge likelihood at
every start; normalization follows from the physical Markov kernel. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgePhysicalPathKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) :
    Kernel (AnisotropicObservationState n) C(Paper.Overlap,AnisotropicParameter n) :=
  independentNoiseKernel (vectorDisorderBrownianMeasure n)
    (fun z=>edgeStoppedDiffusionPath D μ z.1.1 q h z.1.2 z.2)

instance edgePhysicalPathKernel_markov (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) : IsMarkovKernel (edgePhysicalPathKernel D μ q h) :=
  isMarkovKernel_independentNoiseKernel _ _ (measurable_edgeStoppedDiffusionPath_start D μ q h)

def edgeReferencePathKernel (D : AnisotropicSpinModel n) (q h : Paper.Overlap) :
    Kernel (AnisotropicObservationState n) C(Paper.Overlap,AnisotropicParameter n) :=
  independentNoiseKernel (vectorDisorderBrownianMeasure n)
    (fun z=>edgeStoppedReferencePath D z.1.1 q h z.1.2 z.2)

instance edgeReferencePathKernel_markov (D : AnisotropicSpinModel n) (q h : Paper.Overlap) :
    IsMarkovKernel (edgeReferencePathKernel D q h) :=
  isMarkovKernel_independentNoiseKernel _ _ (measurable_edgeStoppedReferencePath_start D q h)

def edgePathLogDensity (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : ℝ :=
  anisotropicMeasureTailPotential D μ h (Z h)-edgeStoppedAction D μ q h Z

theorem continuous_edgePathLogDensity (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) : Continuous (edgePathLogDensity D μ q h) :=
  ((edgeTailPotentialMap D μ).continuous.comp
    (continuous_const.prodMk (continuous_eval_const h))).sub
      (edgeStoppedAction_lipschitz D μ q h).continuous

theorem edgePhysicalPathKernel_apply (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (z : AnisotropicObservationState n) :
    edgePhysicalPathKernel D μ q h z=
      (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D μ z.1 q h z.2) :=
  independentNoiseKernel_apply _ _ (measurable_edgeStoppedDiffusionPath_start D μ q h) z

theorem edgeReferencePathKernel_apply (D : AnisotropicSpinModel n) (q h : Paper.Overlap)
    (z : AnisotropicObservationState n) :
    edgeReferencePathKernel D q h z=
      (vectorDisorderBrownianMeasure n).map (edgeStoppedReferencePath D z.1 q h z.2) :=
  independentNoiseKernel_apply _ _ (measurable_edgeStoppedReferencePath_start D q h) z

theorem edgePhysicalPathKernel_exp_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (hqh : q≤h) :
    edgePhysicalPathKernel D μ q h=(edgeReferencePathKernel D q h).withDensity
      (fun _ Z=>ENNReal.ofReal (Real.exp (edgePathLogDensity D μ q h Z))) := by
  ext z : 1
  rw [edgePhysicalPathKernel_apply,Kernel.withDensity_apply _
    (((continuous_edgePathLogDensity D μ q h).measurable.comp measurable_snd).exp.ennreal_ofReal),
    edgeReferencePathKernel_apply]
  exact edge_stopped_continuous_path_likelihood_density D μ z.1 q h hqh z.2

theorem edgePhysicalPathKernel_printed_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q h : Paper.Overlap) (hqh : q<h) :
    edgePhysicalPathKernel D μ q h=(edgeReferencePathKernel D q h).withDensity
      (fun _ Z=>edgePrintedLikelihood D μ a q h Z) := by
  have hw:edgeStoppedLikelihood D μ q h=edgePrintedLikelihood D μ a q h:=by
    funext Z
    exact edgeStoppedLikelihood_eq_printed_free_endpoints D μ a ha hμ q h hqh Z
  change edgePhysicalPathKernel D μ q h=(edgeReferencePathKernel D q h).withDensity
    (fun _ Z=>edgePrintedLikelihood D μ a q h Z)
  rw [←hw]
  exact edgePhysicalPathKernel_exp_density D μ q h hqh.le

end HexagonPaper
