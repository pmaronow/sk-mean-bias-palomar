module
public import HexagonPaper.CavityTreeUnitCouplings
public import HexagonPaper.EdgeLikelihoodPathKernelSourceLog

@[expose] public section

/-! Genuine unit-coupling transport of the affine Wiener reference and
the complete arbitrary-profile edge action. Zero coupling scales are
retained; no inverse of the coupling rescaling is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cavityCouplingDisorderRescaling (D : AnisotropicSpinModel n) :
    AnisotropicDisorder n →L[ℝ] AnisotropicDisorder n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun g=>WithLp.toLp 2 (fun e=>D.coupling e*g e)
      map_add':=by intro g h;ext e;simp [mul_add]
      map_smul':=by intro c g;ext e;simp [mul_left_comm] }

def cavityCouplingStartRescaling (D : AnisotropicSpinModel n) :
    AnisotropicObservationState n →L[ℝ] AnisotropicObservationState n :=
  (cavityCouplingDisorderRescaling D).prodMap (ContinuousLinearMap.id ℝ (Field n))

def cavityCouplingPathRescaling (D : AnisotropicSpinModel n)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) : C(Paper.Overlap,AnisotropicParameter n) :=
  ⟨fun r=>anisotropicCouplingRescaling D (Z r),
    (anisotropicCouplingRescaling D).continuous.comp Z.continuous⟩

theorem measurable_cavityCouplingPathRescaling (D : AnisotropicSpinModel n) :
    Measurable (cavityCouplingPathRescaling D) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  exact (anisotropicCouplingRescaling D).measurable.comp (ContinuousMap.measurable_eval r)

theorem cavityCouplingRescaling_disorder (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n):
    anisotropicCouplingRescaling D (anisotropicDisorderInjection n g)=
      anisotropicDisorderInjection n (cavityCouplingDisorderRescaling D g) := by
  ext i
  cases i <;> simp [anisotropicCouplingRescaling,anisotropicDisorderInjection,
    cavityCouplingDisorderRescaling]

theorem cavityCouplingRescaling_unitInput (D : AnisotropicSpinModel n) (x : Field n):
    anisotropicCouplingRescaling D (anisotropicUnitInput D x)=
      anisotropicUnitInput (anisotropicUnitCouplings D) x := by
  unfold anisotropicUnitInput
  simp only [ContinuousLinearMap.comp_apply,anisotropicCouplingRescaling_field]
  rfl

theorem cavityCouplingStartRescaling_parameter (D : AnisotropicSpinModel n)
    (z : AnisotropicObservationState n):
    anisotropicObservationParameter (anisotropicUnitCouplings D)
      (cavityCouplingStartRescaling D z)=
        anisotropicCouplingRescaling D (anisotropicObservationParameter D z) := by
  change anisotropicDisorderInjection n (cavityCouplingDisorderRescaling D z.1)+
    anisotropicUnitInput (anisotropicUnitCouplings D) z.2=_
  rw [anisotropicObservationParameter,map_add,cavityCouplingRescaling_disorder,
    cavityCouplingRescaling_unitInput]

theorem cavityCouplingPathRescaling_reference (D : AnisotropicSpinModel n)
    (q h : Paper.Overlap) (z : AnisotropicObservationState n)
    (sample : VectorDisorderBrownianSample n):
    cavityCouplingPathRescaling D (edgeStoppedReferencePath D z.1 q h z.2 sample)=
      edgeStoppedReferencePath (anisotropicUnitCouplings D)
        (cavityCouplingStartRescaling D z).1 q h
          (cavityCouplingStartRescaling D z).2 sample := by
  apply ContinuousMap.ext
  intro r
  change anisotropicCouplingRescaling D
      (anisotropicDisorderInjection n z.1+anisotropicUnitInput D z.2+
        anisotropicUnitInput D (disorderVectorBrownian
          (((edgeStopOverlap h r:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal sample))=_
  rw [map_add,map_add,cavityCouplingRescaling_disorder,
    cavityCouplingRescaling_unitInput,cavityCouplingRescaling_unitInput]
  rfl

theorem cavityCouplingPathRescaling_action (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)):
    edgeStoppedAction (anisotropicUnitCouplings D) μ q h (cavityCouplingPathRescaling D Z)=
      edgeStoppedAction D μ q h Z := by
  unfold edgeStoppedAction
  apply integral_congr_ae
  filter_upwards with r
  change anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ _
    (anisotropicCouplingRescaling D (Z _))=_
  exact cavityTree_native_tail_unitCouplings D μ _ _

theorem cavityCouplingPathRescaling_logDensity (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)):
    edgePathLogDensity (anisotropicUnitCouplings D) μ q h (cavityCouplingPathRescaling D Z)=
      edgePathLogDensity D μ q h Z := by
  unfold edgePathLogDensity
  rw [cavityCouplingPathRescaling_action]
  change anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ h
    (anisotropicCouplingRescaling D (Z h))-_=_
  rw [cavityTree_native_tail_unitCouplings]

theorem cavityCouplingPathRescaling_endpoint (D : AnisotropicSpinModel n)
    (h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)):
    edgePathEndpoint (anisotropicUnitCouplings D) h (cavityCouplingPathRescaling D Z)=
      cavityCouplingStartRescaling D (edgePathEndpoint D h Z) := by
  change edgeObservationParameterInverse (anisotropicUnitCouplings D)
    (anisotropicCouplingRescaling D (Z h))=_
  apply Prod.ext
  · ext e
    simp [edgeObservationParameterInverse,edgeParameterDisorderProjection,
      cavityCouplingStartRescaling,cavityCouplingDisorderRescaling,
      edgePathEndpoint,anisotropicCouplingRescaling]
  · rfl

end HexagonPaper
