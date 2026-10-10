module
public import HexagonPaper.CavityCouplingPathTransport

@[expose] public section

/-! The reference law under a deterministic coupling offset is the
translated genuine affine Wiener law. The physical law uses the actual
changed native RN weight; a shifted diffusion is not identified with a
translation of the original diffusion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cavityCouplingStartTranslation (h : AnisotropicDisorder n)
    (z : AnisotropicObservationState n) : AnisotropicObservationState n := (z.1+h,z.2)

theorem measurable_cavityCouplingStartTranslation (h : AnisotropicDisorder n):
    Measurable (cavityCouplingStartTranslation h) :=
  (measurable_fst.add_const h).prodMk measurable_snd

def cavityCouplingPathTranslation (h : AnisotropicDisorder n)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) : C(Paper.Overlap,AnisotropicParameter n) :=
  Z+ContinuousMap.const _ (anisotropicDisorderInjection n h)

theorem measurable_cavityCouplingPathTranslation (h : AnisotropicDisorder n):
    Measurable (cavityCouplingPathTranslation h) :=
  (continuous_id.add continuous_const).measurable

theorem cavityCouplingStartTranslation_parameter (D : AnisotropicSpinModel n)
    (h : AnisotropicDisorder n) (z : AnisotropicObservationState n):
    anisotropicObservationParameter D (cavityCouplingStartTranslation h z)=
      anisotropicObservationParameter D z+anisotropicDisorderInjection n h := by
  simp only [anisotropicObservationParameter,cavityCouplingStartTranslation,map_add]
  abel

theorem cavityCouplingPathTranslation_reference (D : AnisotropicSpinModel n)
    (q r : Paper.Overlap) (h : AnisotropicDisorder n) (z : AnisotropicObservationState n)
    (sample : VectorDisorderBrownianSample n):
    cavityCouplingPathTranslation h (edgeStoppedReferencePath D z.1 q r z.2 sample)=
      edgeStoppedReferencePath D (cavityCouplingStartTranslation h z).1 q r
        (cavityCouplingStartTranslation h z).2 sample := by
  apply ContinuousMap.ext
  intro t
  change (anisotropicDisorderInjection n z.1+anisotropicUnitInput D z.2+
    anisotropicUnitInput D (disorderVectorBrownian
      (((edgeStopOverlap r t:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal sample))+
    anisotropicDisorderInjection n h=
    anisotropicDisorderInjection n (z.1+h)+anisotropicUnitInput D z.2+
    anisotropicUnitInput D (disorderVectorBrownian
      (((edgeStopOverlap r t:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal sample)
  rw [map_add]
  abel

theorem cavityCouplingPathTranslation_endpoint (D : AnisotropicSpinModel n)
    (r : Paper.Overlap) (h : AnisotropicDisorder n)
    (Z : C(Paper.Overlap,AnisotropicParameter n)):
    edgePathEndpoint D r (cavityCouplingPathTranslation h Z)=
      cavityCouplingStartTranslation h (edgePathEndpoint D r Z) := by
  unfold edgePathEndpoint cavityCouplingPathTranslation
  change edgeObservationParameterInverse D (Z r+anisotropicDisorderInjection n h)=_
  rw [map_add]
  have hi:edgeObservationParameterInverse D (anisotropicDisorderInjection n h)=(h,0):=by
    simpa only [map_zero,add_zero] using edgeObservationParameterInverse_apply D h 0
  rw [hi]
  apply Prod.ext
  · rfl
  · exact add_zero _

theorem cavityCoupling_reference_path_translation_law (D : AnisotropicSpinModel n)
    (q r : Paper.Overlap) (h : AnisotropicDisorder n) (z : AnisotropicObservationState n):
    (edgeReferencePathKernel D q r z).map (cavityCouplingPathTranslation h)=
      edgeReferencePathKernel D q r (cavityCouplingStartTranslation h z) := by
  rw [edgeReferencePathKernel_apply,Measure.map_map
    (measurable_cavityCouplingPathTranslation h)
    (measurable_edgeStoppedReferencePath D z.1 q r z.2),edgeReferencePathKernel_apply]
  congr 1
  funext sample
  exact cavityCouplingPathTranslation_reference D q r h z sample

theorem cavityCoupling_reference_path_translation_kernel (D : AnisotropicSpinModel n)
    (q r : Paper.Overlap) (h : AnisotropicDisorder n):
    (edgeReferencePathKernel D q r).map (cavityCouplingPathTranslation h)=
      (edgeReferencePathKernel D q r).comap
        (cavityCouplingStartTranslation h) (measurable_cavityCouplingStartTranslation h) := by
  ext z : 1
  rw [Kernel.map_apply _ (measurable_cavityCouplingPathTranslation h),Kernel.comap_apply]
  exact cavityCoupling_reference_path_translation_law D q r h z

theorem cavityCoupling_shifted_physical_path_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (h : AnisotropicDisorder n) (z : AnisotropicObservationState n):
    edgePhysicalPathKernel D μ q r (cavityCouplingStartTranslation h z)=
      ((edgeReferencePathKernel D q r z).withDensity
        (fun Z=>edgeStoppedLikelihood D μ q r (cavityCouplingPathTranslation h Z))).map
          (cavityCouplingPathTranslation h) := by
  rw [map_withDensity_pullback _ _ (measurable_cavityCouplingPathTranslation h) _
    (measurable_edgeStoppedLikelihood_path D μ q r),
    cavityCoupling_reference_path_translation_law,
    edgePhysicalPathKernel_apply,edgeReferencePathKernel_apply]
  exact edge_stopped_continuous_path_likelihood_density D μ _ q r hqr _

end HexagonPaper
