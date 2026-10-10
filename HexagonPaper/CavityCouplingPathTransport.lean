module
public import HexagonPaper.CavityCouplingPathTransportBasic

@[expose] public section

/-! Actual native complete-edge path kernels commute with unit-coupling
rescaling. The proof transports the genuine affine Wiener reference and
its proved arbitrary-profile RN action; it never defines a physical law
by the desired density. -/
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

theorem cavityCoupling_reference_path_law (D : AnisotropicSpinModel n)
    (q h : Paper.Overlap) (z : AnisotropicObservationState n):
    (edgeReferencePathKernel D q h z).map (cavityCouplingPathRescaling D)=
      edgeReferencePathKernel (anisotropicUnitCouplings D) q h
        (cavityCouplingStartRescaling D z) := by
  rw [edgeReferencePathKernel_apply,Measure.map_map
    (measurable_cavityCouplingPathRescaling D)
    (measurable_edgeStoppedReferencePath D z.1 q h z.2),edgeReferencePathKernel_apply]
  congr 1
  funext sample
  exact cavityCouplingPathRescaling_reference D q h z sample

theorem cavityCoupling_reference_path_kernel (D : AnisotropicSpinModel n)
    (q h : Paper.Overlap):
    (edgeReferencePathKernel D q h).map (cavityCouplingPathRescaling D)=
      (edgeReferencePathKernel (anisotropicUnitCouplings D) q h).comap
        (cavityCouplingStartRescaling D) (cavityCouplingStartRescaling D).measurable := by
  ext z : 1
  rw [Kernel.map_apply _ (measurable_cavityCouplingPathRescaling D),Kernel.comap_apply]
  exact cavityCoupling_reference_path_law D q h z

theorem cavityCoupling_physical_path_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h)
    (z : AnisotropicObservationState n):
    (edgePhysicalPathKernel D μ q h z).map (cavityCouplingPathRescaling D)=
      edgePhysicalPathKernel (anisotropicUnitCouplings D) μ q h
        (cavityCouplingStartRescaling D z) := by
  have hrn (E : AnisotropicSpinModel n) (y : AnisotropicObservationState n):
      edgePhysicalPathKernel E μ q h y=
        (edgeReferencePathKernel E q h y).withDensity (edgeStoppedLikelihood E μ q h) := by
    rw [edgePhysicalPathKernel_apply,edgeReferencePathKernel_apply]
    exact edge_stopped_continuous_path_likelihood_density E μ y.1 q h hqh y.2
  have hw:edgeStoppedLikelihood D μ q h=
      fun Z=>edgeStoppedLikelihood (anisotropicUnitCouplings D) μ q h
        (cavityCouplingPathRescaling D Z):=by
    funext Z
    change ENNReal.ofReal (Real.exp (edgePathLogDensity D μ q h Z))=_
    change _=ENNReal.ofReal (Real.exp
      (edgePathLogDensity (anisotropicUnitCouplings D) μ q h (cavityCouplingPathRescaling D Z)))
    rw [cavityCouplingPathRescaling_logDensity]
  rw [hrn D z,hw,map_withDensity_pullback _ _
    (measurable_cavityCouplingPathRescaling D) _
    (measurable_edgeStoppedLikelihood_path (anisotropicUnitCouplings D) μ q h),
    cavityCoupling_reference_path_law,hrn]

theorem cavityCoupling_physical_path_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h):
    (edgePhysicalPathKernel D μ q h).map (cavityCouplingPathRescaling D)=
      (edgePhysicalPathKernel (anisotropicUnitCouplings D) μ q h).comap
        (cavityCouplingStartRescaling D) (cavityCouplingStartRescaling D).measurable := by
  ext z : 1
  rw [Kernel.map_apply _ (measurable_cavityCouplingPathRescaling D),Kernel.comap_apply]
  exact cavityCoupling_physical_path_law D μ q h hqh z

end HexagonPaper
