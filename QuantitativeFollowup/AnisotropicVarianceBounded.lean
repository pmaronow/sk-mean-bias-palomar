module
public import QuantitativeFollowup.AnisotropicVarianceContinuous
public import QuantitativeFollowup.AnisotropicKernelLimits
public import FourPapersCommon.BoundedContinuousApproximation

@[expose] public section

/-! The actual arbitrary-profile anisotropic variance bound extends to
bounded Borel signed kernels by true continuous L2 density and dominated passage. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropic_weighted_selfOverlap_variance_bounded (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a)≤
      ∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  obtain ⟨κj,hcont,hbound,hlim⟩:=exists_continuous_bounded_ae_approximation
    (parisiFreeMeasure μ a) κ hκ K hK hb
  have hV:=tendsto_variance_anisotropicWeightedSelfOverlap_kernel D μ a κj κ (fun _=>K)
    (fun j=>(hcont j).measurable) hκ (integrable_const K) (fun _=>hK) hbound hb hlim J
  have hE:=tendsto_integral_anisotropicWeightedProcessHessianEnergy_kernel D μ a κj κ (fun _=>K)
    (fun j=>(hcont j).measurable) (integrable_const (K^2)) hbound hlim J
  apply le_of_tendsto_of_tendsto hV hE
  exact .of_forall fun j=>anisotropic_weighted_selfOverlap_variance_continuous D μ a ha hμ
    (κj j) (hcont j) J hJ K hK (hbound j)

end QuantitativeFollowup
