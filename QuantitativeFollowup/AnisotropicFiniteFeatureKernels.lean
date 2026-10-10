module
public import QuantitativeFollowup.AnisotropicFiniteFuturePairing
public import QuantitativeFollowup.AnisotropicPairResponses
public import FourPapersCommon.FiniteStateCascadeGibbsTransport

@[expose] public section

/-! All terminal-spin features are transported by the actual anisotropic
normalized diffusion kernels, including zero masses and repeated levels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper OverlapPaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def anisotropicFiniteFeatureMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (f : QuantitativePaper.Configuration n→ℝ) (P : AnisotropicParameter n) : ℝ :=
  ∫σ,f σ ∂anisotropicFiniteSpinKernel D s j P

theorem measurable_anisotropicFiniteFeatureMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (f : QuantitativePaper.Configuration n→ℝ) : Measurable (anisotropicFiniteFeatureMean D s j f) :=
  (measurable_of_finite f).stronglyMeasurable.integral_kernel.measurable

theorem anisotropicFiniteFeatureMean_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (f : QuantitativePaper.Configuration n→ℝ) (B : ℝ) (hb : ∀σ,‖f σ‖≤B) (P : AnisotropicParameter n) :
    ‖anisotropicFiniteFeatureMean D s j f P‖≤B := by
  simpa only [anisotropicFiniteFeatureMean,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=anisotropicFiniteSpinKernel D s j P) (.of_forall hb))

theorem anisotropicFinitePotential_eq_parameterCascade (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    anisotropicFinitePotential D s j=
      finiteStateGaussianCascade (anisotropicSchemeMass s) (anisotropicSchemeInput D s)
        (fun P=>gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicEnergyMap D P)) j := by
  funext P
  exact finiteStateGaussianCascade_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) (anisotropicSchemeMass s) _ j P

theorem anisotropicDepthKernel_eq_parameterCascadeKernel (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    anisotropicDepthKernel D s=
      finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (anisotropicSchemeInput D s)
        (fun P=>gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicEnergyMap D P)) := by
  funext j
  unfold anisotropicDepthKernel finiteStateGaussianCascadeKernel
  rw [anisotropicFinitePotential_eq_parameterCascade]

theorem anisotropicFiniteFeatureMean_eq_futureKernels (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (f : QuantitativePaper.Configuration n→ℝ) (P : AnisotropicParameter n) :
    anisotropicFiniteFeatureMean D s j f P=
      sourceKernelExpectation (anisotropicDepthKernel D s) j (anisotropicFiniteFeatureMean D s 0 f) P := by
  have ht := integral_finiteStateCascadeGibbsKernel_comp_linear (fun _ : QuantitativePaper.Configuration n=>0) f
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) j P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel] at ht
  have hf : (fun y=>∫σ,f σ ∂finiteStateGibbsKernel (fun _ : QuantitativePaper.Configuration n=>0)
      (anisotropicEnergyMap D y))=anisotropicFiniteFeatureMean D s 0 f := by
    funext y
    simp only [anisotropicFiniteFeatureMean,anisotropicFiniteSpinKernel,Kernel.comap_apply,
      finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,Kernel.comp_id]
  rw [hf] at ht
  simpa only [anisotropicFiniteFeatureMean,anisotropicFiniteSpinKernel,Kernel.comap_apply,
    finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,Kernel.comp_id] using ht

theorem anisotropicFiniteFutureExpectation_terminalFeature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (f : QuantitativePaper.Configuration n→ℝ) (P : AnisotropicParameter n) :
    anisotropicFiniteFutureExpectation D s i (k+2) (anisotropicFiniteFeatureMean D s 0 f) P=
      anisotropicFiniteFeatureMean D s (k+2-i) f P := by
  rw [anisotropicFiniteFeatureMean_eq_futureKernels]
  simp only [anisotropicFiniteFutureExpectation,Nat.sub_self,zero_add]

theorem anisotropicFinite_terminalFeature_weighted_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i≤k+2)
    (f : QuantitativePaper.Configuration n→ℝ) (B : ℝ) (hb : ∀σ,‖f σ‖≤B)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p,Z p*anisotropicFiniteFeatureMean D s 0 f
      (anisotropicFinitePhysicalParameter D s g 1 p) ∂vectorDisorderBrownianMeasure n)=
      ∫p,Z p*anisotropicFiniteFeatureMean D s (k+2-i) f
        (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p)
        ∂vectorDisorderBrownianMeasure n := by
  have h := anisotropicFinite_future_integrable_weighted_pairing D s g i (k+2) hi le_rfl
    (anisotropicFiniteFeatureMean D s 0 f) (measurable_anisotropicFiniteFeatureMean D s 0 f)
    B (anisotropicFiniteFeatureMean_bound D s 0 f B hb) Z hZ hZi
  simpa only [s.q_top,Real.toNNReal_one,anisotropicFiniteFutureExpectation_terminalFeature] using h

end QuantitativeFollowup
