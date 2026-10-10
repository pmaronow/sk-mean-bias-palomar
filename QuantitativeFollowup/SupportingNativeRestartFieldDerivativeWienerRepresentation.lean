module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeWienerScore
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeScoreIntegral
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNodeHessian

@[expose] public section

/-! Literal physical magnetization/Hessian representation of the true
finite Wiener response, with the terminal mark integrated by its actual
Gibbs kernel. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

def cavityRestartFieldHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (r : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (i : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ r))
    (anisotropicRestartPhysicalParameter D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample)
    (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i)

def cavityRestartSquareFieldResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (r : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (i : Fin n) : ℝ :=
  2*cavityRestartSpinVector D μ g q x sample r i*cavityRestartFieldHessian D μ g q x w r sample i+
  (cavityRestartSpinVector D μ g q x sample r i)^2*
    (inner ℝ w (cavityRestartSpinVector D μ g q x sample 1-
      cavityRestartSpinVector D μ g q x sample q)-
      ∫u,cavityRestartStrictFutureResidual D μ g q x w sample u ∂(μ:Measure Paper.Overlap))

theorem integral_anisotropicFiniteRestartSpinKernel_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    (∫σ,fieldDot w σ ∂anisotropicFiniteRestartSpinKernel D s g q (anisotropicInverseNoiseMap D x) sample)=
      inner ℝ w (cavityRestartSpinVector D (Paper.parisiSchemeMeasure s) g q x sample 1) := by
  have h:=cascadePosteriorRecordedMean_anisotropic_restart_node D s g q
    (anisotropicInverseNoiseMap D x) w (k+2) le_rfl sample
  rw [←cavityRestartSpinVector_scheme_node D s g q x (k+2) le_rfl sample,
    show anisotropicSchemeNode s (k+2) le_rfl=1 from Subtype.ext s.q_top,max_eq_right (show q≤(1:Paper.Overlap) from q.property.2)] at h
  rw [real_inner_comm] at h
  rw [←h]
  unfold cascadePosteriorRecordedMean
  rw [Nat.sub_self,fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg _)]
  simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,OverlapPaper.sourceKernelLaw,
    Kernel.comp_id,anisotropicEnergyMap_field,anisotropicFiniteRestartSpinKernel,Kernel.comap_apply,
    historyExtended,show Fin.ofNat (k+3) (k+2)=Fin.last (k+2) from Fin.ext (Nat.mod_eq_of_lt (by omega))]

theorem cavityRestartFieldHessian_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (hv : v≤k+2) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    cavityRestartFieldHessian D (Paper.parisiSchemeMeasure s) g q x w
      (max q (anisotropicSchemeNode s v hv)) sample i=
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s (max q (anisotropicSchemeNode s v hv))))
        (anisotropicFiniteRestartPhysicalParameter D s g q (anisotropicInverseNoiseMap D x)
          (anisotropicRestartElapsed s q v) sample)
        (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i) := by
  have he : anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s)
      (max q (anisotropicSchemeNode s v hv))=
      anisotropicFiniteTailPotential D s (max q (anisotropicSchemeNode s v hv)) :=
    funext fun P=>anisotropicMeasureTailPotential_scheme_eq_finite D s _ P
  unfold cavityRestartFieldHessian anisotropicRestartPhysicalParameter
  rw [he,anisotropicRestartState_scheme_eq_finite]
  rfl

theorem anisotropicFiniteRestartWienerSquareResponse_eq_physical (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (hv : v≤k+2) (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    anisotropicFiniteRestartWienerSquareResponse D s g q x w v i sample=
      cavityRestartSquareFieldResponse D (Paper.parisiSchemeMeasure s) g q x w
        (max q (anisotropicSchemeNode s v hv)) sample i := by
  let M:=cavityRestartSpinVector D (Paper.parisiSchemeMeasure s) g q x sample
  let R:=max q (anisotropicSchemeNode s v hv)
  let H:=cavityRestartFieldHessian D (Paper.parisiSchemeMeasure s) g q x w R sample i
  let B:=inner ℝ w (M q)+∫u,cavityRestartStrictFutureResidual D
    (Paper.parisiSchemeMeasure s) g q x w sample u ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap)
  have hK : cavityCoordinateFeature i=anisotropicEnergyMap D (anisotropicFieldInjection n (EuclideanSpace.single i 1)) :=
    (anisotropicEnergyMap_coordinateFeature D i).symm
  have hm:=cascadePosteriorRecordedMean_anisotropic_restart_node D s g q
    (anisotropicInverseNoiseMap D x) (EuclideanSpace.single i 1) v hv sample
  rw [←hK,←cavityRestartSpinVector_scheme_node D s g q x v hv sample,
    EuclideanSpace.inner_single_right] at hm
  simp only [one_mul,starRingEnd_apply,star_trivial] at hm
  have hH:=anisotropicFiniteCascade_second_restart_node D s g q (anisotropicInverseNoiseMap D x) w v hv i sample
  rw [←cavityRestartFieldHessian_scheme_node D s g q x w v hv sample i] at hH
  have hF : (fun σ=>cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+1) v (cavityCoordinateFeature i) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
      (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) sample,σ))=
      fun σ=>2*M R i*H+(M R i)^2*(fieldDot w σ-B) := by
    funext σ
    unfold cascadePosteriorRecordedSquareResponse
    rw [hm,hH,cascadePosteriorRecordedScore_anisotropic_residual D s g q x w (sample,σ)]
    dsimp only [M,R,H,B]
    ring
  have hi (f : Configuration n→ℝ) : Integrable f
      (anisotropicFiniteRestartSpinKernel D s g q (anisotropicInverseNoiseMap D x) sample) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  unfold anisotropicFiniteRestartWienerSquareResponse
  rw [hF,integral_add (integrable_const _) (hi _),
    integral_const,integral_const_mul,integral_sub (hi _) (integrable_const _),
    integral_const,integral_anisotropicFiniteRestartSpinKernel_field]
  simp only [probReal_univ,one_smul]
  unfold cavityRestartSquareFieldResponse
  dsimp only [M,R,H,B]
  rw [inner_sub_right]
  ring

end QuantitativeFollowup
