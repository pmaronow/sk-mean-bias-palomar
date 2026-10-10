module
public import QuantitativePaper.VectorMeasureKernelMeanBounds
public import QuantitativePaper.VectorMeasureAffineScoreVarianceBound
public import QuantitativePaper.VectorTerminalLinear

@[expose] public section

/-! The literal weighted score is the past-affine terminal-spin score.
Its variance therefore bounds the covariance of the actual kernel mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem vectorMeasureWeightedOverlapScore_eq_affine (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    vectorMeasureWeightedOverlapScore μ s β t ht κ p=
      vectorMeasurePastAffineSpinScore (vectorMeasureKernelMean μ s β t ht κ)
        (vectorMeasureKernelOffset μ s β t ht κ) p := by
  have hi:=integrable_vectorMeasureKernelMean μ s β t ht κ hκ K hK hB p.1
  have ho:=integrable_vectorMeasureKernelOffset μ s β t ht κ hκ K hK hB p.1
  have hlin:=(fieldDotLinear p.2).integral_comp_comm hi
  simp only [fieldDotLinear_apply,map_smul,smul_eq_mul] at hlin
  have hli : Integrable (fun q=>κ q*fieldDot (vectorMeasureSpinMean μ β t ht q p.1) p.2)
      (parisiFreeMeasure μ s) := by
    simpa only [fieldDotLinear_apply,map_smul,smul_eq_mul] using (fieldDotLinear p.2).integrable_comp hi
  unfold vectorMeasureWeightedOverlapScore vectorMeasureOverlapScore normalizedSpinScore
  have halg (q : Paper.Overlap) : κ q*
      ((fieldDot (vectorMeasureSpinMean μ β t ht q p.1) p.2-‖vectorMeasureSpinMean μ β t ht q p.1‖^2/2)/(n:ℝ))=
      (κ q*fieldDot (vectorMeasureSpinMean μ β t ht q p.1) p.2-
        κ q*‖vectorMeasureSpinMean μ β t ht q p.1‖^2/2)/(n:ℝ) := by ring
  simp_rw [halg]
  rw [integral_div,integral_sub hli ho,hlin]
  rfl

theorem vectorMeasureWeightedScore_kernel_covariance_le_variance (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Icc (0:ℝ) 1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀q,|κ q|≤K) (Q : Paper.Overlap)
    (hSupport : ∀ᵐq ∂parisiFreeMeasure μ s,κ q≠0→q≤Q) :
    (∫sample : VectorDisorderBrownianSample n,vectorMeasureCovarianceQuadratic μ β t s ht.le Q sample
      (vectorMeasureKernelMean μ s β t ht.le κ sample) ∂vectorMeasureDisorderTilt μ β t s)/(n:ℝ)^2≤
      variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  have hmean:=adapted_vectorMeasureKernelMean (n:=n) μ s β t ht.le κ hκ Q hSupport
  have hoff:=adapted_vectorMeasureKernelOffset (n:=n) μ s β t ht.le κ hκ Q hSupport
  have hcomp (i : Fin n) : Measurable[vectorBrownianFiltration n (Q:ℝ).toNNReal]
      (fun sample=>vectorMeasureKernelMean μ s β t ht.le κ sample i) :=
    (EuclideanSpace.proj i).continuous.measurable.comp hmean.measurable
  have h:=vectorMeasure_past_affine_score_covariance_le_variance μ β t s hβ ht Q
    (vectorMeasureKernelMean μ s β t ht.le κ) (vectorMeasureKernelOffset μ s β t ht.le κ)
    hcomp hoff.measurable K (K*(n:ℝ)/2) hK
    (fun sample i=>vectorMeasureKernelMean_component_bound μ s β t ht.le hs κ hκ K hK hB sample i)
    (vectorMeasureKernelOffset_bound μ s β t ht.le hs κ hκ K hK hB)
  have he : vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ=
      vectorMeasurePastAffineSpinScore (vectorMeasureKernelMean μ s β t ht.le κ)
        (vectorMeasureKernelOffset μ s β t ht.le κ) := by
    funext p
    exact vectorMeasureWeightedOverlapScore_eq_affine μ s β t ht.le κ hκ K hK hB p
  rw [he]
  exact h

end QuantitativePaper
