module
public import QuantitativeFollowup.FollowupCavityRestCovariance
public import QuantitativeFollowup.ScalarResponseL2Operator

@[expose] public section

/-! The literal scalar-response/covariance trace pairing, evaluated on
the actual centered rest diffusion process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def cavityRestResponseTrace (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) : ℝ:=
  ∫ω,inner ℝ (cavityRestEndpointProcess D μ a ω)
    (scalarResponseL2Operator β hβ μ a ha hμ (cavityRestEndpointProcess D μ a ω))
    ∂anisotropicMeasureSampleLaw D μ a

theorem cavityRestResponseTrace_hasSum (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ (endpointFixedL2 (parisiFreeMeasure μ a))) :
    HasSum (fun i=>inner ℝ
      (scalarResponseL2Operator β hβ μ a ha hμ (cavityRestCovariance D μ a (b i))) (b i))
      (cavityRestResponseTrace D β hβ μ a ha hμ) :=
  overlapProcessCovariance_hasSum_comp_diagonal _ _ _
    (measurable_cavityRestOverlapPath D μ) 1 (by norm_num)
    (cavityRestOverlapPath_norm_le D μ) b _

theorem cavityRestResponseTrace_eq_tsum (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ (endpointFixedL2 (parisiFreeMeasure μ a))) :
    cavityRestResponseTrace D β hβ μ a ha hμ=
      ∑'i,inner ℝ
        (scalarResponseL2Operator β hβ μ a ha hμ (cavityRestCovariance D μ a (b i))) (b i) :=
  (cavityRestResponseTrace_hasSum D β hβ μ a ha hμ b).tsum_eq.symm

theorem cavityRestResponseTrace_abs_le (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    |cavityRestResponseTrace D β hβ μ a ha hμ|≤
      ‖scalarResponseL2Operator β hβ μ a ha hμ‖*cavityRestVariance D μ a := by
  let J:=scalarResponseL2Operator β hβ μ a ha hμ
  let X:=cavityRestEndpointProcess D μ a
  have hi := (memLp_cavityRestEndpointProcess D μ a).integrable_norm_pow
    (by norm_num : (2:ℕ)≠0)
  have hb (ω : AnisotropicDisorderBrownianSample n) :
      ‖inner ℝ (X ω) (J (X ω))‖≤‖J‖*‖X ω‖^2 := by
    calc
      _≤‖X ω‖*‖J (X ω)‖ := norm_inner_le_norm _ _
      _≤‖X ω‖*(‖J‖*‖X ω‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _=‖J‖*‖X ω‖^2 := by ring
  have hh := norm_integral_le_of_norm_le (hi.const_mul ‖J‖) (.of_forall hb)
  change |cavityRestResponseTrace D β hβ μ a ha hμ|≤‖J‖*cavityRestVariance D μ a
  simpa only [Real.norm_eq_abs,integral_const_mul,
    ←cavityRestVariance_eq_integral_norm_sq D μ a hone,cavityRestResponseTrace,J,X] using hh

end QuantitativeFollowup
