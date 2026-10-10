module
public import QuantitativeFollowup.AnisotropicVarianceDerivative
public import QuantitativeFollowup.AnisotropicMeasureOuterLaw

@[expose] public section

/-! Measurability and depth-independent bounds for the actual covariance
response at a deterministic restart. These are obtained from the genuine
finite Gaussian response and its proved arbitrary-profile limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

theorem measurable_cavityFiniteBinaryGenerator_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j J : ℕ) (K : FiniteStateField (Configuration n)) :
    Measurable (fun H=>cavityFiniteBinaryGenerator D s j J H K) := by
  have hU:=contDiff_two_finiteStateGaussianTerminalCascade
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
  have h1:=(hU.of_le (by norm_num) : ContDiff ℝ 1 _).continuous_fderiv (by norm_num)
  have h2:=(hU.fderiv_right (m:=(1:ℕ∞ω)) (by norm_num)).continuous_fderiv (by norm_num)
  unfold cavityFiniteBinaryGenerator
  apply OverlapPaper.sourceKernelExpectation_measurable
  exact (((h2.clm_apply continuous_const).clm_apply continuous_const).add
    ((h1.clm_apply continuous_const).pow 2 |>.const_mul _ )).measurable

theorem measurable_anisotropicFiniteTailVarianceResponse_parameter
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap) (i : Fin n) :
    Measurable (fun P=>anisotropicFiniteTailVarianceResponse D s q P i) := by
  unfold anisotropicFiniteTailVarianceResponse cavityFiniteNodeBResponse
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_cavityFiniteBinaryGenerator_parameter D
    (vectorClampedScheme s q q.property) j (k+2) (cavityCoordinateFeature i)).comp
      (anisotropicEnergyMap D).continuous.measurable).const_mul _

theorem measurable_anisotropicRestartVarianceResponse_disorder
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (x : Field n) (i : Fin n) :
    Measurable (fun g=>anisotropicRestartVarianceResponse D μ g q x i) := by
  have ht g:=tendsto_anisotropicVarianceFiniteTailResponse D μ i
    (D.variance_pos i) (tendsto_const_nhds (x:=D.variance i)) g q x
  simp only [anisotropicReplaceVariance_self] at ht
  apply measurable_of_tendsto_metrizable _ (tendsto_pi_nhds.mpr ht)
  intro j
  exact (measurable_anisotropicFiniteTailVarianceResponse_parameter D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q i).comp
    ((anisotropicDisorderInjection n).continuous.measurable.add_const _)

theorem anisotropicRestartVarianceResponse_mem_Icc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (i : Fin n) :
    anisotropicRestartVarianceResponse D μ g q x i∈Icc 0 ((1-(q:ℝ))/2) := by
  have ht:=tendsto_anisotropicVarianceFiniteTailResponse D μ i
    (D.variance_pos i) (tendsto_const_nhds (x:=D.variance i)) g q x
  simp only [anisotropicReplaceVariance_self] at ht
  exact isClosed_Icc.mem_of_tendsto ht (.of_forall fun j=>
    anisotropicFiniteTailVarianceResponse_mem_Icc D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q _ i)

theorem norm_anisotropicRestartVarianceResponse_le_half
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (i : Fin n) :
    ‖anisotropicRestartVarianceResponse D μ g q x i‖≤(1/2:ℝ) := by
  have hb:=anisotropicRestartVarianceResponse_mem_Icc D μ g q x i
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  linarith [q.property.1,hb.2]

end QuantitativeFollowup
