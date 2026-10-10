module
public import QuantitativeFollowup.AnisotropicWhitenedStability
public import QuantitativePaper.VectorMeasureEndpoints

@[expose] public section

/-! Uniform convergence of the actual finite anisotropic Picard states to
 the arbitrary-profile same-driver state. Both the CDF error and the actual
 tail-gradient error tend to zero; no state convergence is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem tendstoUniformlyOn_anisotropicWhitenedFiniteState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformlyOn (fun j=>fun z : ℝ≥0×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
      anisotropicWhitenedFiniteState D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) z.2.1 z.1 z.2.2)
      (fun z=>vectorAdditiveState (anisotropicWhitenedDriftData D μ z.2.1) 1 0 1 z.1 z.2.2)
      atTop (Icc (0 : ℝ≥0) 1×ˢ univ) := by
  let A : ℝ:=‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)
  let B : ℝ:=‖anisotropicNoiseMap D‖
  let C : ℝ:=(A+B)*Real.exp (anisotropicWhitenedDriftLip D)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hB : 0 ≤ B := norm_nonneg _
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hA hB) (Real.exp_pos _).le
  have hD : Tendsto (fun j=>Paper.parisiCDFDistance
      (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))) μ)
      atTop (𝓝 0) := by
    simp only [FRSB.parisiSchemeMeasure_grid_eq]
    have hh:=(Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
    convert hh using 1
    funext j
    exact FRSB.parisiCDFDistance_symm _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let e : ℝ:=ε/(2*(C+1))
  have he : 0 < e := div_pos hε (by positivity)
  have heq : e*(2*(C+1))=ε := by
    dsimp only [e]
    exact div_mul_cancel₀ _ (by positivity)
  have hCe : C*e < ε := by nlinarith
  have hresp := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ)) e he
  filter_upwards [hD.eventually (gt_mem_nhds he),hresp] with j hj hrj
  intro z hz
  rw [dist_comm,dist_eq_norm]
  have hb := anisotropicWhitenedFiniteState_sub_le D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) μ z.2.1 e he.le
    (fun q P=>by
      have hh:=hrj (q,P)
      simpa only [dist_eq_norm,norm_sub_rev] using hh.le) z.1 hz.1.2 z.2.2
  apply hb.trans_lt
  calc
    _ ≤ (A*e+B*e)*Real.exp (anisotropicWhitenedDriftLip D) :=
      mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hj.le hA) le_rfl)
        (Real.exp_pos _).le
    _ = C*e := by dsimp only [C];ring
    _ < ε := hCe

end QuantitativeFollowup
