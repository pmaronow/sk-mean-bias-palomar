module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfilePenaltyValues
public import QuantitativeFollowup.FollowupCavityRemainderIntegral

@[expose] public section

/-! Atom-preserving passage of the actual strict-future remainder.
The two free-measure integrations are one literal product-measure
integral; no conditional covariance or convergence identity is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

private theorem responseRemainder_eq_product (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    cavityResponseFutureRemainder β D μ a p=
      -(∫z : Paper.Overlap×Paper.Overlap,
        cavityScalarFutureCovariance β μ z.1 p z.2*cavityRestResidualCovariance D μ a z.1 p z.2
          ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
  have hmap : Measurable (fun z : Paper.Overlap×Paper.Overlap=>(z.1,(p,z.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hm := ((measurable_cavityScalarFutureCovariance β μ).comp hmap).mul
    ((measurable_cavityRestResidualCovariance D μ a).comp hmap)
  have hi : Integrable (fun z : Paper.Overlap×Paper.Overlap=>
      cavityScalarFutureCovariance β μ z.1 p z.2*cavityRestResidualCovariance D μ a z.1 p z.2)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
    apply (integrable_const 1).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      dsimp only [Function.comp_def,Pi.mul_apply]
      rw [norm_mul]
      exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ _ _ _)
        (cavityRestResidualCovariance_norm_le D μ a _ _ _) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  rw [cavityResponseFutureRemainder_eq_residual_integral β hβ D μ a p]
  exact congrArg Neg.neg (integral_prod _ hi).symm

theorem tendsto_cavityResponseFutureRemainder_preserving (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S) (p : Paper.Overlap) (hp : p∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) :
    Tendsto (fun N=>cavityResponseFutureRemainder β D (FRSB.preservingMeasure μ S N) a p)
      atTop (𝓝 (cavityResponseFutureRemainder β D μ a p)) := by
  simp_rw [responseRemainder_eq_product β hβ]
  apply Tendsto.neg
  refine nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hfloor _ _ ?_
    1 (by norm_num) ?_ ?_
  · intro N
    have hmap : Measurable (fun z : Paper.Overlap×Paper.Overlap=>(z.1,(p,z.2))) :=
      measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
    exact ((measurable_cavityScalarFutureCovariance β _).comp hmap).mul
      ((measurable_cavityRestResidualCovariance D _ a).comp hmap)
  · intro N z
    rw [←Real.norm_eq_abs,norm_mul]
    exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β _ _ _ _)
      (cavityRestResidualCovariance_norm_le D _ a _ _ _) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro r l
    have ht := (tendsto_cavityScalarFutureCovariance_preserving β μ S r p l).mul
      (tendsto_cavityRestResidualCovariance_preserving D μ S a r p l)
    simpa only [FRSB.preservingRound_fixed S _ p hp] using ht

end QuantitativeFollowup
