module
public import QuantitativeFollowup.AnisotropicProfileGradientStability
public import QuantitativeFollowup.AnisotropicTailContinuity
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Actual anisotropic Hessian stability under arbitrary weak-profile
convergence, uniformly in the restart level and full disorder/field input.
The native third-jet bound is inherited from the genuine dyadic limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem anisotropicMeasureTailSecondDifferential_lipschitz
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  apply le_of_tendsto
    (((anisotropicMeasureTailPotential_hessian_limit D μ q).1.tendsto_at P).dist
      ((anisotropicMeasureTailPotential_hessian_limit D μ q).1.tendsto_at Q))
  refine Eventually.of_forall fun j => ?_
  have hL : LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ q j))) := by
    unfold anisotropicDyadicTailPotential
    rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
    exact anisotropicFinitePotential_secondDifferential_lipschitz D _ _
  exact hL.dist_le_mul P Q

def anisotropicProfileHessianError (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : ℝ :=
  2*(2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2)+
    8*‖anisotropicEnergyMap D‖^3)*Real.sqrt (Real.sqrt (Paper.parisiCDFDistance μ ν))

theorem anisotropicProfileHessianError_nonneg (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : 0 ≤ anisotropicProfileHessianError D μ ν := by
  unfold anisotropicProfileHessianError
  positivity [anisotropicProfileStabilityConstant_nonneg D]

theorem norm_anisotropicMeasureTailSecondDifferential_profile_sub_le
    (D : AnisotropicSpinModel n) (μ ν : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P-
      fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν q)) P‖ ≤
      anisotropicProfileHessianError D μ ν := by
  have hμ := (anisotropicMeasureTailPotential_hessian_limit D μ q).2
  have hν := (anisotropicMeasureTailPotential_hessian_limit D ν q).2
  simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,coe_nnnorm,anisotropicProfileHessianError] using
    norm_fderiv_sub_le_sqrt_Banach
      (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
      (fderiv ℝ (anisotropicMeasureTailPotential D ν q))
      (hμ.fderiv_right (m:=1) (by norm_num)).differentiable_one
      (hν.fderiv_right (m:=1) (by norm_num)).differentiable_one
      (8*‖anisotropicEnergyMap D‖₊^3)
      (anisotropicMeasureTailSecondDifferential_lipschitz D μ q)
      (anisotropicMeasureTailSecondDifferential_lipschitz D ν q)
      (2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2))
      (Real.sqrt (Paper.parisiCDFDistance μ ν))
      (by positivity [anisotropicProfileStabilityConstant_nonneg D]) (Real.sqrt_nonneg _)
      (fun Q => norm_anisotropicMeasureTailDifferential_profile_sub_le D μ ν q Q) P

theorem tendsto_anisotropicProfileHessianError {ι : Type*} {l : Filter ι}
    (D : AnisotropicSpinModel n) (μ : ι→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto (fun j => Paper.parisiCDFDistance (μ j) ν) l (𝓝 0)) :
    Tendsto (fun j => anisotropicProfileHessianError D (μ j) ν) l (𝓝 0) := by
  simpa only [anisotropicProfileHessianError,Real.sqrt_zero,mul_zero] using
    hμ.sqrt.sqrt.const_mul
      (2*(2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2)+
        8*‖anisotropicEnergyMap D‖^3))

theorem tendstoUniformly_anisotropicMeasureTailSecondDifferential_of_CDFDistance
    {ι : Type*} {l : Filter ι} (D : AnisotropicSpinModel n)
    (μ : ι→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto (fun j => Paper.parisiCDFDistance (μ j) ν) l (𝓝 0)) :
    TendstoUniformly
      (fun j => fun z : Paper.Overlap×AnisotropicParameter n =>
        fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) z.1)) z.2)
      (fun z => fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν z.1)) z.2) l := by
  apply (Metric.tendstoUniformly_iff
    (α:=AnisotropicParameter n→L[ℝ]AnisotropicParameter n→L[ℝ]ℝ)).mpr
  intro epsilon hepsilon
  filter_upwards [(tendsto_anisotropicProfileHessianError D μ ν hμ).eventually
    (gt_mem_nhds hepsilon)] with j hj
  intro z
  rw [dist_comm]
  rw [_root_.dist_eq_norm
    (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) z.1)) z.2)
    (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν z.1)) z.2)]
  exact (norm_anisotropicMeasureTailSecondDifferential_profile_sub_le D (μ j) ν z.1 z.2).trans_lt hj

theorem tendstoUniformly_anisotropicMeasureTailSecondDifferential_of_weak
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    (μ : ι→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto μ l (𝓝 ν)) :
    TendstoUniformly
      (fun j => fun z : Paper.Overlap×AnisotropicParameter n =>
        fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) z.1)) z.2)
      (fun z => fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν z.1)) z.2) l :=
  tendstoUniformly_anisotropicMeasureTailSecondDifferential_of_CDFDistance D μ ν
    (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ)

theorem tendsto_anisotropicMeasureTailSecondDifferential_of_weak_moving
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    (μ : ι→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto μ l (𝓝 ν)) (q : ι→Paper.Overlap) (r : Paper.Overlap)
    (hq : Tendsto q l (𝓝 r)) (P : ι→AnisotropicParameter n) (Q : AnisotropicParameter n)
    (hP : Tendsto P l (𝓝 Q)) :
    Tendsto (fun j => fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) (q j))) (P j))
      l (𝓝 (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν r)) Q)) := by
  have hfixed := (continuous_anisotropicMeasureTailSecondDifferential_joint D ν).tendsto (r,Q)
    |>.comp (hq.prodMk_nhds hP)
  have hzero : Tendsto (fun j => dist
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) (q j))) (P j))
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν (q j))) (P j)))
      l (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_anisotropicProfileHessianError D μ ν (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ))
    rw [_root_.dist_eq_norm
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D (μ j) (q j))) (P j))
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D ν (q j))) (P j))]
    exact norm_anisotropicMeasureTailSecondDifferential_profile_sub_le D (μ j) ν (q j) (P j)
  exact tendsto_of_tendsto_of_dist hfixed (by simpa only [dist_comm] using hzero)

end QuantitativeFollowup
