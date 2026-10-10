module
public import QuantitativeFollowup.ScalarHessianL1Bound
public import FRSB.GradientTimeLipschitz

@[expose] public section

/-! Joint weak-measure and space-time continuity of the genuine scalar
fields.  Time extensions are the original clamped PDE fields. -/
noncomputable section
open Set Filter Paper FourPapersCommon
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem parisiGradient_clamp_time (β : ℝ) (μ : Paper.ParisiMeasure) (t x : ℝ) :
    parisiGradient β μ (t,x)=parisiGradient β μ
      ((projIcc 0 1 zero_le_one t : ℝ),x) := by
  simp only [parisiGradient,parisiSlabExtend,projIcc_of_mem zero_le_one
    (projIcc 0 1 zero_le_one t).property]

theorem parisiHessian_clamp_time (β : ℝ) (μ : Paper.ParisiMeasure) (t x : ℝ) :
    parisiHessian β μ (t,x)=parisiHessian β μ
      ((projIcc 0 1 zero_le_one t : ℝ),x) := by
  simp only [parisiHessian,parisiGradient_clamp_time β μ t]

theorem parisiHessian_CDF_L1_bound_all (β : ℝ) (hβ : β ≠ 0)
    (μ ν : Paper.ParisiMeasure) (t x : ℝ) :
    ‖parisiHessian β μ (t,x)-parisiHessian β ν (t,x)‖ ≤
      parisiHessianL1Constant β*Paper.parisiCDFDistance μ ν := by
  rw [parisiHessian_clamp_time β μ t,parisiHessian_clamp_time β ν t]
  exact parisiHessian_CDF_L1_bound β hβ μ ν _ (projIcc 0 1 zero_le_one t).property x

theorem continuous_parisiGradient_measure_joint (β : ℝ) :
    Continuous (fun p : Paper.ParisiMeasure×(ℝ×ℝ) => parisiGradient β p.1 p.2) := by
  have hg : Continuous (fun p : Paper.ParisiMeasure×(ℝ×ℝ) => parisiGradientBCF β p.1) :=
    (FRSB.continuous_gradientBCF β).comp continuous_fst
  have ht : Continuous (fun p : Paper.ParisiMeasure×(ℝ×ℝ) => projIcc 0 1 zero_le_one p.2.1) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
    (continuous_fst.comp continuous_snd)
  have hx : Continuous (fun p : Paper.ParisiMeasure×(ℝ×ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact continuous_eval.comp (hg.prodMk (ht.prodMk hx))

theorem continuous_parisiHessian_measure_joint (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun p : Paper.ParisiMeasure×(ℝ×ℝ) => parisiHessian β p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hM : Tendsto (fun z : Paper.ParisiMeasure×(ℝ×ℝ) =>
      Paper.parisiCDFDistance z.1 p.1) (𝓝 p) (𝓝 0) :=
    FRSB.tendsto_parisiCDFDistance_of_tendsto continuous_fst.continuousAt
  have hD : Tendsto (fun z : Paper.ParisiMeasure×(ℝ×ℝ) =>
      dist (parisiHessian β z.1 z.2) (parisiHessian β p.1 z.2)) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun z => ?_)
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := parisiHessianL1Constant β)).mul hM)
    rw [dist_eq_norm]
    exact parisiHessian_CDF_L1_bound_all β hβ z.1 p.1 z.2.1 z.2.2
  exact tendsto_of_tendsto_of_dist
    (((continuous_parisiHessian_all β p.1).comp continuous_snd).continuousAt)
    (by
      convert hD using 1
      funext z
      exact dist_comm _ _)

end QuantitativeFollowup
