module
public import QuantitativeFollowup.FollowupCavitySignedResponseScorePairing

@[expose] public section

/-! Joint measurability of the actual signed residuals and their deterministic
kernel averages, including the strict-future Stieltjes cutoff. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem measurable_joint_cavitySignedResponseTerminalResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      cavitySignedResponseTerminalResidual D μ z.1 z.2) := by
  have hmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hm (i : Fin n) : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      anisotropicProcessSpinResponse D μ z.1 i z.2.1) :=
    (EuclideanSpace.proj i).continuous.measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hmap)
  exact (Finset.measurable_sum _ (fun i _ => (hm i).mul
    (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp
      measurable_snd.snd).sub (hm i)))).div_const _

theorem measurable_joint_cavitySignedResponseMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      cavitySignedResponseMeanResidual D μ z.1 z.2.1 z.2.2) := by
  have hrmap : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      (z.1,z.2.2)) := measurable_fst.prodMk measurable_snd.snd
  have hlmap : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      (z.2.1,z.2.2)) := measurable_snd
  have hr (i : Fin n) := (EuclideanSpace.proj i).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hrmap)
  have hl (i : Fin n) := (EuclideanSpace.proj i).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hlmap)
  exact (Finset.measurable_sum _ (fun i _ => (hr i).mul ((hl i).sub (hr i)))).div_const _

theorem measurable_joint_cavitySignedResponseIntegratedFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseIntegratedFutureResidual D μ a z.1 z.2) := by
  have hmap : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      (z.2.1,(z.1,z.2.2))) := measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  have hm : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      if z.2.1<z.1 then cavitySignedResponseMeanResidual D μ z.2.1 z.1 z.2.2 else (0:ℝ)) :=
    ((measurable_joint_cavitySignedResponseMeanResidual D μ).comp hmap).ite
      (measurableSet_lt measurable_snd.fst measurable_fst) measurable_const
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := parisiFreeMeasure μ a)).measurable

theorem measurable_joint_cavitySignedResponseScore (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      cavitySignedResponseScore D μ a z.1 z.2) := by
  have hmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n) =>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  exact (measurable_joint_cavitySignedResponseTerminalResidual D μ).sub
    ((measurable_joint_cavitySignedResponseIntegratedFutureResidual D μ a).comp hmap)

theorem measurable_joint_anisotropicWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n))
    (K : Paper.Overlap→Paper.Overlap→ℝ) (hK : Measurable (Function.uncurry K)) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicWeightedSelfOverlap D μ a (K z.1) J z.2) := by
  have hKmap : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      (z.2.1,z.1)) := measurable_snd.fst.prodMk measurable_fst
  have hMmap : Measurable (fun z : Paper.Overlap×(Paper.Overlap×AnisotropicDisorderBrownianSample n) =>
      (z.1,z.2.2)) := measurable_fst.prodMk measurable_snd.snd
  have hm := (hK.comp hKmap).mul
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hMmap))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := parisiFreeMeasure μ a)).measurable

end QuantitativeFollowup
