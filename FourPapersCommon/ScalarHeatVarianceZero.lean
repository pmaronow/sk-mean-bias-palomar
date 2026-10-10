module
public import FRSB.BackwardHeatQuotient
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-! The scalar Gaussian heat derivative at zero variance, from the actual
positive-variance heat equation and its continuous second spatial jet. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 900000

theorem gaussianHeatFlow_zero (F : ℝ→ℝ) (x : ℝ) :
    gaussianHeatFlow F 0 x=F x := by
  simp [gaussianHeatFlow]

theorem hasDerivWithinAt_gaussianHeatFlow_variance_zero {F : ℝ→ℝ}
    (hF : HeatC2Datum F) (x : ℝ) :
    HasDerivWithinAt (fun v=>gaussianHeatFlow F v x)
      ((1/2:ℝ)*iteratedDeriv 2 F x) (Ici (0:ℝ)) 0 := by
  have hc : Continuous (fun v=>gaussianHeatFlow F v x) :=
    (continuous_gaussianHeatFlow hF).comp (continuous_id.prodMk continuous_const)
  have hj : Continuous (fun v=>(1/2:ℝ)*gaussianHeatFlow (iteratedDeriv 2 F) v x) :=
    ((continuous_gaussianHeatFlow_jet hF (j:=2) (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).const_mul _
  have hl : Tendsto (fun v=>(1/2:ℝ)*gaussianHeatFlow (iteratedDeriv 2 F) v x)
      (𝓝[>] (0:ℝ)) (𝓝 ((1/2:ℝ)*iteratedDeriv 2 F x)) := by
    simpa only [gaussianHeatFlow_zero] using
      (hj.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s:=Ioi (0:ℝ))
    (fun v hv=>(hasDerivAt_gaussianHeatFlow_variance hF hv x).differentiableAt.differentiableWithinAt)
    hc.continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (hasDerivAt_gaussianHeatFlow_variance hF hv x).deriv.symm

end FourPapersCommon
