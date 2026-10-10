module
public import QuantitativeFollowup.AnisotropicDyadicTail

@[expose] public section

/-! Joint measurability of the actual finite and limiting anisotropic tail
potentials, derived from their Gaussian integral constructions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter QuantitativePaper
open scoped Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000

theorem measurable_anisotropicTailRecursion_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    Measurable (fun z : ℝ×AnisotropicParameter n => anisotropicTailRecursion D s z.1 j z.2) := by
  induction j with
  | zero =>
    exact (anisotropicGridTerminalPotential_lipschitz D).continuous.measurable.comp measurable_snd
  | succ j ih =>
    let v := fun q : ℝ => max q (s.q (k+2-j))-max q (s.q (k+1-j))
    have hs : Measurable (fun z : (ℝ×AnisotropicParameter n)×Field n =>
        (z.1.1,z.1.2+(Real.sqrt (v z.1.1)) • anisotropicUnitInput D z.2)) := by
      dsimp only [v]
      fun_prop
    have hm := ih.comp hs
    by_cases h0 : s.m (k+1-j)=0
    · simpa only [anisotropicTailRecursion,gaussianShiftColeHopf,gaussianShiftAverage,
        h0,ite_true,v,ContinuousLinearMap.smul_apply,Function.comp_def] using
          (hm.stronglyMeasurable.integral_prod_right' (ν:=fieldGaussian n)).measurable
    · have hE := Real.measurable_exp.comp ((measurable_const (a:=s.m (k+1-j))).mul hm)
      have hI := (hE.stronglyMeasurable.integral_prod_right' (ν:=fieldGaussian n)).measurable
      simpa only [anisotropicTailRecursion,gaussianShiftColeHopf,gaussianShiftPartition,
        ite_eq_right h0,v,ContinuousLinearMap.smul_apply,Function.comp_def,Pi.mul_apply] using
          (Real.measurable_log.comp hI).div_const (s.m (k+1-j))

theorem measurable_anisotropicMeasureTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicParameter n => anisotropicMeasureTailPotential D μ z.1 z.2) := by
  apply measurable_of_tendsto_metrizable
    (fun j => (measurable_anisotropicTailRecursion_parameter D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3)).comp
      (measurable_subtype_coe.prodMap measurable_id))
  apply tendsto_pi_nhds.mpr
  intro z
  exact tendsto_anisotropicDyadicTailPotential D μ z.1 z.2

end QuantitativeFollowup
