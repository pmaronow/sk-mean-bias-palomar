module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

@[expose] public section

/-! Actual weak continuity of finite Gibbs kernels, and point masses. -/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
open SpinGlass.AT
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [TopologicalSpace S] [OpensMeasurableSpace S]

def finiteStateGibbsProbability (V : S→ℝ) (H : FiniteStateField S) : ProbabilityMeasure S := by
  haveI:=isMarkovKernel_finiteStateGibbsKernel V
  exact (finiteStateGibbsKernel V H).toProbabilityMeasure

theorem continuous_finiteStateGibbsProbability (V : S→ℝ) :
    Continuous (finiteStateGibbsProbability V) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  change Continuous (fun H=>∫σ,f σ ∂finiteStateGibbsKernel V H)
  simp_rw [integral_finiteStateGibbsKernel]
  exact continuous_finset_sum _ fun σ _=>(contDiff_gtStateGibbs V σ).continuous.mul continuous_const

theorem tendsto_dirac_probability {E L : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSingletonClass E] [OpensMeasurableSpace E] {l : Filter L}
    {x : L→E} {y : E} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun j=>(Measure.dirac (x j)).toProbabilityMeasure) l
      (𝓝 (Measure.dirac y).toProbabilityMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun j=>∫v,f v ∂Measure.dirac (x j)) l (𝓝 (∫v,f v ∂Measure.dirac y))
  simp_rw [integral_dirac]
  exact f.continuous.tendsto y |>.comp hx

end FourPapersCommon
