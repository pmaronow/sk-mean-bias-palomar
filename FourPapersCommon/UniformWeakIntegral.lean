module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-! Uniformly convergent continuous observables against genuinely weakly
convergent probability measures on a compact space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem tendsto_integral_of_uniform_and_weak {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    (μj : ℕ→ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (hμ : Tendsto μj atTop (nhds μ)) (Fj : ℕ→Ω→ℝ) (F : Ω→ℝ)
    (hFj : ∀j,Continuous (Fj j)) (hF : Continuous F)
    (hU : TendstoUniformly Fj F atTop) :
    Tendsto (fun j=>∫x,Fj j x∂(μj j:Measure Ω)) atTop
      (nhds (∫x,F x∂(μ:Measure Ω))):=by
  let f : Ω →ᵇ ℝ:=BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩
  let fj : ℕ→Ω →ᵇ ℝ:=fun j=>BoundedContinuousFunction.mkOfCompact ⟨Fj j,hFj j⟩
  have he : Tendsto (fun j=>∫x,(Fj j x-F x)∂(μj j:Measure Ω)) atTop (nhds 0):=by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hU) (ε/2) (by linarith)] with j hj
    have hb:=norm_integral_le_of_norm_le_const (μ:=(μj j:Measure Ω)) (C:=ε/2)
      (f:=fun x=>Fj j x-F x)
      (.of_forall fun x=>by simpa only [Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using (hj x).le)
    rw [probReal_univ,mul_one] at hb
    simpa only [dist_zero_right] using hb.trans_lt (by linarith : ε/2<ε)
  have hw:=(ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  have hh:=he.add hw
  change Tendsto (fun j=>(∫x,(Fj j x-F x)∂(μj j:Measure Ω))+
    ∫x,F x∂(μj j:Measure Ω)) atTop (nhds (0+∫x,F x∂(μ:Measure Ω))) at hh
  convert hh using 1
  · funext j
    have hi : Integrable (Fj j) (μj j:Measure Ω):=(fj j).integrable _
    have hi' : Integrable F (μj j:Measure Ω):=f.integrable _
    rw [integral_sub hi hi']
    ring
  · simp

end FourPapersCommon
