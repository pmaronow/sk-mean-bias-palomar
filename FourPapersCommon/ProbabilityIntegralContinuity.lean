module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.CompactOpen

@[expose] public section

/-! Genuine joint continuity of integration against a weakly varying
probability measure and a continuously varying test on a compact space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace FourPapersCommon
variable {K A : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K] [TopologicalSpace A]
set_option maxHeartbeats 1000000

theorem continuousMap_integrable_probability (f : C(K,ℝ)) (μ : ProbabilityMeasure K) :
    Integrable f (μ:Measure K) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ:Measure K)

theorem norm_integral_sub_continuousMap_le (f g : C(K,ℝ)) (μ : ProbabilityMeasure K) :
    ‖(∫x,f x ∂(μ:Measure K))-(∫x,g x ∂(μ:Measure K))‖ ≤ ‖f-g‖ := by
  rw [←integral_sub (continuousMap_integrable_probability f μ) (continuousMap_integrable_probability g μ)]
  exact (BoundedContinuousFunction.mkOfCompact (f-g)).norm_integral_le_norm (μ:Measure K)

theorem continuous_probability_integral_pair :
    Continuous (fun z:C(K,ℝ)×ProbabilityMeasure K=>∫x,z.1 x ∂(z.2:Measure K)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hfixed : Tendsto (fun w:C(K,ℝ)×ProbabilityMeasure K=>∫x,z.1 x ∂(w.2:Measure K))
      (𝓝 z) (𝓝 (∫x,z.1 x ∂(z.2:Measure K))) :=
    ((ProbabilityMeasure.continuous_integral_continuousMap z.1).comp continuous_snd).continuousAt
  have hnorm : Tendsto (fun w:C(K,ℝ)×ProbabilityMeasure K=>‖w.1-z.1‖) (𝓝 z) (𝓝 0) := by
    have H : Continuous (fun w:C(K,ℝ)×ProbabilityMeasure K=>‖w.1-z.1‖) :=
      (continuous_fst.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using (H.continuousAt (x:=z)).tendsto
  have herror : Tendsto (fun w:C(K,ℝ)×ProbabilityMeasure K=>
      (∫x,w.1 x ∂(w.2:Measure K))-(∫x,z.1 x ∂(w.2:Measure K))) (𝓝 z) (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun _=>norm_nonneg _)
      (fun w=>norm_integral_sub_continuousMap_le w.1 z.1 w.2) hnorm
  change Tendsto _ (𝓝 z) (𝓝 (∫x,z.1 x ∂(z.2:Measure K)))
  simpa only [zero_add,sub_add_cancel] using herror.add hfixed

theorem continuous_integral_probability_of_joint (f : A×K→ℝ) (hf : Continuous f) :
    Continuous (fun z:A×ProbabilityMeasure K=>∫x,f (z.1,x) ∂(z.2:Measure K)) := by
  let F : A→C(K,ℝ) := fun a=>⟨fun x=>f (a,x),hf.comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hf
  exact continuous_probability_integral_pair.comp
    ((hF.comp continuous_fst).prodMk continuous_snd)

theorem continuous_integral_probability_family
    (f : A×K→ℝ) (hf : Continuous f) (μ : A→ProbabilityMeasure K) (hμ : Continuous μ) :
    Continuous (fun a=>∫x,f (a,x) ∂(μ a:Measure K)) :=
  (continuous_integral_probability_of_joint f hf).comp (continuous_id.prodMk hμ)

end FourPapersCommon
