module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Genuine dominated convergence of variance for uniformly bounded
real observables on a fixed probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem tendsto_variance_of_uniform_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Fj : ℕ→Ω→ℝ) (F : Ω→ℝ)
    (hFj : ∀j,Measurable (Fj j)) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hB : ∀j x,‖Fj j x‖≤C) (hBF : ∀x,‖F x‖≤C)
    (hlim : ∀ᵐx ∂P,Tendsto (fun j=>Fj j x) atTop (𝓝 (F x))) :
    Tendsto (fun j=>variance (Fj j) P) atTop (𝓝 (variance F P)) := by
  have he : Tendsto (fun j=>∫x,Fj j x ∂P) atTop (𝓝 (∫x,F x ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _=>C) (fun j=>(hFj j).aestronglyMeasurable)
      (integrable_const _) (fun j=>.of_forall (hB j)) hlim
  have hs : Tendsto (fun j=>∫x,(Fj j x)^2 ∂P) atTop (𝓝 (∫x,(F x)^2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _=>C^2)
    · exact fun j=>((hFj j).pow_const 2).aestronglyMeasurable
    · exact integrable_const _
    · exact fun j=>.of_forall fun x=>by
        simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hB j x) 2
    · exact hlim.mono fun x hx=>hx.pow 2
  have hMj (j : ℕ) : MemLp (Fj j) 2 P:=MemLp.of_bound (hFj j).aestronglyMeasurable C (.of_forall (hB j))
  have hM : MemLp F 2 P:=MemLp.of_bound hF.aestronglyMeasurable C (.of_forall hBF)
  simpa only [variance_eq_sub (hMj _),variance_eq_sub hM,Pi.pow_apply] using hs.sub (he.pow 2)

end FourPapersCommon
