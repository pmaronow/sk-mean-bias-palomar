module
public import FourPapersCommon.GenericFiniteStateCascadeTimeContinuity

@[expose] public section

/-! Preservation of genuine time/spatial regularity through an actual Gaussian
step. Induction on these data discharges the varying-prior cascade calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem continuousOn_of_partial_derivatives
    (F T : ℝ → FiniteStateField S → ℝ)
    (hT : ContinuousOn (fun p : ℝ×FiniteStateField S => T p.1 p.2) (finiteStateGaussianTimeDomain S))
    (hX : ContinuousOn (fun p : ℝ×FiniteStateField S => fderiv ℝ (F p.1) p.2) (finiteStateGaussianTimeDomain S))
    (hdT : ∀ t ∈ Ioo 0 1, ∀ H, HasDerivAt (fun u => F u H) (T t H) t)
    (hdX : ∀ t ∈ Ioo 0 1, Differentiable ℝ (F t)) :
    ContinuousOn (fun p : ℝ×FiniteStateField S => F p.1 p.2) (finiteStateGaussianTimeDomain S) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hn : ∀ᶠ q : ℝ×FiniteStateField S in 𝓝 p, q.1 ∈ Ioo 0 1 := by
    filter_upwards [isOpen_finiteStateGaussianTimeDomain.mem_nhds hp] with q hq
    exact hq.1
  have h1 : ∀ᶠ q : ℝ×FiniteStateField S in 𝓝 p,
      HasFDerivAt (fun u => F u q.2) (ContinuousLinearMap.toSpanSingleton ℝ (T q.1 q.2)) q.1 := by
    filter_upwards [hn] with q hq
    exact (hdT q.1 hq q.2).hasFDerivAt
  have h2 : ∀ᶠ q : ℝ×FiniteStateField S in 𝓝 p,
      HasFDerivAt (F q.1) (fderiv ℝ (F q.1) q.2) q.2 := by
    filter_upwards [hn] with q hq
    exact (hdX q.1 hq).differentiableAt.hasFDerivAt
  have hc1 : ContinuousAt (fun q : ℝ×FiniteStateField S =>
      ContinuousLinearMap.toSpanSingleton ℝ (T q.1 q.2)) p :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
      (hT.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hp))
  exact (hasStrictFDerivAt_uncurry_coprod (f := F)
    (f₁ := fun u H => ContinuousLinearMap.toSpanSingleton ℝ (T u H))
    (f₂ := fun u H => fderiv ℝ (F u) H) h1 h2 hc1
    (hX.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hp))).continuousAt

def finiteStateGaussianTimeStep
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (ha : 0 ≤ a) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    FiniteStateGaussianTimeData
      (fun t H => finiteStateGaussianStep a (Real.sqrt (1-t) • L) (F t) H)
      C (B+2*Real.toNNReal a*C^2) (K+finiteStateGaussianGeneratorBound a L C B) := by
  let U := fun t H => finiteStateGaussianStep a (Real.sqrt (1-t) • L) (F t) H
  let T := fun t H => finiteStateGaussianPriorTimeMean d a L t H-
    finiteStateGaussianVarianceGenerator a (1-t) L (F t) H
  have hSpatial (t : ℝ) (ht : t ∈ Ioo 0 1) : ContDiff ℝ 2 (U t) :=
    contDiff_two_finiteStateGaussianStep a _ (F t) (d.spatial_C2 t ht) C B
      (d.first_bound t ht) (d.second_bound t ht)
  have hFirst (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
      fderiv ℝ (U t) H = finiteStateGaussianDifferential a (Real.sqrt (1-t) • L) (F t) H :=
    (hasFDerivAt_finiteStateGaussianStep a _ (F t) ((d.spatial_C2 t ht).of_le (by norm_num))
      C (d.first_bound t ht) H).fderiv
  have hSecond (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
      fderiv ℝ (fderiv ℝ (U t)) H = finiteStateGaussianHessian a (Real.sqrt (1-t) • L) (F t) H := by
    rw [show fderiv ℝ (U t) = finiteStateGaussianDifferential a (Real.sqrt (1-t) • L) (F t)
      from funext (hFirst t ht)]
    exact (hasFDerivAt_finiteStateGaussianDifferential a _ (F t) (d.spatial_C2 t ht) C B
      (d.first_bound t ht) (d.second_bound t ht) H).fderiv
  have hcFirst : ContinuousOn (fun p : ℝ×FiniteStateField S => fderiv ℝ (U p.1) p.2)
      (finiteStateGaussianTimeDomain S) :=
    (continuousOn_finiteStateGaussian_family_differential d a L).congr (fun p hp => hFirst p.1 hp.1 p.2)
  have hcSecond : ContinuousOn (fun p : ℝ×FiniteStateField S => fderiv ℝ (fderiv ℝ (U p.1)) p.2)
      (finiteStateGaussianTimeDomain S) :=
    (continuousOn_finiteStateGaussian_family_hessian d a L).congr (fun p hp => hSecond p.1 hp.1 p.2)
  have hcTime : ContinuousOn (fun p : ℝ×FiniteStateField S => T p.1 p.2)
      (finiteStateGaussianTimeDomain S) :=
    (continuousOn_finiteStateGaussianPriorTimeMean d a L).sub
      (continuousOn_finiteStateGaussian_family_varianceGenerator d a L)
  have hdTime (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
      HasDerivAt (fun u => U u H) (T t H) t := hasDerivAt_finiteStateGaussianStep_time d a L t ht H
  refine {
    time := T, cont := continuousOn_of_partial_derivatives U T hcTime hcFirst hdTime
      (fun t ht => (hSpatial t ht).differentiable (by norm_num)),
    first_cont := hcFirst, second_cont := hcSecond, spatial_C2 := hSpatial,
    first_bound := ?_, second_bound := ?_, time_cont := hcTime, time_hasDeriv := hdTime,
    time_bound := ?_ }
  · intro t ht H
    exact norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianStep_lipschitz (F t) (d.lipschitz t ht) a ha _)
  · intro t ht H
    rw [hSecond t ht H]
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow,
      Real.coe_toNNReal _ ha] using norm_finiteStateGaussianHessian_le a ha _ (F t)
        (d.spatial_C2 t ht) C B (d.first_bound t ht) (d.second_bound t ht) H
  · intro t ht H
    exact (abs_sub _ _).trans (add_le_add (abs_finiteStateGaussianPriorTimeMean_le d a L t ht H)
      (abs_finiteStateGaussianVarianceGenerator_le a (1-t) L (F t) (d.spatial_C2 t ht) C B
        (d.first_bound t ht) (d.second_bound t ht) H))

end FourPapersCommon
