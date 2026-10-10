module
public import FourPapersCommon.GenericFiniteStateCascadeTimeFormula

@[expose] public section

/-! The increasing-variance Gaussian derivative is obtained from the actual
decreasing-variance formula by reflection of the interpolation parameter. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 400000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianTimeReverse
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K) :
    FiniteStateGaussianTimeData (fun t => F (1-t)) C B K := by
  have href : Continuous (fun p : ℝ×FiniteStateField S => (1-p.1,p.2)) := by fun_prop
  have hmem (p : ℝ×FiniteStateField S) (hp : p ∈ finiteStateGaussianTimeDomain S) :
      (1-p.1,p.2) ∈ finiteStateGaussianTimeDomain S := ⟨by constructor <;> linarith [hp.1.1,hp.1.2],mem_univ _⟩
  refine {
    time := (fun t H => -(d.time (1-t) H)),
    cont := d.cont.comp href.continuousOn hmem,
    first_cont := d.first_cont.comp href.continuousOn hmem,
    second_cont := d.second_cont.comp href.continuousOn hmem,
    spatial_C2 := fun t ht => d.spatial_C2 (1-t) (by constructor <;> linarith [ht.1,ht.2]),
    first_bound := fun t ht => d.first_bound (1-t) (by constructor <;> linarith [ht.1,ht.2]),
    second_bound := fun t ht => d.second_bound (1-t) (by constructor <;> linarith [ht.1,ht.2]),
    time_cont := (d.time_cont.comp href.continuousOn hmem).neg,
    time_hasDeriv := ?_, time_bound := ?_ }
  · intro t ht H
    have hd := (d.time_hasDeriv (1-t) (by constructor <;> linarith [ht.1,ht.2]) H).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    simpa only [Function.comp_def, zero_sub, mul_neg_one] using hd
  · intro t ht H
    simpa only [abs_neg] using d.time_bound (1-t) (by constructor <;> linarith [ht.1,ht.2]) H

def finiteStateGaussianPositivePriorTimeMean
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (H : FiniteStateField S) : ℝ :=
  finiteStateGaussianInputMean a
    (fun z => F t (H+Real.sqrt t • L z))
    (fun z => d.time t (H+Real.sqrt t • L z))

theorem hasDerivAt_finiteStateGaussianStep_positive_time
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianStep a (Real.sqrt u • L) (F u) H)
      (finiteStateGaussianPositivePriorTimeMean d a L t H+
        finiteStateGaussianVarianceGenerator a t L (F t) H) t := by
  have hs (u : ℝ) : 1-(1-u)=u := by ring
  have hd := (hasDerivAt_finiteStateGaussianStep_time (finiteStateGaussianTimeReverse d) a L (1-t)
    (by constructor <;> linarith [ht.1,ht.2]) H).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have hm : finiteStateGaussianPriorTimeMean (finiteStateGaussianTimeReverse d) a L (1-t) H =
      -finiteStateGaussianPositivePriorTimeMean d a L t H := by
    simp only [finiteStateGaussianPriorTimeMean, finiteStateGaussianPositivePriorTimeMean,
      finiteStateGaussianTimeReverse, hs]
    simpa only [neg_one_mul] using finiteStateGaussianInputMean_const_mul a (-1)
      (fun z => F t (H+Real.sqrt t • L z)) (fun z => d.time t (H+Real.sqrt t • L z))
  rw [hm] at hd
  simpa only [finiteStateGaussianTimeReverse, Function.comp_def, hs, zero_sub, mul_neg_one, neg_sub,
    sub_neg_eq_add, add_comm] using hd

end FourPapersCommon
