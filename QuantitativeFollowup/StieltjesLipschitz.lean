module
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-! A globally Lipschitz monotone primitive gives a genuinely dominated
Stieltjes measure. The proof constructs the complementary monotone
primitive, so it requires no assumed Radon--Nikodym conclusion. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace QuantitativeFollowup

def stieltjesMax (f : StieltjesFunction ℝ) (c : ℝ) : StieltjesFunction ℝ where
  toFun x := max c (f x)
  mono' := monotone_const.max f.mono
  right_continuous' x := continuousWithinAt_const.max (f.right_continuous x)

def stieltjesMin (f : StieltjesFunction ℝ) (c : ℝ) : StieltjesFunction ℝ where
  toFun x := min c (f x)
  mono' := monotone_const.min f.mono
  right_continuous' x := continuousWithinAt_const.min (f.right_continuous x)

theorem stieltjesMax_measure_le (f : StieltjesFunction ℝ) (c : ℝ) :
    (stieltjesMax f c).measure ≤ f.measure := by
  have he : stieltjesMax f c + stieltjesMin f c = f + StieltjesFunction.const ℝ c := by
    ext x
    change max c (f x)+min c (f x) = f x+c
    rw [max_add_min,add_comm]
  have hm : (stieltjesMax f c).measure + (stieltjesMin f c).measure = f.measure := by
    rw [←StieltjesFunction.measure_add,he,StieltjesFunction.measure_add,
      StieltjesFunction.measure_const,add_zero]
  rw [←hm]
  exact Measure.le_add_right le_rfl

end QuantitativeFollowup
