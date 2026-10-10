module
public import QuantitativePaper.VectorDyadicStateConvergence

@[expose] public section

/-! Actual upward grid nodes approximate every physical overlap. The
chosen node retains measurability of every event from the earlier past. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 400000

def vectorDyadicTimeIndex (q : Paper.Overlap) (j : ℕ) : ℕ :=
  (Paper.parisiGridIndex (vectorDyadicIndex j) q).val+1

theorem vectorDyadicTimeIndex_le (q : Paper.Overlap) (j : ℕ) :
    vectorDyadicTimeIndex q j≤vectorDyadicIndex j+2 := by
  have h := (Paper.parisiGridIndex (vectorDyadicIndex j) q).isLt
  unfold vectorDyadicTimeIndex
  omega

theorem vectorDyadicTimeIndex_node (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) :
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (vectorDyadicTimeIndex q j)=
      (Paper.parisiGridRound (vectorDyadicIndex j) q : ℝ) := by
  unfold Paper.parisiGridRSBScheme Paper.parisiGridSchemeOverlap vectorDyadicTimeIndex
    Paper.parisiGridRound Paper.parisiGridPoint
  simp only [Nat.add_sub_cancel]
  rw [min_eq_left (by have h := (Paper.parisiGridIndex (vectorDyadicIndex j) q).isLt;omega)]

def vectorDyadicTime (q : Paper.Overlap) (j : ℕ) : ℝ≥0 :=
  (Paper.parisiGridRound (vectorDyadicIndex j) q : ℝ).toNNReal

theorem vectorDyadicTime_le_one (q : Paper.Overlap) (j : ℕ) : vectorDyadicTime q j≤1 := by
  unfold vectorDyadicTime
  exact Real.toNNReal_le_one.mpr (Paper.parisiGridRound (vectorDyadicIndex j) q).property.2

theorem le_vectorDyadicTime (q : Paper.Overlap) (j : ℕ) : (q : ℝ).toNNReal≤vectorDyadicTime q j :=
  Real.toNNReal_le_toNNReal (Paper.le_parisiGridRound (vectorDyadicIndex j) q)

theorem tendsto_vectorDyadicTime (q : Paper.Overlap) :
    Tendsto (vectorDyadicTime q) atTop (𝓝 (q : ℝ).toNNReal) := by
  have hq := (Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hr : Tendsto (fun j : ℕ=>(Paper.parisiGridRound (vectorDyadicIndex j) q : ℝ)) atTop
      (𝓝 (q : ℝ)) := by
    exact (continuous_subtype_val.tendsto q).comp hq
  change Tendsto (fun j=>(Paper.parisiGridRound (vectorDyadicIndex j) q : ℝ).toNNReal)
    atTop (𝓝 (q : ℝ).toNNReal)
  simpa only [Function.comp_def] using
    (continuous_real_toNNReal.tendsto (q : ℝ)).comp hr

end QuantitativePaper
