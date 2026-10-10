module
public import QuantitativePaper.VectorBrownianHistory

@[expose] public section

/-! The genuine continuous Brownian base model realizes the existing finite
RSB vector law at every finite overlap grid, including repeated nodes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

def schemeBrownianClock {k : ℕ} (s : RSBScheme k) : Fin (k+3) → ℝ≥0 :=
  fun i => (s.q i).toNNReal

theorem schemeBrownianClock_mono {k : ℕ} (s : RSBScheme k) : Monotone (schemeBrownianClock s) := by
  intro i j hij
  apply Real.toNNReal_le_toNNReal
  exact s.q_mono' j (by omega) i (by exact_mod_cast hij)

@[simp] theorem schemeBrownianClock_zero {k : ℕ} (s : RSBScheme k) :
    schemeBrownianClock s 0 = 0 := by
  simp [schemeBrownianClock,s.q_zero]

def vectorBrownianScale (β t : ℝ) : ℝ := Real.sqrt ((1-t)*β^2)

theorem vectorBrownianScale_sq (β t : ℝ) (ht : t ≤ 1) :
    vectorBrownianScale β t ^ 2 = (1-t)*β^2 :=
  Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))

theorem schemeBrownianGridVariance {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (ht : t ≤ 1) (i : Fin (k+2)) :
    brownianGridVariance (schemeBrownianClock s) (vectorBrownianScale β t) i =
      (1-t)*(β^2*(s.q (i+1)-s.q i)) := by
  unfold brownianGridVariance schemeBrownianClock
  rw [vectorBrownianScale_sq β t ht]
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [Real.coe_toNNReal _ (s.q_nonneg (p := i.val+1) (by omega)),
    Real.coe_toNNReal _ (s.q_nonneg (p := i.val) (by omega))]
  ring

theorem brownianGridKernel_scheme {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    brownianGridKernel (n := n) (schemeBrownianClock s) (vectorBrownianScale β t) =
      vectorProfileBaseKernel s β t := by
  funext i
  unfold brownianGridKernel vectorProfileBaseKernel
  by_cases hi : i < k+2
  · have hj : i ≤ k+1 := by omega
    simp only [dite_eq_left hi,ite_eq_left hj]
    rw [schemeBrownianGridVariance s β t ht]
  · have hj : ¬ i ≤ k+1 := by omega
    simp only [dite_eq_right hi,ite_eq_right hj]

def vectorSchemeBrownianHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (VectorState n) (k+2) :=
  scaledDisorderBrownianHistory (schemeBrownianClock s) (vectorBrownianScale β t) sample

theorem measurable_vectorSchemeBrownianHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (vectorSchemeBrownianHistory (n := n) s β t) :=
  measurable_scaledDisorderBrownianHistory _ _

theorem vectorSchemeBrownianHistory_map {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    (vectorDisorderBrownianMeasure n).map (vectorSchemeBrownianHistory s β t) =
      vectorBaseFieldHistoryLaw s β t := by
  unfold vectorSchemeBrownianHistory
  rw [scaledDisorderBrownianHistory_map _
    (schemeBrownianClock_mono s) (schemeBrownianClock_zero s),
    brownianGridKernel_scheme s β t ht]
  rfl

@[simp] theorem vectorSchemeBrownianHistory_initial {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (sample : VectorDisorderBrownianSample n) :
    vectorSchemeBrownianHistory s β t sample 0 = (sample.1,0) := by
  simp [vectorSchemeBrownianHistory,scaledDisorderBrownianHistory,disorderVectorBrownian]

theorem vectorSchemeBrownianHistory_disorder {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (sample : VectorDisorderBrownianSample n) (i : Fin (k+3)) :
    (vectorSchemeBrownianHistory s β t sample i).1 = sample.1 := rfl

theorem vectorSchemeBrownianHistory_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (sample : VectorDisorderBrownianSample n) (i : Fin (k+3)) :
    (vectorSchemeBrownianHistory s β t sample i).2 =
      Real.sqrt (β^2*(1-t)) • disorderVectorBrownian ((s.q i).toNNReal) sample := by
  change Real.sqrt ((1-t)*β^2) • _ = Real.sqrt (β^2*(1-t)) • _
  rw [mul_comm (1-t)]
  rfl

end QuantitativePaper
