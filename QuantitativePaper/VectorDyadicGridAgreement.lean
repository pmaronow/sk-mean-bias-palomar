module
public import FourPapersCommon.ParisiNestedGrid
public import QuantitativePaper.VectorMeasureTail

@[expose] public section

/-! Exact agreement of the actual arbitrary-measure potential with every
finite dyadic grid recursion. Nested grid laws stabilize exactly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1400000
open SpinGlass SpinGlass.Targets FourPapersCommon
variable {n : ℕ}

theorem parisiGridMeasure_dyadic_refines (μ : Paper.ParisiMeasure) (a b : ℕ) (hab : a ≤ b) :
    Paper.parisiGridMeasure (Paper.parisiGridMeasure μ (vectorDyadicIndex a))
      (vectorDyadicIndex b) = Paper.parisiGridMeasure μ (vectorDyadicIndex a) := by
  apply parisiGridMeasure_refines μ (vectorDyadicIndex a) (vectorDyadicIndex b)
    (2^(b-a)) (pow_pos (by omega) _)
  rw [vectorDyadicIndex_add_one, vectorDyadicIndex_add_one, ← pow_add]
  congr 1
  omega

theorem vectorDyadicTailPotential_grid_succ (μ : Paper.ParisiMeasure) (a j : ℕ)
    (haj : a ≤ j) (β t q : ℝ) (ht : t ≤ 1) (p : Couplings n × ℝ) :
    vectorDyadicTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q (j+1) p =
      vectorDyadicTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q j p := by
  let ν := Paper.parisiGridMeasure μ (vectorDyadicIndex a)
  have he := vectorTailRecursion_grid_refine_coarse (n := n) ν (vectorDyadicIndex j) β t q ht p
  rw [show Paper.parisiGridMeasure ν (vectorDyadicIndex j) = ν from
    parisiGridMeasure_dyadic_refines μ a j haj] at he
  funext x
  have hex := congrFun he x
  unfold vectorDyadicTailPotential
  rw [vectorDyadicIndex_succ]
  simpa only [
    show 2*vectorDyadicIndex j+1+3 = 2*vectorDyadicIndex j+4 by omega, ν] using hex

theorem vectorDyadicTailPotential_grid_stable (μ : Paper.ParisiMeasure) (a j : ℕ)
    (haj : a+1 ≤ j) (β t q : ℝ) (ht : t ≤ 1) (p : Couplings n × ℝ) :
    vectorDyadicTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q j p =
      vectorDyadicTailPotential μ β t q a p := by
  induction j, haj using Nat.le_induction with
  | base =>
    have he := vectorTailRecursion_grid_refine_coarse (n := n) μ (vectorDyadicIndex a) β t q ht p
    funext x
    have hex := congrFun he x
    unfold vectorDyadicTailPotential
    rw [vectorDyadicIndex_succ]
    simpa only [
      show 2*vectorDyadicIndex a+1+3 = 2*vectorDyadicIndex a+4 by omega] using hex
  | succ j hj ih =>
    rw [vectorDyadicTailPotential_grid_succ μ a j (by omega) β t q ht p, ih]

theorem vectorMeasureTailPotential_grid_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    vectorMeasureTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q p =
      vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t q p
        (vectorDyadicIndex a+3) := by
  funext x
  apply tendsto_nhds_unique
    (tendsto_vectorDyadicTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a))
      β t q ht q.property p x)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (a+1)] with j hj
  exact (congrFun (vectorDyadicTailPotential_grid_stable μ a j hj β t q ht p) x).symm

theorem vectorMeasurePotential_grid_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n × ℝ) :
    vectorMeasurePotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t p =
      vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t p
        (vectorDyadicIndex a+3) := by
  funext x
  calc
    _ = vectorMeasureTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t 0 p x :=
      (vectorMeasureTailPotential_zero _ β t ht p x).symm
    _ = vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t 0 p
        (vectorDyadicIndex a+3) x :=
      congrFun (vectorMeasureTailPotential_grid_eq_finite μ a β t ht
        ⟨0, by constructor <;> norm_num⟩ p) x
    _ = _ := congrFun (vectorTailRecursion_zero _ β t p le_rfl) x

end QuantitativePaper
