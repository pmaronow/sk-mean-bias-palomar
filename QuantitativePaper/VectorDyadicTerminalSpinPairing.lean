module
public import QuantitativePaper.VectorDyadicSpinMeanConvergence

@[expose] public section

/-! Actual terminal spin pairings at the upward dyadic node. The weight
can observe every part of the original Wiener past at the requested time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorDyadic_terminal_spin_pairing_past (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (j : ℕ) (l : Fin n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫sample,Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
      (fun σ=>Paper.spinSign (σ l))
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)=
      ∫sample,Z sample*vectorDyadicSpinMean μ β t ht.le q j sample l
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  have hi : vectorDyadicTimeIndex q j≤(vectorDyadicIndex j+1)+2 :=
    (vectorDyadicTimeIndex_le q j).trans (by omega)
  have htime : ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q
      (vectorDyadicTimeIndex q j)).toNNReal=vectorDyadicTime q j := by
    rw [vectorDyadicTimeIndex_node]
    rfl
  have hpast : Measurable[vectorBrownianFiltration n
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q
        (vectorDyadicTimeIndex q j)).toNNReal] Z := by
    rw [htime]
    exact hZ.mono ((vectorBrownianFiltration n).mono (le_vectorDyadicTime q j)) le_rfl
  have he := vectorFinite_terminal_mean_pairing_past
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a hβ ht
    (fun σ=>Paper.spinSign (σ l)) (vectorDyadicTimeIndex q j) hi Z hpast C hC
  rw [htime] at he
  refine he.trans (integral_congr_ae (.of_forall fun sample=>?_))
  exact congrArg (fun v : ℝ=>Z sample*v)
    (vectorDyadicSpinMean_eq_backward μ β t ht.le q j sample l).symm

end QuantitativePaper
