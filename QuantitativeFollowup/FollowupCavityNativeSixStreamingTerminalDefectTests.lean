module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairCommonClock
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeOldVertexGeometry
public import FourPapersCommon.FiniteObservationTerminalProjection
public import QuantitativeFollowup.FollowupCavityMarkedDefectBounds

@[expose] public section

/-! Literal terminal-spin defect tests depend continuously on their true
common-history clock and have the source bound 2 sup|F|.  These tests are
the coefficients passed to the moving mark laws; a CDF multiplier is kept
separate, since a genuine profile may have atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 900000

theorem continuous_cavitySpinOverlapDefect_clock
    {A : Type*} [TopologicalSpace A] (clock : A → Paper.Overlap)
    (hclock : Continuous clock) (σ τ : Configuration (n+1)) :
    Continuous (fun z => cavitySpinOverlapDefect n (clock z) σ τ) := by
  simp only [cavitySpinOverlapDefect_eq]
  exact continuous_const.mul (continuous_const.sub (continuous_subtype_val.comp hclock))

def nativeStreamingDefectSpinTest
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (q : Paper.Overlap)
    (z : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1))) : ℝ :=
  F z.1 * cavitySpinOverlapDefect n q z.2.1 z.2.2

theorem nativeStreamingDefectSpinTest_abs_le
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (z : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1))) :
    |nativeStreamingDefectSpinTest T F q z| ≤ 2*C := by
  rw [nativeStreamingDefectSpinTest, abs_mul]
  exact (mul_le_mul (hF z.1)
    (cavitySpinOverlapDefect_abs_le_two n q q.property z.2.1 z.2.2)
    (abs_nonneg _) hC).trans_eq (by ring)

theorem continuous_nativeStreamingDefectSpinTest_clock
    {A : Type*} [TopologicalSpace A]
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (clock : A → Paper.Overlap) (hclock : Continuous clock)
    (z : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1))) :
    Continuous (fun r => nativeStreamingDefectSpinTest T F (clock r) z) :=
  continuous_const.mul (continuous_cavitySpinOverlapDefect_clock clock hclock z.2.1 z.2.2)

theorem continuous_nativeStreamingOldSelectedCommonClock
    (c de : ℕ) (qc : Paper.Overlap) :
    Continuous (fun r : Paper.Overlap => nativeStreamingOldSelectedCommonClock c de r qc) := by
  classical
  unfold nativeStreamingOldSelectedCommonClock
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem continuous_nativeStreamingEdgePairDefectSpinTest
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (c de df : ℕ) (qc : Paper.Overlap)
    (z : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1))) :
    Continuous (fun r : Paper.Overlap × Paper.Overlap =>
      nativeStreamingDefectSpinTest T F
        (nativeStreamingSelectedCommonClock c de df r.1 r.2 qc) z) :=
  continuous_nativeStreamingDefectSpinTest_clock T F _
    (continuous_nativeStreamingSelectedCommonClock c de df qc) z

def nativeStreamingOriginalFreshSpinTest
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (q : Paper.Overlap)
    (z : TerminalSpins (Configuration (n+1)) T × Configuration (n+1)) : ℝ :=
  F z.1 * cavitySpinOverlapDefect n q (observationTerminalSpin T i z.1) z.2

theorem nativeStreamingOriginalFreshSpinTest_abs_le
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C)
    (i : ObservationLeaf T) (q : Paper.Overlap)
    (z : TerminalSpins (Configuration (n+1)) T × Configuration (n+1)) :
    |nativeStreamingOriginalFreshSpinTest T F i q z| ≤ 2*C := by
  rw [nativeStreamingOriginalFreshSpinTest, abs_mul]
  exact (mul_le_mul (hF z.1)
    (cavitySpinOverlapDefect_abs_le_two n q q.property (observationTerminalSpin T i z.1) z.2)
    (abs_nonneg _) hC).trans_eq (by ring)

theorem continuous_nativeStreamingOriginalFreshSpinTest_clock
    {A : Type*} [TopologicalSpace A]
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (clock : A → Paper.Overlap) (hclock : Continuous clock)
    (z : TerminalSpins (Configuration (n+1)) T × Configuration (n+1)) :
    Continuous (fun r => nativeStreamingOriginalFreshSpinTest T F i (clock r) z) :=
  continuous_const.mul
    (continuous_cavitySpinOverlapDefect_clock clock hclock (observationTerminalSpin T i z.1) z.2)

end QuantitativeFollowup
