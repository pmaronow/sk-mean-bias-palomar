module
public import QuantitativePaper.ResponseCrossingTime
public import QuantitativePaper.VectorDyadicHessianPassage

@[expose] public section

/-! Upward grid nodes at an actual CDF crossing have the literal incoming
and outgoing masses required by the conditioned finite-prefix estimate. -/
noncomputable section
open Set Paper
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem parisiGridRSBScheme_firstMass (μ : ParisiMeasure) (n : ℕ) :
    (parisiGridRSBScheme μ n).m 1=parisiCDF μ 0 := by
  have hh := parisiCDF_grid_at_round μ n (⟨0,by constructor <;> norm_num⟩ : Overlap)
  simpa [parisiGridRSBScheme,parisiGridSchemeMass,parisiGridSchemeOverlap,
    parisiGridRound,parisiGridIndex,parisiGridPoint] using hh

theorem vectorDyadic_previous_node_lt (μ : ParisiMeasure) (T : Overlap) (j : ℕ)
    (hN : 1 < vectorDyadicTimeIndex T j) :
    (parisiGridRSBScheme μ (vectorDyadicIndex j)).q (vectorDyadicTimeIndex T j-1) < T := by
  let d := vectorDyadicIndex j+1
  let c := Nat.ceil ((d : ℝ)*(T : ℝ))
  have hd : 0 < (d : ℝ) := by dsimp [d];positivity
  have hc : 1 ≤ c := by
    change 1 < c+1 at hN
    omega
  have hcd : c ≤ d := by
    apply Nat.ceil_le.mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left T.property.2 hd.le
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hd.le T.property.1)
  change ((min (c-1) d : ℕ) : ℝ)/(d : ℝ) < T
  rw [min_eq_left (by omega : c-1 ≤ d),Nat.cast_sub hc,Nat.cast_one,
    div_lt_iff₀ hd]
  dsimp [c] at *
  nlinarith

theorem responseDyadicCrossingStage (μ : ParisiMeasure) (β a U : ℝ)
    (hβ : 0 < β) (ha : a ≤ parisiCDF μ 0) (T : Overlap)
    (hTout : 1 ≤ β*parisiCDF μ T)
    (hTin : ∀r : ℝ,r ∈ Icc 0 1 → r < T → β*parisiCDF μ r ≤ max 1 U)
    (hroot : β*a ≤ max 1 U) (j : ℕ) :
    a ≤ (parisiGridRSBScheme μ (vectorDyadicIndex j)).m 1 ∧
    1 ≤ β*vectorDyadicNodeMass μ T j ∧
    β*(if vectorDyadicTimeIndex T j=1 then a else
      (parisiGridRSBScheme μ (vectorDyadicIndex j)).m (vectorDyadicTimeIndex T j-1)) ≤ max 1 U := by
  refine ⟨by rwa [parisiGridRSBScheme_firstMass],?_,?_⟩
  · rw [vectorDyadicNodeMass_eq_CDF]
    exact hTout.trans (mul_le_mul_of_nonneg_left
      (parisiCDF_monotone μ (le_parisiGridRound _ T)) hβ.le)
  · by_cases h1 : vectorDyadicTimeIndex T j=1
    · simpa only [if_pos h1] using hroot
    · have hNpos : 0 < vectorDyadicTimeIndex T j := by unfold vectorDyadicTimeIndex;omega
      have hNg : 1 < vectorDyadicTimeIndex T j := by omega
      let s := parisiGridRSBScheme μ (vectorDyadicIndex j)
      let P := vectorDyadicTimeIndex T j-1
      have hP : P ≤ vectorDyadicIndex j+2 := (Nat.sub_le _ _).trans (vectorDyadicTimeIndex_le T j)
      have hPm : s.q P ∈ Icc (0 : ℝ) 1 :=
        ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      have hPlt : s.q P < T := vectorDyadic_previous_node_lt μ T j hNg
      have hmass : s.m P ≤ parisiCDF μ (s.q P) := by
        change parisiGridSchemeMass μ (vectorDyadicIndex j) P ≤ _
        rw [parisiGridSchemeMass,if_neg (by dsimp [P];omega)]
        exact parisiCDF_grid_le μ (vectorDyadicIndex j) _
      rw [if_neg h1]
      exact (mul_le_mul_of_nonneg_left hmass hβ.le).trans (hTin _ hPm hPlt)

end QuantitativePaper
