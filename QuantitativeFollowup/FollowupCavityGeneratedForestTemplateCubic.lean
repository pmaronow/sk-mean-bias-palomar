module
public import QuantitativeFollowup.FollowupCavityGeneratedForestClocks

@[expose] public section

/-! A count-only cubic bound for actual native forests with explicit
generated mark measures. Structural branch labels and order restrictions
discharge the common-level assumptions internally, including repeated
leaf choices. No mark-domination or third-moment premise is supplied. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedForestTemplate_threeDefects_le
    (hn : 0 < n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedForestClockTemplate m) (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r))) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clock h) c b e
      ∂(P.restrict W.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (m:ℝ) * P.budget * cavityThirdMoment D μ a := by
  by_cases hbe : ∀r, b r ≠ e r
  · have hl : ∀ᵐ h ∂(P.restrict W.orderSet).measure (parisiFreeMeasure μ a), ∀r : Fin 3,
        ∃i : Fin m, W.clock h (c r) (observationCommonLevel (W.tree (c r)) (b r) (e r)) = h i := by
      have hh : ∀ᵐ h ∂(P.measure (parisiFreeMeasure μ a)).restrict W.orderSet, h ∈ W.orderSet :=
        ae_restrict_mem W.isClosed_orderSet.measurableSet
      exact hh.mono fun h hm r => W.branch_clock_is_mark h hm (c r) (b r) (e r) (hbe r)
    simpa only [CavityGeneratedMarkProgram.budget] using
      cavityGeneratedForest_three_defects_integral_le D μ a ha (P.restrict W.orderSet)
        W.depth W.tree W.clock (fun i p _ => W.clock_continuous i p)
        (fun h => W.clock_terminal h) (fun h => W.clock_initial h)
        (fun h i p _ => W.clock_step_le h i p) c b e hbe hl
  · push_neg at hbe
    obtain ⟨r, hr⟩ := hbe
    have hz : (fun h => cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clock h) c b e) = 0 := by
      funext h
      exact cavityGeneratedForestThreeDefectMoment_eq_zero_of_same hn D μ a W.depth W.tree
        (W.clock h) (W.clock_terminal h) c b e r hr
    rw [hz]
    change (∫ h : CavityGeneratedHistory Paper.Overlap m, (0:ℝ)
      ∂(P.restrict W.orderSet).measure (parisiFreeMeasure μ a)) ≤ _
    rw [integral_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg P.budget))
      (cavityThirdMoment_nonneg D μ a)

def cavityGeneratedThreeDefectCountConstant (L N : ℕ) : ℕ := (N+1)*(L+2)^N

theorem cavityGeneratedForestTemplate_threeDefects_count_bound
    (hn : 0 < n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedForestClockTemplate m) (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r)))
    (L : ℕ) (hL : P.largestMultiplicity ≤ L) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clock h) c b e
      ∂(P.restrict W.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (cavityGeneratedThreeDefectCountConstant L P.constructorCount : ℝ) * cavityThirdMoment D μ a := by
  have hm : (m:ℝ) ≤ (P.constructorCount+1:ℕ) := by
    exact_mod_cast P.markCount_le_constructorCount_succ
  have hb : (P.budget:ℝ) ≤ ((L+2)^P.constructorCount:ℕ) := by
    exact_mod_cast P.budget_le_count_power L hL
  have hs := mul_le_mul hm hb (Nat.cast_nonneg P.budget)
    (show (0:ℝ) ≤ (P.constructorCount+1:ℕ) from Nat.cast_nonneg _)
  apply (cavityGeneratedForestTemplate_threeDefects_le hn D μ a ha P W c b e).trans
  simpa only [cavityGeneratedThreeDefectCountConstant, Nat.cast_mul] using
    mul_le_mul_of_nonneg_right hs (cavityThirdMoment_nonneg D μ a)

end QuantitativeFollowup
