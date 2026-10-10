module
public import HexagonPaper.PathHeatClockKernelFamily

@[expose] public section

/-! The physical covariance derivative is derived from the actual clock
derivatives. Fixed ancestor and terminal-row reconstruction introduces only
finite linear combinations of those clock covariances. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem hasDerivAt_pathHeatClockRawKernel {L : ℕ}
    (c dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ)
    (hdc : ∀l t, HasDerivAt (fun w => c w l t) (dc z l t) z)
    (x y : Fin L × I) :
    HasDerivAt (fun w => pathHeatClockRawKernel (c w) x y)
      (pathHeatClockRawKernel (dc z) x y) z := by
  simp only [pathHeatClockRawKernel_apply]
  by_cases h : x.1=y.1
  · simpa only [if_pos h] using hdc x.1 (min x.2 y.2)
  · simpa only [if_neg h] using hasDerivAt_const z (0:ℝ)

theorem hasDerivAt_pathHeatMixedClockKernel {L : ℕ}
    (c dc : ℝ → Fin L → C(I,ℝ)) (δ : Fin L → ℝ)
    (W : Fin L → Fin L → ℝ) (z : ℝ)
    (hdc : ∀l t, HasDerivAt (fun w => c w l t) (dc z l t) z)
    (x y : Fin L × I) :
    HasDerivAt (fun w => pathHeatTreeMixedKernelOperator δ W
        (pathHeatClockRawKernel (c w)) x y)
      (pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z)) x y) z := by
  simp only [pathHeatTreeMixedKernelOperator_four_terms,smul_eq_mul]
  have h1 := (hasDerivAt_pathHeatClockRawKernel c dc z hdc x y).const_mul
    (δ x.1 * δ y.1)
  have h2 : HasDerivAt (fun w => ∑b : Fin L,
      (δ x.1 * W y.1 b) * pathHeatClockRawKernel (c w) x (b,1))
      (∑b : Fin L, (δ x.1 * W y.1 b) * pathHeatClockRawKernel (dc z) x (b,1)) z := by
    apply HasDerivAt.fun_sum
    intro b _
    exact (hasDerivAt_pathHeatClockRawKernel c dc z hdc x (b,1)).const_mul _
  have h3 : HasDerivAt (fun w => ∑a : Fin L,
      (W x.1 a * δ y.1) * pathHeatClockRawKernel (c w) (a,1) y)
      (∑a : Fin L, (W x.1 a * δ y.1) * pathHeatClockRawKernel (dc z) (a,1) y) z := by
    apply HasDerivAt.fun_sum
    intro a _
    exact (hasDerivAt_pathHeatClockRawKernel c dc z hdc (a,1) y).const_mul _
  have h4 : HasDerivAt (fun w => ∑a : Fin L, ∑b : Fin L,
      (W x.1 a * W y.1 b) * pathHeatClockRawKernel (c w) (a,1) (b,1))
      (∑a : Fin L, ∑b : Fin L,
        (W x.1 a * W y.1 b) * pathHeatClockRawKernel (dc z) (a,1) (b,1)) z := by
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro b _
    exact (hasDerivAt_pathHeatClockRawKernel c dc z hdc (a,1) (b,1)).const_mul _
  exact ((h1.add h2).add h3).add h4

theorem hasDerivAt_pathHeatMixedUnitClockKernel {L : ℕ}
    (c : ℝ → Fin L → C(I,I)) (dc : ℝ → Fin L → C(I,ℝ))
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (z : ℝ)
    (hdc : ∀l t, HasDerivAt (fun w => (c w l t : ℝ)) (dc z l t) z)
    (x y : Fin L × I) :
    HasDerivAt (fun w => pathHeatTreeMixedKernelOperator δ W
        (pathHeatClockRawKernel (pathHeatClockReal (c w))) x y)
      (pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z)) x y) z :=
  hasDerivAt_pathHeatMixedClockKernel (fun w => pathHeatClockReal (c w)) dc δ W z hdc x y

end HexagonPaper
