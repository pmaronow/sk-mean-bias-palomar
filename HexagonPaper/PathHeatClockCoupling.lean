module
public import HexagonPaper.PathHeatEnvelope
public import HexagonPaper.PathHeatBernstein

@[expose] public section

/-! An actual common-Wiener coupling of finite clocked tree histories.
Clock composition is jointly continuous and never increases the Wiener
supremum. Fixed ancestor masks permit shared Brownian edges. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon
open scoped Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J L : Type*} [Fintype J] [Fintype L]

def pathHeatClockedWienerPath (c : C(Paper.Overlap,Paper.Overlap))
    (w : WienerPath) : WienerPath := w.comp c

theorem norm_pathHeatClockedWienerPath_le (c : C(Paper.Overlap,Paper.Overlap))
    (w : WienerPath) : ‖pathHeatClockedWienerPath c w‖≤‖w‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
  intro t
  exact w.norm_coe_le_norm _

theorem continuous_pathHeatClockedWienerPath :
    Continuous (fun p : C(Paper.Overlap,Paper.Overlap)×WienerPath=>
      pathHeatClockedWienerPath p.1 p.2) := ContinuousMap.continuous_comp'

def pathHeatClockTreePath (mask : J→L→ℝ) (c : J→C(Paper.Overlap,Paper.Overlap))
    (w : J→WienerPath) (l : L) : WienerPath :=
  ∑j : J,mask j l•pathHeatClockedWienerPath (c j) (w j)

theorem norm_pathHeatClockTreePath_le (mask : J→L→ℝ)
    (c : J→C(Paper.Overlap,Paper.Overlap)) (w : J→WienerPath) (l : L) :
    ‖pathHeatClockTreePath mask c w l‖≤∑j : J,|mask j l| *‖w j‖ := by
  unfold pathHeatClockTreePath
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _=>by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_pathHeatClockedWienerPath_le _ _) (abs_nonneg _)))

theorem continuous_pathHeatClockTreePath_family {Z : Type*} [TopologicalSpace Z]
    (mask : J→L→ℝ) (c : Z→J→C(Paper.Overlap,Paper.Overlap))
    (w : Z→J→WienerPath) (hc : ∀j,Continuous (fun z=>c z j))
    (hw : ∀j,Continuous (fun z=>w z j)) (l : L) :
    Continuous (fun z=>pathHeatClockTreePath mask (c z) (w z) l) := by
  apply continuous_finsetSum
  intro j _
  exact ((hw j).compCM (hc j)).const_smul (mask j l)

theorem tendsto_pathHeatClockTreePath_family {A : Type*} {l : Filter A}
    (mask : J→L→ℝ) (c : A→J→C(Paper.Overlap,Paper.Overlap))
    (w : A→J→WienerPath) (c₀ : J→C(Paper.Overlap,Paper.Overlap)) (w₀ : J→WienerPath)
    (hc : ∀j,Tendsto (fun i=>c i j) l (𝓝 (c₀ j)))
    (hw : ∀j,Tendsto (fun i=>w i j) l (𝓝 (w₀ j))) (v : L) :
    Tendsto (fun i=>pathHeatClockTreePath mask (c i) (w i) v) l
      (𝓝 (pathHeatClockTreePath mask c₀ w₀ v)) := by
  apply tendsto_finsetSum
  intro j _
  exact (hw j).compCM (hc j) |>.const_smul (mask j v)

end HexagonPaper
