module
public import HexagonPaper.PathHeatClockFactor

@[expose] public section

/-! Genuine local regularity and finite uniform bounds for the explicit
clock-variance factor. Zero dimension is included. -/
noncomputable section
open Set Filter
open scoped Topology NNReal BigOperators
namespace HexagonPaper
open QuantitativePaper
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ}

theorem continuousAt_pathHeatVarianceFactor (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ)
    (hv : ∀ i, ContinuousAt (fun u => v u i) z) :
    ContinuousAt (pathHeatVarianceFactor v V) z := by
  unfold pathHeatVarianceFactor ContinuousAt
  apply tendsto_finsetSum
  intro i _
  exact ((hv i).sqrt.smul continuousAt_const).tendsto

theorem continuousAt_pathHeatVarianceFactorDerivative (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hpos : ∀ i, 0 < v z i)
    (hv : ∀ i, ContinuousAt (fun u => v u i) z)
    (hdv : ∀ i, ContinuousAt (fun u => dv u i) z) :
    ContinuousAt (pathHeatVarianceFactorDerivative v dv V) z := by
  unfold pathHeatVarianceFactorDerivative ContinuousAt
  apply tendsto_finsetSum
  intro i _
  exact (((hdv i).div ((hv i).sqrt.const_mul 2)
    (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (hpos i)).ne')).smul
      continuousAt_const).tendsto

theorem pathHeatVarianceFactor_local_bounds (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hpos : ∀ i, 0 < v z i)
    (hv : ∀ i, ContinuousAt (fun u => v u i) z)
    (hdv : ∀ i, ContinuousAt (fun u => dv u i) z) :
    ∃ (S : Set ℝ) (K L : ℝ≥0), S ∈ 𝓝 z ∧
      (∀ u ∈ S, ‖pathHeatVarianceFactor v V u‖ ≤ K) ∧
      (∀ u ∈ S, ‖pathHeatVarianceFactorDerivative v dv V u‖ ≤ L) := by
  let A := pathHeatVarianceFactor v V
  let B := pathHeatVarianceFactorDerivative v dv V
  have hA := continuousAt_pathHeatVarianceFactor v V z hv
  have hB := continuousAt_pathHeatVarianceFactorDerivative v dv V z hpos hv hdv
  have ha : ∀ᶠ u in 𝓝 z, ‖A u‖ < ‖A z‖+1 :=
    hA.norm.tendsto.eventually_lt_const (by dsimp [A];linarith)
  have hb : ∀ᶠ u in 𝓝 z, ‖B u‖ < ‖B z‖+1 :=
    hB.norm.tendsto.eventually_lt_const (by dsimp [B];linarith)
  refine ⟨{u | ‖A u‖ < ‖A z‖+1 ∧ ‖B u‖ < ‖B z‖+1},
    ⟨‖A z‖+1,by positivity⟩,⟨‖B z‖+1,by positivity⟩,ha.and hb,?_,?_⟩
  · intro u hu
    exact hu.1.le
  · intro u hu
    exact hu.2.le

def pathHeatClockMeshVariance (c : ℝ → Fin (n+1) → ℝ)
    (z : ℝ) (i : Fin n) : ℝ := c z i.succ-c z i.castSucc

theorem hasDerivAt_pathHeatClockMeshVariance
    (c dc : ℝ → Fin (n+1) → ℝ) (z : ℝ)
    (hc : ∀ i, HasDerivAt (fun u => c u i) (dc z i) z) (i : Fin n) :
    HasDerivAt (fun u => pathHeatClockMeshVariance c u i)
      (pathHeatClockMeshVariance dc z i) z :=
  (hc i.succ).sub (hc i.castSucc)

theorem hasDerivAt_pathHeatClockMeshFactor
    (c dc : ℝ → Fin (n+1) → ℝ) (V : Fin n → Field m) (z : ℝ)
    (hc : ∀ i, HasDerivAt (fun u => c u i) (dc z i) z)
    (hpos : ∀ i : Fin n, c z i.castSucc < c z i.succ) :
    HasDerivAt (pathHeatVarianceFactor (pathHeatClockMeshVariance c) V)
      (pathHeatVarianceFactorDerivative (pathHeatClockMeshVariance c)
        (pathHeatClockMeshVariance dc) V z) z :=
  hasDerivAt_pathHeatVarianceFactor _ _ V z
    (fun i => sub_pos.2 (hpos i))
    (hasDerivAt_pathHeatClockMeshVariance c dc z hc)

end HexagonPaper
