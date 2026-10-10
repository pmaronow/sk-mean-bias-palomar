module
public import HexagonPaper.PathHeatTreeBernsteinReconstructionCovariance

@[expose] public section

/-! Mixed tree paths and finite coordinates. A row with own coefficient zero
and terminal self coefficient one is exactly a constant finite-coordinate
path; rows with own coefficient one are physical tree edges. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathHeatTreeDiagonalColumn {L : ℕ} (δ : Fin L → ℝ) : C(Fin L × I,ℝ) :=
  ⟨fun x => δ x.1, continuous_prod_of_discrete_left.mpr (fun l => by
    change Continuous (fun _ : I => δ l)
    exact continuous_const)⟩

def pathHeatTreeDiagonalSample {L : ℕ} (δ : Fin L → ℝ)
    (f : C(Fin L × I,E)) : C(Fin L × I,E) :=
  ⟨fun x => δ x.1 • f x, (pathHeatTreeDiagonalColumn δ).continuous.smul f.continuous⟩

@[simp] theorem pathHeatTreeDiagonalSample_apply {L : ℕ} (δ : Fin L → ℝ)
    (f : C(Fin L × I,E)) (x : Fin L × I) :
    pathHeatTreeDiagonalSample δ f x = δ x.1 • f x := rfl

theorem norm_pathHeatTreeDiagonalSample_le {L : ℕ} (δ : Fin L → ℝ)
    (f : C(Fin L × I,E)) :
    ‖pathHeatTreeDiagonalSample δ f‖ ≤ ‖pathHeatTreeDiagonalColumn δ‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  rw [pathHeatTreeDiagonalSample_apply,norm_smul]
  exact mul_le_mul ((pathHeatTreeDiagonalColumn δ).norm_coe_le_norm x)
    (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

def pathHeatTreeDiagonalOperator {L : ℕ} (δ : Fin L → ℝ) :
    C(Fin L × I,E) →L[ℝ] C(Fin L × I,E) :=
  LinearMap.mkContinuous
    { toFun := pathHeatTreeDiagonalSample δ
      map_add' := by intro f g; ext x; exact smul_add _ _ _
      map_smul' := by intro c f; ext x; simp only [pathHeatTreeDiagonalSample_apply,
        ContinuousMap.smul_apply,RingHom.id_apply,smul_smul]; rw [mul_comm] }
    ‖pathHeatTreeDiagonalColumn δ‖ (norm_pathHeatTreeDiagonalSample_le δ)

@[simp] theorem pathHeatTreeDiagonalOperator_apply {L : ℕ} (δ : Fin L → ℝ)
    (f : C(Fin L × I,E)) (x : Fin L × I) :
    pathHeatTreeDiagonalOperator δ f x = δ x.1 • f x := rfl

theorem norm_pathHeatTreeDiagonalOperator_le {L : ℕ} (δ : Fin L → ℝ) :
    ‖pathHeatTreeDiagonalOperator (E:=E) δ‖ ≤ ‖pathHeatTreeDiagonalColumn δ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (norm_pathHeatTreeDiagonalSample_le δ)

theorem pathHeatTreeDiagonalOperator_bernstein_commute (n L : ℕ)
    (δ : Fin L → ℝ) (f : C(Fin L × I,E)) :
    pathHeatTreeBernsteinOperator n L (pathHeatTreeDiagonalOperator δ f) =
      pathHeatTreeDiagonalOperator δ (pathHeatTreeBernsteinOperator n L f) := by
  ext x
  simp only [pathHeatTreeBernsteinOperator_apply,pathHeatTreeBernsteinSample_apply,
    pathHeatTreeDiagonalOperator_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl; intro i _; rw [mul_comm]

def pathHeatTreeMixedOperator {L : ℕ} (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) :
    C(Fin L × I,E) →L[ℝ] C(Fin L × I,E) :=
  pathHeatTreeDiagonalOperator (fun l => δ l-1) + pathHeatTreeAncestorOperator W

theorem pathHeatTreeMixedOperator_apply {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) (x : Fin L × I) :
    pathHeatTreeMixedOperator δ W f x = δ x.1 • f x + ∑a : Fin L, W x.1 a • f (a,1) := by
  simp only [pathHeatTreeMixedOperator,ContinuousLinearMap.add_apply,ContinuousMap.add_apply,
    pathHeatTreeDiagonalOperator_apply,pathHeatTreeAncestorOperator_apply,
    pathHeatTreeAncestorReconstruct_apply,sub_smul,one_smul]
  abel

def pathHeatTreeMixedBound {L : ℕ} (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) : ℝ :=
  ‖pathHeatTreeDiagonalColumn (fun l => δ l-1)‖ + pathHeatTreeAncestorBound W

theorem pathHeatTreeMixedBound_nonneg {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) : 0 ≤ pathHeatTreeMixedBound δ W :=
  add_nonneg (norm_nonneg _) (pathHeatTreeAncestorBound_nonneg W)

theorem norm_pathHeatTreeMixedOperator_le {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) :
    ‖pathHeatTreeMixedOperator (E:=E) δ W‖ ≤ pathHeatTreeMixedBound δ W := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pathHeatTreeMixedBound_nonneg δ W)
  intro f
  apply (ContinuousMap.norm_le _
    (mul_nonneg (pathHeatTreeMixedBound_nonneg δ W) (norm_nonneg f))).mpr
  intro x
  change ‖(δ x.1-1) • f x + pathHeatTreeAncestorReconstruct W f x‖ ≤ _
  calc
    _ ≤ ‖(δ x.1-1) • f x‖ + ‖pathHeatTreeAncestorReconstruct W f x‖ := norm_add_le _ _
    _ ≤ ‖pathHeatTreeDiagonalColumn (fun l => δ l-1)‖ * ‖f‖ +
        pathHeatTreeAncestorBound W * ‖f‖ := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul ((pathHeatTreeDiagonalColumn (fun l => δ l-1)).norm_coe_le_norm x)
          (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
      · exact ((pathHeatTreeAncestorReconstruct W f).norm_coe_le_norm x).trans
          (norm_pathHeatTreeAncestorReconstruct_le W f)
    _ = pathHeatTreeMixedBound δ W * ‖f‖ := by rw [pathHeatTreeMixedBound,add_mul]

theorem pathHeatTreeMixedOperator_bernstein_commute (n L : ℕ) (hn : n ≠ 0)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    pathHeatTreeBernsteinOperator n L (pathHeatTreeMixedOperator δ W f) =
      pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinOperator n L f) := by
  simp only [pathHeatTreeMixedOperator,ContinuousLinearMap.add_apply,map_add,
    pathHeatTreeDiagonalOperator_bernstein_commute,
    pathHeatTreeAncestorOperator_bernstein_commute n L hn]

theorem tendsto_pathHeatTreeMixedBernstein (L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    Tendsto (fun n => pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinOperator n L f))
      atTop (𝓝 (pathHeatTreeMixedOperator δ W f)) :=
  (pathHeatTreeMixedOperator δ W).continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatTreeBernsteinOperator L f)

end HexagonPaper
