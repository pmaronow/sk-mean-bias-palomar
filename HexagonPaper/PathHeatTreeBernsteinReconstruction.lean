module
public import HexagonPaper.PathHeatTreeBernsteinCovariance

@[expose] public section

/-! A fixed finite tree reconstructs each physical edge from its own input
edge and the terminal values of its ancestors. The matrix below records the
fixed ancestor coefficients; no probabilistic or differentiability identity
is included among its hypotheses. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathHeatTreeAncestorColumn {L : ℕ} (W : Fin L → Fin L → ℝ) (a : Fin L) :
    C(Fin L × I,ℝ) :=
  ⟨fun x => W x.1 a, continuous_prod_of_discrete_left.mpr (fun l => by
    change Continuous (fun _ : I => W l a)
    exact continuous_const)⟩

def pathHeatTreeAncestorBound {L : ℕ} (W : Fin L → Fin L → ℝ) : ℝ :=
  1 + ∑a : Fin L, ‖pathHeatTreeAncestorColumn W a‖

theorem pathHeatTreeAncestorBound_nonneg {L : ℕ} (W : Fin L → Fin L → ℝ) :
    0 ≤ pathHeatTreeAncestorBound W := by
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

def pathHeatTreeAncestorReconstruct {L : ℕ} (W : Fin L → Fin L → ℝ)
    (f : C(Fin L × I,E)) : C(Fin L × I,E) :=
  ⟨fun x => f x + ∑a : Fin L, W x.1 a • f (a,1),
    f.continuous.add (continuous_prod_of_discrete_left.mpr (fun l => by
      change Continuous (fun _ : I => ∑a : Fin L, W l a • f (a,1))
      exact continuous_const))⟩

@[simp] theorem pathHeatTreeAncestorReconstruct_apply {L : ℕ}
    (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) (x : Fin L × I) :
    pathHeatTreeAncestorReconstruct W f x = f x + ∑a : Fin L, W x.1 a • f (a,1) := rfl

theorem norm_pathHeatTreeAncestorReconstruct_le {L : ℕ}
    (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    ‖pathHeatTreeAncestorReconstruct W f‖ ≤ pathHeatTreeAncestorBound W * ‖f‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (pathHeatTreeAncestorBound_nonneg W) (norm_nonneg f))).mpr
  intro x
  rw [pathHeatTreeAncestorReconstruct_apply]
  calc
    ‖f x + ∑a : Fin L, W x.1 a • f (a,1)‖ ≤
      ‖f x‖ + ∑a : Fin L, ‖W x.1 a • f (a,1)‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ ‖f‖ + ∑a : Fin L, ‖pathHeatTreeAncestorColumn W a‖ * ‖f‖ := by
      apply add_le_add (f.norm_coe_le_norm x)
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul]
      exact mul_le_mul ((pathHeatTreeAncestorColumn W a).norm_coe_le_norm x)
        (f.norm_coe_le_norm (a,1)) (norm_nonneg _) (norm_nonneg _)
    _ = pathHeatTreeAncestorBound W * ‖f‖ := by
      rw [pathHeatTreeAncestorBound,add_mul,one_mul,Finset.sum_mul]

def pathHeatTreeAncestorOperator {L : ℕ} (W : Fin L → Fin L → ℝ) :
    C(Fin L × I,E) →L[ℝ] C(Fin L × I,E) :=
  LinearMap.mkContinuous
    { toFun := pathHeatTreeAncestorReconstruct W
      map_add' := by
        intro f g; ext x
        simp only [pathHeatTreeAncestorReconstruct_apply,ContinuousMap.add_apply,
          smul_add,Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro c f; ext x
        simp only [pathHeatTreeAncestorReconstruct_apply,ContinuousMap.smul_apply,
          RingHom.id_apply,smul_add,Finset.smul_sum,smul_smul]
        congr 1; congr 1; ext a; rw [mul_comm] }
    (pathHeatTreeAncestorBound W) (norm_pathHeatTreeAncestorReconstruct_le W)

@[simp] theorem pathHeatTreeAncestorOperator_apply {L : ℕ}
    (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    pathHeatTreeAncestorOperator W f = pathHeatTreeAncestorReconstruct W f := rfl

theorem norm_pathHeatTreeAncestorOperator_le {L : ℕ} (W : Fin L → Fin L → ℝ) :
    ‖pathHeatTreeAncestorOperator (E:=E) W‖ ≤ pathHeatTreeAncestorBound W :=
  LinearMap.mkContinuous_norm_le _ (pathHeatTreeAncestorBound_nonneg W)
    (norm_pathHeatTreeAncestorReconstruct_le W)

theorem pathHeatTreeAncestorOperator_bernstein_commute (n L : ℕ) (hn : n ≠ 0)
    (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    pathHeatTreeBernsteinOperator n L (pathHeatTreeAncestorOperator W f) =
      pathHeatTreeAncestorOperator W (pathHeatTreeBernsteinOperator n L f) := by
  ext x
  change pathHeatTreeBernsteinSample n L (pathHeatTreeAncestorReconstruct W f) x =
    pathHeatTreeAncestorReconstruct W (pathHeatTreeBernsteinOperator n L f) x
  rw [pathHeatTreeBernsteinSample_apply]
  simp only [pathHeatTreeAncestorOperator_apply,pathHeatTreeAncestorReconstruct_apply,
    smul_add,Finset.sum_add_distrib]
  rw [←pathHeatTreeBernsteinSample_apply n L f x]
  congr 1
  have ht (a : Fin L) : pathHeatTreeBernsteinOperator n L f (a,1) = f (a,1) :=
    pathHeatTreeBernsteinOperator_preserves_terminal n L hn f a
  simp only [ht]
  rw [←Finset.sum_smul,bernstein.probability,one_smul]

theorem tendsto_pathHeatTreeAncestorBernstein (L : ℕ) (W : Fin L → Fin L → ℝ)
    (f : C(Fin L × I,E)) :
    Tendsto (fun n => pathHeatTreeAncestorOperator W (pathHeatTreeBernsteinOperator n L f))
      atTop (𝓝 (pathHeatTreeAncestorOperator W f)) :=
  (pathHeatTreeAncestorOperator W).continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatTreeBernsteinOperator L f)

end HexagonPaper
