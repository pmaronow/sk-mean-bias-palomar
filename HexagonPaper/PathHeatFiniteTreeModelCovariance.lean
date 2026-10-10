module
public import HexagonPaper.PathHeatFiniteTreeModelRealClockCovariance

@[expose] public section

/-! Literal finite, mixed and tree blocks of the original-index dot-kernel.
Independent finite coordinate rows retain their prescribed derivative dv;
the finite/tree cross block vanishes and the tree block retains all ancestors. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A J : ℕ} {Z : Type*}

theorem pathHeatFiniteTreeMixedKernel_finite_finite (V : ℝ) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ)
    (K : C(Fin (A+J)×I,C(Fin (A+J)×I,ℝ))) (a b : Fin A) (t u : I) :
    pathHeatTreeMixedKernelOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      K (finSumFinEquiv (Sum.inl a),t) (finSumFinEquiv (Sum.inl b),u)=
        (Real.sqrt V)^2*K (finSumFinEquiv (Sum.inl a),1) (finSumFinEquiv (Sum.inl b),1) := by
  rw [pathHeatTreeMixedKernelOperator_apply]
  simp_rw [pathHeatFiniteTree_sum_reindex]
  simp only [pathHeatFiniteTreeDiagonal_finite,pathHeatFiniteTreeAncestor_finite_finite,
    pathHeatFiniteTreeAncestor_finite_tree,smul_eq_mul,zero_mul,zero_add,
    Finset.sum_const_zero,add_zero]
  simp [ite_mul,pow_two,mul_assoc]

theorem pathHeatFiniteTreeMixedKernel_finite_tree (V : ℝ) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ)
    (K : C(Fin (A+J)×I,C(Fin (A+J)×I,ℝ))) (a : Fin A) (j : Fin J) (t u : I) :
    pathHeatTreeMixedKernelOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      K (finSumFinEquiv (Sum.inl a),t) (finSumFinEquiv (Sum.inr j),u)=
        Real.sqrt V*(δ j*K (finSumFinEquiv (Sum.inl a),1) (finSumFinEquiv (Sum.inr j),u)+
          ∑k : Fin J,W j k*K (finSumFinEquiv (Sum.inl a),1) (finSumFinEquiv (Sum.inr k),1)) := by
  rw [pathHeatTreeMixedKernelOperator_apply]
  simp_rw [pathHeatFiniteTree_sum_reindex]
  simp only [pathHeatFiniteTreeDiagonal_finite,pathHeatFiniteTreeDiagonal_tree,
    pathHeatFiniteTreeAncestor_finite_finite,pathHeatFiniteTreeAncestor_finite_tree,
    pathHeatFiniteTreeAncestor_tree_finite,pathHeatFiniteTreeAncestor_tree_tree,
    smul_eq_mul,zero_mul,zero_add,Finset.sum_const_zero,add_zero]
  simp [ite_mul]

theorem pathHeatFiniteTreeRawDerivative_tree_tree
    (dv : Z→Fin A→ℝ) (V : ℝ) (dc : Z→Fin J→C(I,ℝ)) (z : Z)
    (j k : Fin J) (t u : I) :
    pathHeatClockRawKernel (pathHeatFiniteTreeClockDerivatives dv V dc z)
      (finSumFinEquiv (Sum.inr j),t) (finSumFinEquiv (Sum.inr k),u)=
        pathHeatClockRawKernel (dc z) (j,t) (k,u) := by
  simp [pathHeatClockRawKernel_apply,pathHeatFiniteTreeClockDerivatives]

theorem pathHeatFiniteTreeRawDerivative_finite_tree
    (dv : Z→Fin A→ℝ) (V : ℝ) (dc : Z→Fin J→C(I,ℝ)) (z : Z)
    (a : Fin A) (j : Fin J) (t u : I) :
    pathHeatClockRawKernel (pathHeatFiniteTreeClockDerivatives dv V dc z)
      (finSumFinEquiv (Sum.inl a),t) (finSumFinEquiv (Sum.inr j),u)=0 := by
  have hn : finSumFinEquiv (Sum.inl a)≠finSumFinEquiv (Sum.inr j) := by
    intro h
    have hh:=finSumFinEquiv.injective h
    cases hh
  simp only [pathHeatClockRawKernel_apply,hn,ite_false]

theorem pathHeatFiniteTreeDotKernel_finite_finite
    (dv : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V) (dc : Z→Fin J→C(I,ℝ)) (z : Z)
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (a b : Fin A) (t u : I) :
    pathHeatTreeMixedKernelOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      (pathHeatClockRawKernel (pathHeatFiniteTreeClockDerivatives dv V dc z))
      (finSumFinEquiv (Sum.inl a),t) (finSumFinEquiv (Sum.inl b),u)=
        if a=b then dv z a else 0 := by
  rw [pathHeatFiniteTreeMixedKernel_finite_finite,Real.sq_sqrt hV.le]
  simp only [pathHeatClockRawKernel_apply,pathHeatFiniteTreeClockDerivatives]
  by_cases hab : a=b
  · simp [hab,pathHeatFiniteVarianceClockDerivative_apply]
    field_simp
  · simp [hab]

theorem pathHeatFiniteTreeDotKernel_finite_tree
    (dv : Z→Fin A→ℝ) (V : ℝ) (dc : Z→Fin J→C(I,ℝ)) (z : Z)
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (a : Fin A) (j : Fin J) (t u : I) :
    pathHeatTreeMixedKernelOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      (pathHeatClockRawKernel (pathHeatFiniteTreeClockDerivatives dv V dc z))
      (finSumFinEquiv (Sum.inl a),t) (finSumFinEquiv (Sum.inr j),u)=0 := by
  rw [pathHeatFiniteTreeMixedKernel_finite_tree]
  simp only [pathHeatFiniteTreeRawDerivative_finite_tree,mul_zero,Finset.sum_const_zero,add_zero]

theorem pathHeatFiniteTreeDotKernel_tree_tree
    (dv : Z→Fin A→ℝ) (V : ℝ) (dc : Z→Fin J→C(I,ℝ)) (z : Z)
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (j k : Fin J) (t u : I) :
    pathHeatTreeMixedKernelOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      (pathHeatClockRawKernel (pathHeatFiniteTreeClockDerivatives dv V dc z))
      (finSumFinEquiv (Sum.inr j),t) (finSumFinEquiv (Sum.inr k),u)=
        pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z)) (j,t) (k,u) := by
  simp only [pathHeatTreeMixedKernelOperator_apply]
  simp_rw [pathHeatFiniteTree_sum_reindex]
  simp only [pathHeatFiniteTreeDiagonal_tree,pathHeatFiniteTreeAncestor_tree_finite,
    pathHeatFiniteTreeAncestor_tree_tree,smul_eq_mul,zero_mul,Finset.sum_const_zero,zero_add,
    pathHeatFiniteTreeRawDerivative_tree_tree]

end HexagonPaper
