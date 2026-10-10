module
public import HexagonPaper.PathHeatFiniteTreeModel

@[expose] public section

/-! Literal physical field values of the finite-coordinate/tree factory.
The finite coordinates are genuine independent Wiener terminal observations
with their actual prescribed Gaussian variances, including zero variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A J : ℕ} {Z : Type*}

theorem pathHeatFiniteTree_sum_reindex {R : Type*} [AddCommMonoid R]
    (f : Fin (A+J)→R) :
    (∑l : Fin (A+J),f l)=(∑a : Fin A,f (finSumFinEquiv (Sum.inl a)))+
      ∑j : Fin J,f (finSumFinEquiv (Sum.inr j)) := by
  rw [←finSumFinEquiv.sum_comp f,Fintype.sum_sum_type]

@[simp] theorem pathHeatFiniteTreeDiagonal_finite (δ : Fin J→ℝ) (a : Fin A) :
    pathHeatFiniteTreeDiagonal δ (finSumFinEquiv (Sum.inl a))=0 := by
  simp [pathHeatFiniteTreeDiagonal]

@[simp] theorem pathHeatFiniteTreeDiagonal_tree (δ : Fin J→ℝ) (j : Fin J) :
    pathHeatFiniteTreeDiagonal (A:=A) δ (finSumFinEquiv (Sum.inr j))=δ j := by
  simp [pathHeatFiniteTreeDiagonal]

@[simp] theorem pathHeatFiniteTreeAncestor_finite_finite (V : ℝ)
    (W : Fin J→Fin J→ℝ) (a b : Fin A) :
    pathHeatFiniteTreeAncestor V W (finSumFinEquiv (Sum.inl a))
      (finSumFinEquiv (Sum.inl b))=if a=b then Real.sqrt V else 0 := by
  simp [pathHeatFiniteTreeAncestor]

@[simp] theorem pathHeatFiniteTreeAncestor_finite_tree (V : ℝ)
    (W : Fin J→Fin J→ℝ) (a : Fin A) (j : Fin J) :
    pathHeatFiniteTreeAncestor V W (finSumFinEquiv (Sum.inl a))
      (finSumFinEquiv (Sum.inr j))=0 := by
  simp [pathHeatFiniteTreeAncestor]

@[simp] theorem pathHeatFiniteTreeAncestor_tree_finite (V : ℝ)
    (W : Fin J→Fin J→ℝ) (j : Fin J) (a : Fin A) :
    pathHeatFiniteTreeAncestor V W (finSumFinEquiv (Sum.inr j))
      (finSumFinEquiv (Sum.inl a))=0 := by
  simp [pathHeatFiniteTreeAncestor]

@[simp] theorem pathHeatFiniteTreeAncestor_tree_tree (V : ℝ)
    (W : Fin J→Fin J→ℝ) (j k : Fin J) :
    pathHeatFiniteTreeAncestor (A:=A) V W (finSumFinEquiv (Sum.inr j))
      (finSumFinEquiv (Sum.inr k))=W j k := by
  simp [pathHeatFiniteTreeAncestor]

theorem pathHeatFiniteTreeField_finite (V : ℝ) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ)
    (f : C(Fin (A+J)×I,ℝ)) (a : Fin A) (t : I) :
    pathHeatTreeMixedOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      f (finSumFinEquiv (Sum.inl a),t)=Real.sqrt V*f (finSumFinEquiv (Sum.inl a),1) := by
  rw [pathHeatTreeMixedOperator_apply,pathHeatFiniteTree_sum_reindex]
  simp only [pathHeatFiniteTreeDiagonal_finite,pathHeatFiniteTreeAncestor_finite_finite,
    pathHeatFiniteTreeAncestor_finite_tree,smul_eq_mul,zero_mul,zero_add,
    Finset.sum_const_zero,add_zero]
  simp [ite_mul]

theorem pathHeatFiniteTreeField_tree (V : ℝ) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ)
    (f : C(Fin (A+J)×I,ℝ)) (j : Fin J) (t : I) :
    pathHeatTreeMixedOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
      f (finSumFinEquiv (Sum.inr j),t)=δ j*f (finSumFinEquiv (Sum.inr j),t)+
        ∑k : Fin J,W j k*f (finSumFinEquiv (Sum.inr k),1) := by
  rw [pathHeatTreeMixedOperator_apply,pathHeatFiniteTree_sum_reindex]
  simp only [pathHeatFiniteTreeDiagonal_tree,pathHeatFiniteTreeAncestor_tree_finite,
    pathHeatFiniteTreeAncestor_tree_tree,smul_eq_mul,zero_mul,Finset.sum_const_zero,zero_add]

theorem hasLaw_pathHeatFiniteTreeFiniteCoordinate
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (z : Z) (a : Fin A) :
    HasLaw (fun w=>pathHeatTreeMixedOperator (pathHeatFiniteTreeDiagonal δ)
      (pathHeatFiniteTreeAncestor V W)
      (pathHeatFlatClockPath (A+J) (pathHeatFiniteTreeClocks v V hV hv hvV c z) w)
      (finSumFinEquiv (Sum.inl a),1))
      (gaussianReal 0 (v z a).toNNReal) (pathHeatWienerMeshBase (J:=Fin (A+J))) := by
  simp_rw [pathHeatFiniteTreeField_finite]
  have h := gaussianReal_const_mul
    (hasLaw_pathHeatFlatClockEvaluation (pathHeatFiniteTreeClocks v V hV hv hvV c z)
      (finSumFinEquiv (Sum.inl a),1)) (Real.sqrt V)
  have he : NNReal.mk ((Real.sqrt V)^2) (sq_nonneg _) *
      (pathHeatFiniteTreeClocks v V hV hv hvV c z (finSumFinEquiv (Sum.inl a)) 1).1.toNNReal=
        (v z a).toNNReal := by
    rw [pathHeatFiniteTreeClocks_finite]
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _
      (pathHeatFiniteVarianceClock (v z a) V hV (hv z a) (hvV z a) 1).property.1,
      Real.coe_toNNReal _ (hv z a)]
    exact pathHeatFiniteVarianceClock_terminal_variance (v z a) V hV (hv z a) (hvV z a)
  simpa only [mul_zero,he] using h

end HexagonPaper
