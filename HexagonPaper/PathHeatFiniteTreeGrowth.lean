module
public import HexagonPaper.PathHeatNativeSourceExtension
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Literal finite Euclidean and tree supremum growth implies native
joint-index supremum growth, with an explicit harmless larger constant. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators unitInterval NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A J : ℕ}

def pathHeatNativeFiniteVector (p : C(pathHeatFiniteTreeIndex A J,ℝ)) :
    EuclideanSpace ℝ (Fin A) := WithLp.toLp 2 (fun a=>p (Sum.inl a))

def pathHeatNativeTreePath (p : C(pathHeatFiniteTreeIndex A J,ℝ)) (j : Fin J) : C(I,ℝ) :=
  ⟨fun t=>p (Sum.inr (j,t)),p.continuous.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))⟩

theorem norm_pathHeatNativeFiniteVector_le (p : C(pathHeatFiniteTreeIndex A J,ℝ)) :
    ‖pathHeatNativeFiniteVector p‖≤(A:ℝ)*‖p‖ := by
  have he : pathHeatNativeFiniteVector p=
      ∑a : Fin A,EuclideanSpace.single a (p (Sum.inl a)) := by
    ext a
    simp [pathHeatNativeFiniteVector]
  rw [he]
  calc
    _ ≤ ∑a : Fin A,‖EuclideanSpace.single a (p (Sum.inl a))‖ := norm_sum_le _ _
    _ ≤ ∑a : Fin A,‖p‖ := Finset.sum_le_sum (fun a _=>by
      simpa using p.norm_coe_le_norm (Sum.inl a))
    _ = _ := by simp

theorem norm_pathHeatNativeTreePath_le (p : C(pathHeatFiniteTreeIndex A J,ℝ)) (j : Fin J) :
    ‖pathHeatNativeTreePath p j‖≤‖p‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
  intro t
  exact p.norm_coe_le_norm (Sum.inr (j,t))

theorem sum_norm_pathHeatNativeTreePath_le (p : C(pathHeatFiniteTreeIndex A J,ℝ)) :
    (∑j : Fin J,‖pathHeatNativeTreePath p j‖)≤(J:ℝ)*‖p‖ := by
  calc
    _ ≤ ∑j : Fin J,‖p‖ := Finset.sum_le_sum (fun j _=>norm_pathHeatNativeTreePath_le p j)
    _ = _ := by simp

theorem pathHeatFiniteTree_separate_growth_to_joint
    {E K : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (ell : Icc a b×((E×K)×C(pathHeatFiniteTreeIndex A J,ℝ))→ℝ)
    (C : ℝ≥0)
    (hgrowth : ∀z ω p,|ell (z,(ω,p))|≤C*(1+‖ω.1‖+‖pathHeatNativeFiniteVector p‖+
      ∑j : Fin J,‖pathHeatNativeTreePath p j‖)) :
    ∀z ω p,|ell (z,(ω,p))|≤(C*(1+A+J):ℝ≥0)*(1+‖ω.1‖+‖p‖) := by
  intro z ω p
  calc
    _ ≤ C*(1+‖ω.1‖+(A:ℝ)*‖p‖+(J:ℝ)*‖p‖) := (hgrowth z ω p).trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (add_le_add le_rfl (norm_pathHeatNativeFiniteVector_le p))
        (sum_norm_pathHeatNativeTreePath_le p)) C.coe_nonneg)
    _ ≤ _ := by
      simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,NNReal.coe_natCast]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      nlinarith [norm_nonneg ω.1,norm_nonneg p,
        mul_nonneg (Nat.cast_nonneg A : (0:ℝ)≤A) (norm_nonneg ω.1),
        mul_nonneg (Nat.cast_nonneg J : (0:ℝ)≤J) (norm_nonneg ω.1)]

end HexagonPaper
