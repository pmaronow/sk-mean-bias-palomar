module
public import HexagonPaper.PathHeatTreeBernsteinCovariance

@[expose] public section

/-! Exact finite covariance contraction for all edges simultaneously. The
Hessian measure itself is unchanged by the finite Gaussian coordinate map. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem pathHeatTreeBernstein_hessian_coefficients (n L : ℕ)
    (M : SignedMeasure ((Fin L × I) × (Fin L × I)))
    (p q : Fin L × Fin (n+1)) :
    pathHeatSignedHessian M
      (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1))
      (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single q 1)) =
        ∫ᵛx, pathHeatTreeBernsteinBasis n L p x.1 *
          pathHeatTreeBernsteinBasis n L q x.2 ∂•M := by
  rw [pathHeatTreeBernsteinSynthesis_basis,pathHeatTreeBernsteinSynthesis_basis]
  rfl

theorem pathHeatTreeKernelSample_uncurry_sum (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,ℝ))) :
    (pathHeatTreeKernelSample n L K).uncurry =
      ∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
        K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) •
          pathHeatTensor (pathHeatTreeBernsteinBasis n L p)
            (pathHeatTreeBernsteinBasis n L q) := by
  ext x
  change pathHeatTreeKernelSample n L K x.1 x.2 = _
  rw [pathHeatTreeKernelSample_apply]
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,pathHeatTensor,
    ContinuousMap.coe_mk,pathHeatTreeBernsteinBasis_apply,smul_eq_mul,
    Fintype.sum_prod_type]
  simp only [ite_mul,mul_ite,mul_zero,zero_mul,Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero,Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem pathHeatTreeBernstein_signed_covariance_contraction (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : SignedMeasure ((Fin L × I) × (Fin L × I))) :
    (∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
      K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) *
        pathHeatSignedHessian M
          (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1))
          (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single q 1))) =
      signedContraction
        (BoundedContinuousFunction.mkOfCompact (pathHeatTreeKernelSample n L K).uncurry) M := by
  change _ = pathHeatSignedScore M (pathHeatTreeKernelSample n L K).uncurry
  rw [pathHeatTreeKernelSample_uncurry_sum,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,pathHeatTreeBernsteinSynthesis_basis]
  rfl

theorem norm_pathHeatTreeKernel_uncurry_le (L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,ℝ))) : ‖K.uncurry‖ ≤ ‖K‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
  intro x
  exact ((K x.1).norm_coe_le_norm x.2).trans (K.norm_coe_le_norm x.1)

theorem tendsto_pathHeatTreeKernelPairingSample (L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : ℕ → SignedMeasure ((Fin L × I) × (Fin L × I)))
    (N : SignedMeasure ((Fin L × I) × (Fin L × I))) (C : ℝ)
    (hM : ∀ n, signedTV (M n) ≤ C)
    (hN : Tendsto (fun n => signedTV (M n-N)) atTop (𝓝 0)) :
    Tendsto (fun n => signedContraction
      (BoundedContinuousFunction.mkOfCompact (pathHeatTreeKernelSample n L K).uncurry) (M n)) atTop
      (𝓝 (signedContraction (BoundedContinuousFunction.mkOfCompact K.uncurry) N)) := by
  have hk := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L
    (fun n => pathHeatTreeKernelSample n L K) K (tendsto_pathHeatTreeKernelSample L K)
  have hf : Tendsto (fun n => ‖BoundedContinuousFunction.mkOfCompact
      (pathHeatTreeKernelSample n L K).uncurry-BoundedContinuousFunction.mkOfCompact K.uncurry‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hk
    rw [←BoundedContinuousFunction.mkOfCompact_sub,BoundedContinuousFunction.norm_mkOfCompact]
    have he : (pathHeatTreeKernelSample n L K).uncurry-K.uncurry =
        (pathHeatTreeKernelSample n L K-K).uncurry := by ext x; rfl
    rw [he]
    exact norm_pathHeatTreeKernel_uncurry_le L _
  exact tendsto_signedContraction _ _ _ N C (ENNReal.toReal_nonneg.trans (hM 0)) hM
    (tendsto_iff_norm_sub_tendsto_zero.mpr hf) hN

end HexagonPaper
