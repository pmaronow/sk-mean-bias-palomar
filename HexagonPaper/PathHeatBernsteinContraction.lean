module
public import HexagonPaper.PathHeatCovariance
public import HexagonPaper.PathHeatSignedJet
public import HexagonPaper.PathHeatClockFactor

@[expose] public section

/-! The actual finite Bernstein synthesis map and the exact pullback of a
signed Hessian measure. Its finite covariance contraction is precisely the
signed-measure pairing with the interpolated kernel; all atoms are kept. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
open QuantitativePaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pathHeatBernsteinSynthesis (n : ℕ) : QuantitativePaper.Field (n+1)→L[ℝ]C(I,ℝ) :=
  ∑i : Fin (n+1),(PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (n+1)=>ℝ) i).smulRight (bernstein n i)

theorem pathHeatBernsteinSynthesis_apply (n : ℕ) (g : QuantitativePaper.Field (n+1)) (x : I) :
    pathHeatBernsteinSynthesis n g x=∑i : Fin (n+1),bernstein n i x*g i := by
  simp only [pathHeatBernsteinSynthesis,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)

theorem pathHeatBernsteinSynthesis_basis (n : ℕ) (i : Fin (n+1)) :
    pathHeatBernsteinSynthesis n (EuclideanSpace.single i 1)=bernstein n i := by
  simp [pathHeatBernsteinSynthesis,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,PiLp.single_apply]

theorem norm_pathHeatBernsteinSynthesis_le (n : ℕ) :
    ‖pathHeatBernsteinSynthesis n‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
  intro x
  rw [pathHeatBernsteinSynthesis_apply]
  calc
    ‖∑i : Fin (n+1),bernstein n i x*g i‖≤∑i : Fin (n+1),‖bernstein n i x*g i‖ := norm_sum_le _ _
    _ =∑i : Fin (n+1),bernstein n i x*‖g i‖ := by
      congr 1;ext i;rw [norm_mul,Real.norm_of_nonneg bernstein_nonneg]
    _ ≤∑i : Fin (n+1),bernstein n i x*‖g‖ :=
      Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left
        (PiLp.norm_apply_le g i) bernstein_nonneg)
    _ =‖g‖ := by rw [←Finset.sum_mul,bernstein.probability,one_mul]

theorem pathHeatBernsteinSynthesis_sample (n : ℕ) (f : C(I,ℝ)) :
    pathHeatBernsteinSynthesis n (WithLp.toLp 2 (fun i : Fin (n+1)=>f (bernstein.z i)))=
      bernsteinPathOperator n f := by
  ext x
  rw [pathHeatBernsteinSynthesis_apply,bernsteinPathOperator_apply,bernsteinApproximation.apply]
  rfl

theorem pathHeatBernstein_hessian_coefficients (n : ℕ) (M : SignedMeasure (I×I))
    (i j : Fin (n+1)) :
    pathHeatSignedHessian M
      (pathHeatBernsteinSynthesis n (EuclideanSpace.single i 1))
      (pathHeatBernsteinSynthesis n (EuclideanSpace.single j 1))=
        ∫ᵛx,bernstein n i x.1*bernstein n j x.2 ∂•M := by
  rw [pathHeatBernsteinSynthesis_basis,pathHeatBernsteinSynthesis_basis]
  rfl

theorem pathHeatKernelSample_uncurry_sum (n : ℕ) (K : C(I,C(I,ℝ))) :
    (pathKernelSample n K).uncurry=
      ∑i : Fin (n+1),∑j : Fin (n+1),
        K (bernstein.z i) (bernstein.z j) • pathHeatTensor (bernstein n i) (bernstein n j) := by
  ext x
  change pathKernelSample n K x.1 x.2=_
  rw [pathKernelSample_apply]
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,pathHeatTensor,
    ContinuousMap.coe_mk,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _=>by ring)

/-- Actual finite covariance/Hessian contraction, with the signed measure
unchanged by the finite interpolation. -/
theorem pathHeatBernstein_signed_covariance_contraction (n : ℕ)
    (K : C(I,C(I,ℝ))) (M : SignedMeasure (I×I)) :
    (∑i : Fin (n+1),∑j : Fin (n+1),K (bernstein.z i) (bernstein.z j)*
      pathHeatSignedHessian M
        (pathHeatBernsteinSynthesis n (EuclideanSpace.single i 1))
        (pathHeatBernsteinSynthesis n (EuclideanSpace.single j 1)))=
          signedContraction (BoundedContinuousFunction.mkOfCompact (pathKernelSample n K).uncurry) M := by
  change _=pathHeatSignedScore M (pathKernelSample n K).uncurry
  rw [pathHeatKernelSample_uncurry_sum,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,pathHeatBernsteinSynthesis_basis]
  rfl

theorem norm_pathHeatKernel_uncurry_le (K : C(I,C(I,ℝ))) : ‖K.uncurry‖≤‖K‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
  intro x
  exact ((K x.1).norm_coe_le_norm x.2).trans (K.norm_coe_le_norm x.1)

theorem tendsto_pathHeatKernelPairingSample (K : C(I,C(I,ℝ)))
    (M : ℕ→SignedMeasure (I×I)) (N : SignedMeasure (I×I)) (C : ℝ)
    (hM : ∀n,signedTV (M n)≤C)
    (hN : Tendsto (fun n=>signedTV (M n-N)) atTop (𝓝 0)) :
    Tendsto (fun n=>signedContraction
      (BoundedContinuousFunction.mkOfCompact (pathKernelSample n K).uncurry) (M n)) atTop
      (𝓝 (signedContraction (BoundedContinuousFunction.mkOfCompact K.uncurry) N)) := by
  have hk := pathKernel_norm_sub_tendsto_zero_of_tendsto
    (fun n=>pathKernelSample n K) K (tendsto_pathKernelSample K)
  have hf : Tendsto (fun n=>‖BoundedContinuousFunction.mkOfCompact (pathKernelSample n K).uncurry-
      BoundedContinuousFunction.mkOfCompact K.uncurry‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _=>norm_nonneg _) (fun n=>?_) hk
    rw [←BoundedContinuousFunction.mkOfCompact_sub,BoundedContinuousFunction.norm_mkOfCompact]
    have he : (pathKernelSample n K).uncurry-K.uncurry=(pathKernelSample n K-K).uncurry := by
      ext x;rfl
    rw [he]
    exact norm_pathHeatKernel_uncurry_le _
  exact tendsto_signedContraction _ _ _ N C (by
    exact (ENNReal.toReal_nonneg.trans (hM 0))) hM
      (tendsto_iff_norm_sub_tendsto_zero.mpr hf) hN

end HexagonPaper
