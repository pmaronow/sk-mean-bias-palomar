module
public import HexagonPaper.PathHeatSignedJet
public import HexagonPaper.PathHeatSignedTensor

@[expose] public section

/-! Tensor product score measures and the literal centered signed Hessian
bundle appearing in the manuscript's normalized path Price formula. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]

theorem pathHeatSignedHessian_add (M N : SignedMeasure (X×X)) :
    pathHeatSignedHessian (M+N)=pathHeatSignedHessian M+pathHeatSignedHessian N := by
  ext h k
  exact VectorMeasure.integral_add_vectorMeasure
    (pathHeat_continuous_integrable (pathHeatTensor h k) M)
    (pathHeat_continuous_integrable (pathHeatTensor h k) N)

theorem pathHeatSignedHessian_smul (c : ℝ) (M : SignedMeasure (X×X)) :
    pathHeatSignedHessian (c•M)=c•pathHeatSignedHessian M := by
  ext h k
  exact VectorMeasure.integral_smul_vectorMeasure _ c

/-- Fubini identifies the product measure with the product of actual
first derivative forms, including arbitrary atoms. -/
theorem pathHeatSignedHessian_tensor (S T : SignedMeasure X) (h k : C(X,ℝ)) :
    pathHeatSignedHessian (pathHeatSignedTensor S T) h k=
      pathHeatSignedScore S h*pathHeatSignedScore T k := by
  have hi : Integrable (fun x : X×X=>h x.1*k x.2) (S.variation.prod T.variation) :=
    (BoundedContinuousFunction.mkOfCompact (pathHeatTensor h k)).integrable _
  change (∫ᵛx,h x.1*k x.2 ∂•(S.prod T (ContinuousLinearMap.lsmul ℝ ℝ)))=_
  rw [VectorMeasure.integral_prod_smul hi]
  have he (x : X) : (∫ᵛy,h x*k y ∂•T)=h x*pathHeatSignedScore T k := by
    simpa only [pathHeatSignedScore_apply,smul_eq_mul] using
      (VectorMeasure.integral_fun_smul T (ContinuousLinearMap.lsmul ℝ ℝ) (h x) k)
  simp_rw [he]
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ]ℝ→L[ℝ]ℝ).flip=
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext <;> simp [ContinuousLinearMap.flip_apply,ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,mul_comm]
  rw [hflip]
  have hf : (fun x=>h x*pathHeatSignedScore T k)=
      (fun x=>pathHeatSignedScore T k*h x) := by funext x;exact mul_comm _ _
  rw [hf]
  have hh := VectorMeasure.integral_fun_smul S (ContinuousLinearMap.lsmul ℝ ℝ)
    (pathHeatSignedScore T k) h
  simpa only [pathHeatSignedScore_apply,smul_eq_mul,mul_comm] using hh

def pathHeatCenteredDerivativeMeasure (S P : SignedMeasure X)
    (M Q : SignedMeasure (X×X)) (phi center : ℝ) : SignedMeasure (X×X) :=
  Q+pathHeatSignedTensor S P+pathHeatSignedTensor P S+
    (phi-center)•(M+pathHeatSignedTensor S S)

theorem pathHeatCenteredDerivativeMeasure_hessian (S P : SignedMeasure X)
    (M Q : SignedMeasure (X×X)) (phi center : ℝ) (h k : C(X,ℝ)) :
    pathHeatSignedHessian (pathHeatCenteredDerivativeMeasure S P M Q phi center) h k=
      pathHeatSignedHessian Q h k+
        pathHeatSignedScore S h*pathHeatSignedScore P k+
        pathHeatSignedScore P h*pathHeatSignedScore S k+
        (phi-center)*(pathHeatSignedHessian M h k+
          pathHeatSignedScore S h*pathHeatSignedScore S k) := by
  simp only [pathHeatCenteredDerivativeMeasure,pathHeatSignedHessian_add,
    pathHeatSignedHessian_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    pathHeatSignedHessian_tensor,smul_eq_mul]

end HexagonPaper
