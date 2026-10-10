module
public import QuantitativePaper.VectorProfileTraceExtensionSource

@[expose] public section

/-! Literal Xi energy and curvature pairing for the constructed finite
profile. All matrix positivity and derivative identifications are actual
model theorems, rather than independent matrix assumptions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellTraceTime_eq_trace_timeMatrix
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellTraceTime s₀ s₁ β t i a m=
      Matrix.trace (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m) := by
  have hd:=hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm
  unfold vectorProfileCellTraceTime vectorProfileCellHessianTimeMatrix
  rw [hd.deriv]
  exact (hasDerivAt_euclideanOperatorTrace hd).deriv

def vectorProfileCellFieldXi (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (φ φ' : ℝ) (z : VectorProfileCellParameter n×Field n) : Matrix (Fin n) (Fin n) ℝ:=
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i z
  responseXiMatrix (vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m)
    (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i z.1 m) φ φ'

theorem vectorProfileCellFieldXi_curvature_pairing
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) (φ φ' : ℝ) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    let H:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
    let B:=vectorProfileCellBMatrix s₀ s₁ β t i a m
    responseMatrixPair (CFC.sqrt H*B*H) (vectorProfileCellFieldXi s₀ s₁ β t i φ φ' (a,x))=
      φ'*vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x)+
        φ*vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i (a,x)-
        (1-t)*(β*(s₁.m i-s₀.m i))*φ*Matrix.trace (H*H) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hh:=vectorProfileCellHessianMatrix_posDef s₀ s₁ β t hβ i a m hm
  have hb:=vectorProfileCellBMatrix_symmetric s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm
  change responseMatrixPair (CFC.sqrt (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)*
      vectorProfileCellBMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
    (responseXiMatrix _ _ φ φ')=_
  rw [response_Xi_cfc_pairing _ _ _ hh hb]
  unfold responseXiPairing vectorProfileCellFieldCurvaturePairing
    vectorProfileCellCurvaturePairing vectorProfileFieldCurvaturePairingSource
  dsimp only
  ring

theorem vectorProfileCellFieldXi_energy
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) (φ φ' : ℝ) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    let H:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
    responseMatrixFrobeniusSquare (vectorProfileCellFieldXi s₀ s₁ β t i φ φ' (a,x))=
      φ'^2*Matrix.trace H+2*(2*φ'*φ*vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i (a,x)+
        φ^2*vectorProfileFieldTraceTimeSource s₀ s₁ β t i (a,x)) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hh:=vectorProfileCellHessianMatrix_posDef s₀ s₁ β t hβ i a m hm
  have hd:=vectorProfileCellHessianTimeMatrix_symmetric s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm
  have htrace : vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i (a,x)=
      Matrix.trace (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m):=
    (vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ.ne' ht i hi a hq hθ x).trans
      (vectorProfileCellTraceTime_eq_trace_timeMatrix s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm)
  change responseMatrixFrobeniusSquare (responseXiMatrix _ _ φ φ')=_
  rw [response_Xi_cfc_energy _ _ hh hd,responseXiEnergy,
    response_inverse_weight_frobenius _ _ hh hd,htrace]
  unfold vectorProfileFieldTraceTimeSource
  dsimp only
  ring

end QuantitativePaper
