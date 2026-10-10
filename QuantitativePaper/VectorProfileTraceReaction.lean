module
public import QuantitativePaper.VectorProfileSecondVariationGenerator
public import FourPapersCommon.HessianLocalCalculus

@[expose] public section

/-! The trace reaction in magnetization coordinates is derived from the
actual Legendre time PDE and literal inverse Hessian. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellTrace (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  euclideanOperatorTrace (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)

def vectorProfileCellTraceHessian (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Field n→L[ℝ]Field n:=
  hessianOperator (vectorProfileCellTrace s₀ s₁ β t i a) m

theorem contDiffAt_vectorProfileCellTrace (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellTrace s₀ s₁ β t i z.1 z.2) (a,m) :=
  ContDiffAt.comp (f := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2)
    (g := euclideanOperatorTraceCLM (n:=n)) (a,m)
    euclideanOperatorTraceCLM.contDiff.contDiffAt
    (contDiffAt_vectorProfileCellPhysicalHessian s₀ s₁ β t hβ ht i hi a hq hθ m hm)

theorem hasDerivAt_vectorProfileCellEnergyHessian_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun q=>vectorProfileCellEnergyHessian s₀ s₁ β t i (q,a.2) m)
      (((1-t)/2) • (vectorProfileCellTraceHessian s₀ s₁ β t i a m+
        (2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Field n→L[ℝ]Field n))) a.1 := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i
    ((z.1,a.2),z.2)
  have hU : ContDiffAt ℝ ∞ U (a.1,m):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
    (g := vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i) (a.1,m)
    (contDiffAt_vectorProfileCellEnergyLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  have hd:=hasDerivAt_partial_hessian U a.1 m hU
  have he : (fun y=>deriv (fun q=>U (q,y)) a.1)=ᶠ[𝓝 m]
      (fun y=>(1-t)/2*vectorProfileCellTrace s₀ s₁ β t i a y+
        (1-t)*(β*vectorProfileMass s₀ s₁ a.2.1 i)/2*‖y‖^2):=by
    filter_upwards [(isOpen_vectorOpenSpinCube n).mem_nhds hm] with y hy
    exact (hasDerivAt_vectorProfileCellEnergyLegendrePotential_time s₀ s₁ β t hβ ht i hi
      a hq hθ y hy).deriv
  have hT : ContDiffAt ℝ 2 (vectorProfileCellTrace s₀ s₁ β t i a) m:=
    ((contDiffAt_vectorProfileCellTrace s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hN : ContDiffAt ℝ 2 (fun y : Field n=>‖y‖^2) m:=(contDiff_norm_sq ℝ).contDiffAt
  apply hd.congr_deriv
  rw [hessianOperator_congr_of_eventuallyEq _ _ m he,
    hessianOperator_add_at _ _ m (contDiffAt_const.mul hT) (contDiffAt_const.mul hN),
    hessianOperator_const_mul_at _ m _ hT,hessianOperator_const_mul_at _ m _ hN,
    hessianOperator_norm_sq]
  apply ContinuousLinearMap.ext
  intro w
  change (((1-t)/2) • (vectorProfileCellTraceHessian s₀ s₁ β t i a m)) w+
    (((1-t)*(β*vectorProfileMass s₀ s₁ a.2.1 i)/2) • ((2 : ℝ) • (1 : Field n→L[ℝ]Field n))) w=_
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    smul_add,smul_smul,vectorProfileCellTraceHessian]
  module

theorem hasDerivAt_vectorProfileCellPhysicalHessian_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m)
      (-((1-t)/2) • (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m*
        (vectorProfileCellTraceHessian s₀ s₁ β t i a m+
          (2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Field n→L[ℝ]Field n))*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)) a.1 := by
  have hd:=hasDerivAt_ringInverse_comp
    (fun q=>vectorProfileCellEnergyHessian s₀ s₁ β t i (q,a.2) m) _ a.1
    (hasDerivAt_vectorProfileCellEnergyHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (vectorProfileEnergyHessian_isUnit s₀ s₁ β t hβ (vectorProfileCellOverlap a.1)
      (k+2) a.2.1 a.2.2 m hm)
  apply hd.congr_deriv
  ext w
  simp only [vectorProfileCellPhysicalHessian,ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,map_smul,neg_smul,neg_mul,
    ContinuousLinearMap.add_apply]

theorem vectorProfileCellTrace_generator (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellTrace s₀ s₁ β t i (q,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m))=
      -(1-t)*(β*vectorProfileMass s₀ s₁ a.2.1 i)*Matrix.trace
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  let h:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
  let N:=euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m)
  let Hdot:=deriv (fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m) a.1
  have hJet : euclideanOperatorMatrix Hdot=
      -((1-t)/2) • (h*(N+(2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Matrix (Fin n) (Fin n) ℝ))*h):=by
    dsimp only [Hdot]
    rw [(hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi
      a hq hθ m hm).deriv]
    simp only [euclideanOperatorMatrix_smul,euclideanOperatorMatrix_mul,
      euclideanOperatorMatrix_add,euclideanOperatorMatrix_one]
    rfl
  have hDeriv := (hasDerivAt_euclideanOperatorTrace
    (hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm)).deriv
  have hEq : deriv (fun q=>vectorProfileCellTrace s₀ s₁ β t i (q,a.2) m) a.1=
      Matrix.trace (euclideanOperatorMatrix Hdot):=by
    dsimp only [Hdot]
    rw [(hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv]
    exact hDeriv
  rw [hEq]
  exact response_generator_trace h N (euclideanOperatorMatrix Hdot) (1-t)
    (β*vectorProfileMass s₀ s₁ a.2.1 i)
    (vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ i a m hm) hJet

end QuantitativePaper
