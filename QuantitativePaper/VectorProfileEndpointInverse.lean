module
public import QuantitativePaper.VectorProfileEndpointSmooth
public import QuantitativePaper.VectorProfileLegendreCoordinates
public import FourPapersCommon.SmoothParameterInverseWithin

@[expose] public section

/-! Actual smooth local extensions of the selected Legendre inverse at
closed profile parameters. The extension is supplied by the genuine IFT. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileTailRecursion_eq_clamped_profiles_all_theta
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap) (θ : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (hj : j≤k+2) :
    vectorProfileTailRecursion s₀ s₁ β t q θ p j=
      vectorProfileRecursion (vectorClampedScheme s₀ q q.property)
        (vectorClampedScheme s₁ q q.property) β t θ p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorProfileTailRecursion,vectorProfileRecursion,ih (by omega)]
    have hi : k+1+1-j=(k+1-j)+1:=by omega
    have hi' : k+1+2-j=(k+2-j)+1:=by omega
    rw [hi,hi',vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ]
    unfold vectorProfileMass
    rw [vectorClampedScheme_mass_succ,vectorClampedScheme_mass_succ]
    simp only [show k+1-j+1=k+2-j by omega]

theorem contDiff_vectorProfileJointPotential_all_theta
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2) :
    ContDiff ℝ ∞ (vectorProfileJointPotential (n:=n) s₀ s₁ β t q j) := by
  let L : (VectorProfileParameter n×Field n)→L[ℝ](ℝ×VectorParameter n):=
    ((ContinuousLinearMap.fst ℝ ℝ (Couplings n×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (VectorProfileParameter n) (Field n))).prod
    (((ContinuousLinearMap.snd ℝ ℝ (Couplings n×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (VectorProfileParameter n) (Field n))).prod
      (ContinuousLinearMap.snd ℝ (VectorProfileParameter n) (Field n)))
  have he : vectorProfileJointPotential (n:=n) s₀ s₁ β t q j=
      (vectorProfileJointFunction (vectorClampedScheme s₀ q q.property)
        (vectorClampedScheme s₁ q q.property) β t j) ∘ L:=by
    funext z
    exact congrFun (vectorProfileTailRecursion_eq_clamped_profiles_all_theta s₀ s₁ β t q z.1.1 z.1.2 j hj) z.2
  rw [he]
  exact (contDiff_vectorProfileJointFunction_all_theta _ _ β t j).comp L.contDiff

theorem contDiffAt_vectorProfileJointGradient_all_theta
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (z : VectorProfileParameter n×Field n) :
    ContDiffAt ℝ ∞ (vectorProfileJointGradient s₀ s₁ β t q j) z :=
  contDiffAt_partial_gradient _ z
    (contDiff_vectorProfileJointPotential_all_theta s₀ s₁ β t q j hj).contDiffAt

theorem exists_vectorProfileLegendreField_smooth_extension_closed_theta
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Icc (0:ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ∃ψ : VectorProfileParameter n×Field n→Field n,
      ContDiffAt ℝ ∞ ψ (a,m) ∧
      (fun z : VectorProfileParameter n×Field n=>
        vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2)=ᶠ[
          𝓝[({a : VectorProfileParameter n|a.1∈Icc (0:ℝ) 1})×ˢvectorOpenSpinCube n] (a,m)]ψ := by
  let F:=vectorProfileJointGradient (n:=n) s₀ s₁ β t q j
  let Y : VectorProfileParameter n×Field n→Field n:=
    fun z=>vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2
  let x:=Y (a,m)
  let S:=vectorProfileInverseScheme s₀ s₁ q a.1
  have hF : ContDiffAt ℝ ∞ F (a,x):=
    contDiffAt_vectorProfileJointGradient_all_theta s₀ s₁ β t q j hj (a,x)
  have hx:F (a,x)=m:=vectorProfileJointGradient_legendreField s₀ s₁ β t q j hj a.1 hθ a.2 m hm
  have heq : (fun y=>F (a,y))=vectorMagnetization S β t a.2 j:=by
    funext y
    exact vectorProfileJointGradient_eq_inverseScheme s₀ s₁ β t q j hj a.1 hθ a.2 y
  have hd : HasFDerivAt (fun y=>F (a,y))
      ((fderiv ℝ F (a,x)).comp (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))) x:=by
    convert hF.differentiableAt (by simp) |>.hasFDerivAt.comp x
      ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1 <;>
      first | rfl | (ext w; simp)
  rw [heq] at hd
  have hpartial : (fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))=
      vectorFieldHessian S β t a.2 j x:=
    hd.unique (hasFDerivAt_vectorMagnetization S β t a.2 j x)
  have hInv : ((fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))).IsInvertible:=by
    rw [hpartial,←vectorFieldHessianEquiv_coe S β t a.2 j x]
    exact ContinuousLinearMap.isInvertible_equiv
  apply exists_smooth_parameter_inverse_within F Y {a|a.1∈Icc (0:ℝ) 1}
    (vectorOpenSpinCube n) (isOpen_vectorOpenSpinCube n) a m x hθ hm hF hx hInv
  · intro b hb
    have he : (fun y=>F (b,y))=vectorMagnetization
        (vectorProfileInverseScheme s₀ s₁ q b.1) β t b.2 j:=by
      funext y
      exact vectorProfileJointGradient_eq_inverseScheme s₀ s₁ β t q j hj b.1 hb b.2 y
    rw [he]
    exact vectorMagnetization_injective _ β t b.2 j
  · intro z hz
    exact vectorProfileJointGradient_legendreField s₀ s₁ β t q j hj z.1.1 hz.1 z.1.2 z.2 hz.2

end QuantitativePaper
