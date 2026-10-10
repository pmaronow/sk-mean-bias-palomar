module
public import QuantitativePaper.VectorProfilePullbackGenerator
public import QuantitativePaper.VectorProfileTraceTimeGenerator

@[expose] public section

/-! Literal original-field generator equations for the three actual
Legendre observables used in the second-profile variation proof. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_vectorProfileCellSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellSecondVariation s₀ s₁ β t i z.1 z.2) (a,m) := by
  let U : ℝ×(ℝ×((Couplings n×ℝ)×Field n))→ℝ:=fun z=>
    vectorProfileCellFirstVariation s₀ s₁ β t i (z.2.1,z.1,z.2.2.1) z.2.2.2
  have hU : ContDiffAt ℝ ∞ U (a.2.1,a.1,a.2.2,m):=ContDiffAt.comp
    (f := fun z : ℝ×(ℝ×((Couplings n×ℝ)×Field n))=>((z.2.1,z.1,z.2.2.1),z.2.2.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellFirstVariation s₀ s₁ β t i z.1 z.2) (a.2.1,a.1,a.2.2,m)
    (contDiffAt_vectorProfileCellFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  have hD:=contDiffAt_partialParamDerivative (1 : ℝ) U (a.2.1,a.1,a.2.2,m) hU
  have hh:=ContDiffAt.comp
    (f := fun z : VectorProfileCellParameter n×Field n=>(z.1.2.1,z.1.1,z.1.2.2,z.2))
    (g := partialParamDerivative (1 : ℝ) U) (a,m) hD (by fun_prop)
  simpa only [Function.comp_def,partialParamDerivative,fderiv_apply_one_eq_deriv,U,
    vectorProfileCellFirstVariation,vectorProfileCellSecondVariation] using hh

def vectorProfileCellFieldGenerator (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (F : VectorProfileCellParameter n×Field n→ℝ) (a : VectorProfileCellParameter n)
    (x : Field n) : ℝ:=
  deriv (fun r=>F ((r,a.2),x)) a.1+
    fderiv ℝ (fun y=>F (a,y)) x
      (((1-t)*β^2*vectorProfileMass s₀ s₁ a.2.1 i) •
        vectorProfileCellJointGradient s₀ s₁ β t i (a,x))+
    ((1-t)*β^2)/2*(∑j : Fin n,fderiv ℝ (fderiv ℝ (fun y=>F (a,y))) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))

def vectorProfileCellFieldSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileCellSecondVariation s₀ s₁ β t i z.1
    (vectorProfileCellJointGradient s₀ s₁ β t i z)

def vectorProfileCellFieldCurvaturePairing (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileCellCurvaturePairing s₀ s₁ β t i z.1
    (vectorProfileCellJointGradient s₀ s₁ β t i z)

def vectorProfileCellFieldTraceTime (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileCellTraceTime s₀ s₁ β t i z.1
    (vectorProfileCellJointGradient s₀ s₁ β t i z)

theorem vectorProfileCellFieldSecondVariation_generator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    vectorProfileCellFieldGenerator s₀ s₁ β t i
      (vectorProfileCellFieldSecondVariation s₀ s₁ β t i) a x=
      (1-t)*responseMatrixFrobeniusSquare
        (CFC.sqrt (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hZ:=contDiffAt_vectorProfileCellSecondVariation s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm
  have hp:=vectorProfileCell_pullback_generator s₀ s₁ β t hβ.ne' ht i hi a hq hθ
    (fun z=>vectorProfileCellSecondVariation s₀ s₁ β t i z.1 z.2) x (hZ.of_le (by norm_num))
  change vectorProfileCellFieldGenerator s₀ s₁ β t i
    (vectorProfileCellFieldSecondVariation s₀ s₁ β t i) a x=_
  unfold vectorProfileCellFieldGenerator vectorProfileCellFieldSecondVariation
  rw [hp]
  exact vectorProfileCellSecondVariation_frobenius_source s₀ s₁ β t hβ ht i hi a hq hθ m hm

theorem vectorProfileCellFieldCurvaturePairing_generator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    vectorProfileCellFieldGenerator s₀ s₁ β t i
      (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i) a x=
      (1-t)*(β*(s₁.m i-s₀.m i))*Matrix.trace
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)+
        2*Matrix.trace
          (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
            vectorProfileCellBMatrix s₀ s₁ β t i a m*
            vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hZ:=contDiffAt_vectorProfileCellCurvaturePairing s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hp:=vectorProfileCell_pullback_generator s₀ s₁ β t hβ ht i hi a hq hθ
    (fun z=>vectorProfileCellCurvaturePairing s₀ s₁ β t i z.1 z.2) x (hZ.of_le (by norm_num))
  change vectorProfileCellFieldGenerator s₀ s₁ β t i
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i) a x=_
  unfold vectorProfileCellFieldGenerator vectorProfileCellFieldCurvaturePairing
  rw [hp]
  exact vectorProfileCellCurvaturePairing_generator s₀ s₁ β t hβ ht i hi a hq hθ m hm

theorem vectorProfileCellFieldTraceTime_generator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    vectorProfileCellFieldGenerator s₀ s₁ β t i
      (vectorProfileCellFieldTraceTime s₀ s₁ β t i) a x=
      2*responseMatrixFrobeniusSquare
        (CFC.sqrt ((vectorProfileCellHessianMatrix s₀ s₁ β t i a m)⁻¹)*
          vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hZ:=contDiffAt_vectorProfileCellTraceTime s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm
  have hp:=vectorProfileCell_pullback_generator s₀ s₁ β t hβ.ne' ht i hi a hq hθ
    (fun z=>vectorProfileCellTraceTime s₀ s₁ β t i z.1 z.2) x (hZ.of_le (by norm_num))
  change vectorProfileCellFieldGenerator s₀ s₁ β t i
    (vectorProfileCellFieldTraceTime s₀ s₁ β t i) a x=_
  unfold vectorProfileCellFieldGenerator vectorProfileCellFieldTraceTime
  rw [hp]
  exact vectorProfileCellTraceTime_generator s₀ s₁ β t hβ ht i hi a hq hθ m hm

end QuantitativePaper
