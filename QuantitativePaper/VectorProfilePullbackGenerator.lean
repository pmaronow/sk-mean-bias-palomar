module
public import QuantitativePaper.VectorProfileGradientGenerator
public import QuantitativePaper.VectorProfileLegendrePullback

@[expose] public section

/-! The literal field diffusion generator agrees with the magnetization
generator after the actual chosen Legendre change of variables. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileCellGradient_mem_openSpinCube
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellJointGradient s₀ s₁ β t i (a,x)∈vectorOpenSpinCube n := by
  rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a hq hθ]
  exact fun l=>vectorMagnetization_component_abs_lt_one _ β t a.2.2 (k+2) x l

theorem vectorProfileCellPhysicalHessian_at_gradient
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellPhysicalHessian s₀ s₁ β t i a
      (vectorProfileCellJointGradient s₀ s₁ β t i (a,x))=
      β • hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x := by
  rw [vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i a _
    (vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a hq hθ x),
    vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a hq hθ x,
    vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a hq hθ]
  rfl

theorem vectorProfileCell_pullback_generator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (Z : VectorProfileCellParameter n×Field n→ℝ) (x : Field n)
    (hZ : ContDiffAt ℝ 2 Z (a,vectorProfileCellJointGradient s₀ s₁ β t i (a,x))) :
    deriv (fun r=>Z ((r,a.2),vectorProfileCellJointGradient s₀ s₁ β t i ((r,a.2),x))) a.1+
      fderiv ℝ (fun y=>Z (a,vectorProfileCellJointGradient s₀ s₁ β t i (a,y))) x
        (((1-t)*β^2*vectorProfileMass s₀ s₁ a.2.1 i) •
          vectorProfileCellJointGradient s₀ s₁ β t i (a,x))+
      ((1-t)*β^2)/2*(∑j : Fin n,
        fderiv ℝ (fderiv ℝ (fun y=>Z (a,vectorProfileCellJointGradient s₀ s₁ β t i (a,y)))) x
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))=
      deriv (fun r=>Z ((r,a.2),vectorProfileCellJointGradient s₀ s₁ β t i (a,x))) a.1+
        (1-t)/2*responseMatrixPair
          (vectorProfileCellHessianMatrix s₀ s₁ β t i a
              (vectorProfileCellJointGradient s₀ s₁ β t i (a,x))*
            vectorProfileCellHessianMatrix s₀ s₁ β t i a
              (vectorProfileCellJointGradient s₀ s₁ β t i (a,x)))
          (euclideanOperatorMatrix (hessianOperator (fun m=>Z (a,m))
            (vectorProfileCellJointGradient s₀ s₁ β t i (a,x)))) := by
  let G : ℝ×Field n→Field n:=fun z=>vectorProfileCellJointGradient s₀ s₁ β t i ((z.1,a.2),z.2)
  let W : ℝ×Field n→ℝ:=fun z=>Z ((z.1,a.2),z.2)
  let U : Field n→ℝ:=fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)
  have hG : ContDiffAt ℝ 2 G (a.1,x):=
    (ContDiffAt.comp (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
      (g := vectorProfileCellJointGradient s₀ s₁ β t i) (a.1,x)
      (contDiffAt_vectorProfileCellJointGradient s₀ s₁ β t hβ ht i hi (a,x) hq.2 hθ)
      (by fun_prop)).of_le (by norm_num)
  have hW : ContDiffAt ℝ 2 W (a.1,G (a.1,x)):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2)) (g := Z) (a.1,G (a.1,x)) hZ
    (by fun_prop)
  have hh:=diffusion_generator_pullback (fun j : Fin n=>EuclideanSpace.single j 1)
    W G a.1 x (((1-t)*β^2*vectorProfileMass s₀ s₁ a.2.1 i) • G (a.1,x)) ((1-t)*β^2)
    hW hG (vectorProfileCellGradient_generator_zero s₀ s₁ β t hβ ht i hi a hq.2 hθ x)
  have hU : ContDiffAt ℝ 2 U x:=
    ((contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq.2 hθ).comp
      x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hdg : fderiv ℝ (fun y=>G (a.1,y)) x=hessianOperator U x:=
    (hasFDerivAt_gradient_of_contDiffAt U x hU).fderiv
  simp only [hdg] at hh
  rw [sum_second_hessian_pushforward U (fun m=>W (a.1,m)) x (G (a.1,x)) hU] at hh
  change _=_ at hh
  have hphysical:=vectorProfileCellPhysicalHessian_at_gradient s₀ s₁ β t hβ i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hmat : vectorProfileCellHessianMatrix s₀ s₁ β t i a (G (a.1,x))=
      β • euclideanOperatorMatrix (hessianOperator U x):=by
    unfold vectorProfileCellHessianMatrix
    rw [hphysical,euclideanOperatorMatrix_smul]
  rw [hmat]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,responseMatrixPair,Matrix.transpose_smul,
    Matrix.trace_smul,smul_eq_mul]
  dsimp only [G,W,U] at hh
  unfold responseMatrixPair at hh
  dsimp only [U]
  convert hh using 1 <;> ring

end QuantitativePaper
