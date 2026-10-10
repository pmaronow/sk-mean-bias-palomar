module
public import QuantitativePaper.VectorProfileLegendreProfileCurve
public import QuantitativePaper.VectorProfileTraceTimePullback

@[expose] public section

/-! The curvature-pairing field observable uses only retained profile and
spatial jets. This avoids taking a time derivative at a zero-variance node. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellTrace_profile_eq_neg_pairing
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (a : VectorProfileCellParameter n) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun θ=>vectorProfileCellTrace s₀ s₁ β t i (a.1,θ,a.2.2) m) a.2.1=
      -vectorProfileCellCurvaturePairing s₀ s₁ β t i a m := by
  have hd:=(hasDerivAt_euclideanOperatorTrace
    (hasDerivAt_vectorProfileCellPhysicalHessian_profile s₀ s₁ β t hβ ht i a hθ m hm)).deriv
  change deriv (fun θ=>vectorProfileCellTrace s₀ s₁ β t i (a.1,θ,a.2.2) m) a.2.1=_ at hd
  rw [hd]
  unfold euclideanOperatorTrace vectorProfileCellCurvaturePairing
  simp only [euclideanOperatorMatrix_mul,euclideanOperatorMatrix_neg,Matrix.neg_mul,
    Matrix.trace_neg]
  congr 1
  change Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
    vectorProfileCellBMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m)=_
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle'
    (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
    (vectorProfileCellBMatrix s₀ s₁ β t i a m) (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)

theorem vectorProfileCellCurvaturePairing_retained_formula
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) :
    vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x)=
      β*(-deriv (fun θ=>vectorProfileCellRawTrace s₀ s₁ β t i (a.1,θ,a.2.2) x) a.2.1+
        fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i a) x
          ((Ring.inverse (hessianOperator
            (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x))) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  let Y : ℝ→Field n:=fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m)
  let W : ℝ×Field n→ℝ:=fun z=>vectorProfileCellRawTrace s₀ s₁ β t i (a.1,z.1,a.2.2) z.2
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hY0 : Y a.2.1=x:=vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hY : ContDiffAt ℝ ∞ Y a.2.1:=ContDiffAt.comp
    (f := fun θ : ℝ=>((a.1,θ,a.2.2),m)) (g := vectorProfileCellLegendreField s₀ s₁ β t i) a.2.1
    (contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hW : ContDiffAt ℝ ∞ W (a.2.1,Y a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>vectorProfileCellRawTrace s₀ s₁ β t i z.1 z.2)
    (a.2.1,Y a.2.1)
    (contDiffAt_vectorProfileCellRawTrace s₀ s₁ β t hβ ht i hi a hq.2 hθ (Y a.2.1)) (by fun_prop)
  have he : (fun θ=>vectorProfileCellTrace s₀ s₁ β t i (a.1,θ,a.2.2) m)=ᶠ[𝓝 a.2.1]
      (fun θ=>β*W (θ,Y θ)):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    unfold vectorProfileCellTrace
    rw [vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i (a.1,θ,a.2.2) m hm]
    have heU : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),y))=
        vectorRecursion (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) θ)
          β t a.2.2 (k+2):=vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi (a.1,θ,a.2.2)
            ⟨hq.1.le,hq.2.le⟩ ⟨hθ'.1.le,hθ'.2.le⟩
    dsimp only [W,vectorProfileCellRawTrace,Y]
    rw [heU]
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_smul,Matrix.trace_smul,smul_eq_mul]
    rfl
  have hCalc:=he.deriv_eq
  rw [vectorProfileCellTrace_profile_eq_neg_pairing s₀ s₁ β t hβ ht i a hθ m hm,
    deriv_const_mul_field,
    deriv_time_curve_composition W Y a.2.1 (hW.of_le (by norm_num)) (hY.of_le (by norm_num)),
    (hasDerivAt_vectorProfileCellLegendreField_profile_curve s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv,
    hY0] at hCalc
  have hy : vectorProfileCellLegendreField s₀ s₁ β t i (a,m)=x:=hY0
  rw [hy] at hCalc
  simp only [map_neg,←sub_eq_add_neg] at hCalc
  change -vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x)=
    β*(deriv (fun θ=>vectorProfileCellRawTrace s₀ s₁ β t i (a.1,θ,a.2.2) x) a.2.1-
      fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i a) x
        ((Ring.inverse (hessianOperator
          (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
          (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x))) at hCalc
  linarith

end QuantitativePaper
