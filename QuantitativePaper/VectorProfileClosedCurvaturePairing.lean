module
public import QuantitativePaper.VectorProfileClosedLegendreVariations
public import QuantitativePaper.VectorProfileClosedReaction

@[expose] public section

/-! Genuine curvature pairing identification at closed cell endpoints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem contDiffAt_vectorProfileCell_fixed_time_trace
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun w : VectorProfileParameter n×Field n=>
      vectorProfileCellRawTrace s₀ s₁ β t i (q,w.1) w.2) z := by
  have hf:=retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n)
    s₀ s₁ β t ht i hi (z.1.1/2) ((z.1.1+1)/2) (by linarith [hθ.1]) (by linarith [hθ.2])
  exact hf.smooth q hq z ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem hasDerivAt_vectorProfileCellLegendreField_profile_curve_closed
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m))
      (-((Ring.inverse (hessianOperator
        (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x))
        (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))
        (gradient (fun x=>deriv (fun θ=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),x)) a.2.1)
          (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))) a.2.1 := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1,a.2.2),z.2)
  let Y : ℝ→Field n:=fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m)
  have hU : ContDiffAt ℝ ∞ U (a.2.1,Y a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2.2),z.2))
    (g := fun z : VectorProfileParameter n×Field n=>
      vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1),z.2)) (a.2.1,Y a.2.1)
    (contDiffAt_vectorProfileCell_fixed_time_potential s₀ s₁ β t ht i hi a.1 hq
      ((a.2.1,a.2.2),Y a.2.1) hθ) (by fun_prop)
  have hY : ContDiffAt ℝ ∞ Y a.2.1:=
    contDiffAt_vectorProfileCell_fixed_time_inverse_curve s₀ s₁ β t ht i a.1 a.2.1 hθ a.2.2 m hm
  have hStationary : (fun θ=>gradient (fun x=>U (θ,x)) (Y θ))=ᶠ[𝓝 a.2.1](fun _=>m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    change vectorProfileCellJointGradient s₀ s₁ β t i ((a.1,θ,a.2.2),Y θ)=m
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi (a.1,θ,a.2.2)
      hq ⟨hθ'.1.le,hθ'.2.le⟩]
    exact vectorMagnetization_legendreField _ β t a.2.2 (k+2) m hm
  have hUnit : IsUnit (hessianOperator (fun x=>U (a.2.1,x)) (Y a.2.1)):=by
    change IsUnit (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x)) (Y a.2.1))
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a
      hq ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorFieldHessian_isUnit _ β t a.2.2 (k+2) _
  exact hasDerivAt_stationary_inverse_curve U Y a.2.1 m hU
    (hY.differentiableAt (by simp)) hStationary hUnit


theorem vectorProfileCellCurvaturePairing_retained_formula_closed
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
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
    hq ⟨hθ.1.le,hθ.2.le⟩ x
  have hY0 : Y a.2.1=x:=vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a
    hq ⟨hθ.1.le,hθ.2.le⟩ x
  have hY : ContDiffAt ℝ ∞ Y a.2.1:=
    contDiffAt_vectorProfileCell_fixed_time_inverse_curve s₀ s₁ β t ht.le i a.1 a.2.1 hθ a.2.2 m hm
  have hW : ContDiffAt ℝ ∞ W (a.2.1,Y a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2.2),z.2))
    (g := fun z : VectorProfileParameter n×Field n=>
      vectorProfileCellRawTrace s₀ s₁ β t i (a.1,z.1) z.2) (a.2.1,Y a.2.1)
    (contDiffAt_vectorProfileCell_fixed_time_trace s₀ s₁ β t ht.le i hi a.1 hq
      ((a.2.1,a.2.2),Y a.2.1) hθ) (by fun_prop)
  have he : (fun θ=>vectorProfileCellTrace s₀ s₁ β t i (a.1,θ,a.2.2) m)=ᶠ[𝓝 a.2.1]
      (fun θ=>β*W (θ,Y θ)):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    unfold vectorProfileCellTrace
    rw [vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i (a.1,θ,a.2.2) m hm]
    have heU : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),y))=
        vectorRecursion (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) θ)
          β t a.2.2 (k+2):=vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi (a.1,θ,a.2.2)
            hq ⟨hθ'.1.le,hθ'.2.le⟩
    dsimp only [W,vectorProfileCellRawTrace,Y]
    rw [heU]
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_smul,Matrix.trace_smul,smul_eq_mul]
    rfl
  have hCalc:=he.deriv_eq
  rw [vectorProfileCellTrace_profile_eq_neg_pairing s₀ s₁ β t hβ ht i a hθ m hm,
    deriv_const_mul_field,
    deriv_time_curve_composition W Y a.2.1 (hW.of_le (by norm_num)) (hY.of_le (by norm_num)),
    (hasDerivAt_vectorProfileCellLegendreField_profile_curve_closed s₀ s₁ β t ht.le i hi a hq hθ m hm).deriv,
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
