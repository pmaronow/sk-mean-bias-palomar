module
public import QuantitativePaper.VectorProfileCurvaturePairingPDE
public import FourPapersCommon.StationarySecondVariation

@[expose] public section

/-! The literal second Legendre variation in original field coordinates.
No growth estimate is inferred from smoothness alone. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellPotentialFirstVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (x : Field n) : ℝ:=
  deriv (fun θ=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),x)) a.2.1

def vectorProfileCellPotentialSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (x : Field n) : ℝ:=
  deriv (deriv (fun θ=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),x))) a.2.1

theorem vectorProfileCellSecondVariation_field_formula (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellSecondVariation s₀ s₁ β t i a m=
      β⁻¹*(-vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a
          (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))+
        inner ℝ (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a)
          (vectorProfileCellLegendreField s₀ s₁ β t i (a,m)))
          ((Ring.inverse (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x))
              (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a)
              (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))) := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1,a.2.2),z.2)
  let Y : ℝ→Field n:=fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m)
  let Φ : ℝ→ℝ:=fun θ=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((a.1,θ,a.2.2),m)
  have hU : ContDiffAt ℝ ∞ U (a.2.1,Y a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.2.1,Y a.2.1)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,Y a.2.1) hq.2 hθ)
    (by fun_prop)
  have hY : ContDiffAt ℝ ∞ Y a.2.1:=ContDiffAt.comp
    (f := fun θ : ℝ=>((a.1,θ,a.2.2),m))
    (g := vectorProfileCellLegendreField s₀ s₁ β t i) a.2.1
    (contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hStationary : (fun θ=>gradient (fun x=>U (θ,x)) (Y θ))=ᶠ[𝓝 a.2.1](fun _=>m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    change vectorProfileCellJointGradient s₀ s₁ β t i ((a.1,θ,a.2.2),Y θ)=m
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi (a.1,θ,a.2.2)
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ'.1.le,hθ'.2.le⟩]
    exact vectorMagnetization_legendreField _ β t a.2.2 (k+2) m hm
  have hUnit : IsUnit (hessianOperator (fun x=>U (a.2.1,x)) (Y a.2.1)):=by
    change IsUnit (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x)) (Y a.2.1))
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorFieldHessian_isUnit _ β t a.2.2 (k+2) _
  have hFirst : ∀ᶠ θ in 𝓝 a.2.1,HasDerivAt Φ (-β⁻¹*deriv (fun α=>U (α,Y θ)) θ) θ:=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    have hLine : HasDerivAt (fun α : ℝ=>(a.1,α,a.2.2)) (0,(1,0)) θ:=
      (hasDerivAt_const θ a.1).prodMk ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ a.2.2))
    have hEnv:=(hasFDerivAt_vectorProfileCellLegendrePotential_parameter s₀ s₁ β t hβ ht i hi
      (a.1,θ,a.2.2) hq hθ' m hm).comp_hasDerivAt θ hLine |>.div_const β
    have hJoint:=contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi
      ((a.1,θ,a.2.2),Y θ) hq.2 hθ'
    have hRaw:=((hJoint.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt θ
      (hLine.prodMk (hasDerivAt_const θ (Y θ)))
    apply hEnv.congr_deriv
    change -(fderiv ℝ (vectorProfileCellJointPotential s₀ s₁ β t i)
      ((a.1,θ,a.2.2),Y θ) ((0,(1,0)),0))/β= -β⁻¹*deriv (fun α=>U (α,Y θ)) θ
    have he : deriv (fun α=>U (α,Y θ)) θ=
        (fderiv ℝ (vectorProfileCellJointPotential s₀ s₁ β t i)
          ((a.1,θ,a.2.2),Y θ)) ((0,(1,0)),0):=hRaw.deriv
    rw [he]
    ring
  exact stationary_second_variation U Y Φ a.2.1 β⁻¹ m hU
    (hY.differentiableAt (by simp)) hStationary hUnit hFirst

theorem vectorProfileCellLegendreField_gradient (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellLegendreField s₀ s₁ β t i
      (a,vectorProfileCellJointGradient s₀ s₁ β t i (a,x))=x := by
  rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a hq hθ]
  exact vectorLegendreField_magnetization _ β t a.2.2 (k+2) x

theorem vectorProfileCellSecondVariation_pullback (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellSecondVariation s₀ s₁ β t i a
      (vectorProfileCellJointGradient s₀ s₁ β t i (a,x))=
      β⁻¹*(-vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a x+
        inner ℝ (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x)
          ((Ring.inverse (hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x))) := by
  have hm : vectorProfileCellJointGradient s₀ s₁ β t i (a,x)∈vectorOpenSpinCube n:=by
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    exact fun l=>vectorMagnetization_component_abs_lt_one _ β t a.2.2 (k+2) x l
  rw [vectorProfileCellSecondVariation_field_formula s₀ s₁ β t hβ ht i hi a hq hθ _ hm,
    vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x]

end QuantitativePaper
