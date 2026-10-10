module
public import QuantitativePaper.VectorProfileCellLegendrePotential
public import QuantitativePaper.VectorProfileHessianVariations

@[expose] public section

/-! The literal physical Legendre time PDE on actual finite profile cells. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellEnergyHessian (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Field n→L[ℝ]Field n:=
  hessianOperator (fun y=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i (a,y)) m

def vectorProfileCellPhysicalHessian (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Field n→L[ℝ]Field n:=
  Ring.inverse (vectorProfileCellEnergyHessian s₀ s₁ β t i a m)

def vectorOperatorTrace (H : Field n→L[ℝ]Field n) : ℝ:=
  ∑ l : Fin n,(H (EuclideanSpace.single l 1)) l

theorem vectorProfileCellPhysicalHessian_eq (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (i : ℕ) (a : VectorProfileCellParameter n)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellPhysicalHessian s₀ s₁ β t i a m=
      β • vectorFieldHessian
        (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1) β t a.2.2 (k+2)
        (vectorProfileCellLegendreField s₀ s₁ β t i (a,m)) :=
  vectorProfilePhysicalHessian_eq s₀ s₁ β t hβ (vectorProfileCellOverlap a.1) (k+2)
    a.2.1 a.2.2 m hm

theorem hasDerivAt_vectorProfileCellEnergyLegendrePotential_time_raw
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun r=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((r,a.2),m))
      (((1-t)*β^2)/(2*β)*
        (vectorLaplacian (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y))
          (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))+
          vectorProfileMass s₀ s₁ a.2.1 i*‖m‖^2)) a.1 := by
  let U:=vectorProfileCellJointPotential (n:=n) s₀ s₁ β t i
  let Y:=vectorProfileCellLegendreField s₀ s₁ β t i (a,m)
  have hU:=contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,Y) hq.2 hθ
  have hline : HasDerivAt (fun r : ℝ=>(r,a.2)) (1,0) a.1:=by
    convert (hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2) using 1 <;> rfl
  have hUline : HasDerivAt (fun r : ℝ=>((r,a.2),Y)) ((1,0),0) a.1:=
    hline.prodMk (hasDerivAt_const a.1 Y)
  have hDU:=((hU.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt a.1 hUline
  have hPDE:=hasDerivAt_vectorProfilePhysicalCell_PDE s₀ s₁ β t hβ ht i a.1 a.2.1
    ⟨hθ.1.le,hθ.2.le⟩ hq.2 a.2.2 Y
  have hgrad : gradient (fun y=>U (a,y)) Y=m:=by
    change vectorProfileCellJointGradient s₀ s₁ β t i (a,Y)=m
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorMagnetization_legendreField
      (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
      β t a.2.2 (k+2) m hm
  have hUq : (fderiv ℝ U (a,Y)) ((1,0),0)=
      (-((1-t)*β^2)/2*(vectorLaplacian (fun y=>U (a,y)) Y+
        vectorProfileMass s₀ s₁ a.2.1 i*‖m‖^2)):=by
    have he:=hDU.unique hPDE
    change _=-((1-t)*β^2)/2*(vectorLaplacian (fun y=>U (a,y)) Y+
      vectorProfileMass s₀ s₁ a.2.1 i*‖gradient (fun y=>U (a,y)) Y‖^2) at he
    rwa [hgrad] at he
  have hEnv:=hasFDerivAt_vectorProfileCellLegendrePotential_parameter s₀ s₁ β t hβ ht i hi
    a hq hθ m hm
  have hPhi:=(hEnv.comp_hasDerivAt a.1 hline).div_const β
  apply hPhi.congr_deriv
  change (-((fderiv ℝ U (a,Y)) ((1,0),0)))/β=_
  rw [hUq]
  ring

theorem hasDerivAt_vectorProfileCellEnergyLegendrePotential_time
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun r=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((r,a.2),m))
      ((1-t)/2*vectorOperatorTrace (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)+
        (1-t)*(β*vectorProfileMass s₀ s₁ a.2.1 i)/2*‖m‖^2) a.1 := by
  have hd:=hasDerivAt_vectorProfileCellEnergyLegendrePotential_time_raw s₀ s₁ β t hβ ht i hi
    a hq hθ m hm
  apply hd.congr_deriv
  let S:=vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1
  let Y:=vectorProfileCellLegendreField s₀ s₁ β t i (a,m)
  have hLap : vectorLaplacian (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) Y=
      vectorOperatorTrace (vectorFieldHessian S β t a.2.2 (k+2) Y):=by
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    unfold vectorLaplacian vectorOperatorTrace
    apply Finset.sum_congr rfl
    intro l _
    change fderiv ℝ (fderiv ℝ (vectorRecursion S β t a.2.2 (k+2))) Y
      (EuclideanSpace.single l 1) (EuclideanSpace.single l 1)=
      (vectorFieldHessian S β t a.2.2 (k+2) Y (EuclideanSpace.single l 1)) l
    rw [vectorFieldHessian,←inner_hessianOperator]
    simp only [EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul]
  rw [hLap,vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i a m hm]
  have htr : vectorOperatorTrace (β • vectorFieldHessian S β t a.2.2 (k+2) Y)=
      β*vectorOperatorTrace (vectorFieldHessian S β t a.2.2 (k+2) Y):=by
    simp only [vectorOperatorTrace,ContinuousLinearMap.smul_apply,PiLp.smul_apply,
      smul_eq_mul,Finset.mul_sum]
  rw [htr]
  field_simp
  <;> ring

end QuantitativePaper
