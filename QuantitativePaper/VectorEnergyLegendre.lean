module
public import QuantitativePaper.VectorLegendreDuality
public import FourPapersCommon.LocalGradientCalculus

@[expose] public section

/-! Exact energy scaling of the genuine finite Legendre transform.
In the paper's variables the field is x/β and the physical Hessian is βH. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

def vectorEnergyLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) : ℝ:=
  vectorLegendrePotential s β t p j m/β

theorem contDiffAt_vectorEnergyLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorEnergyLegendrePotential s β t p j) m:=
  (contDiffAt_vectorLegendrePotential s β t p j m hm).div_const β

theorem gradient_vectorEnergyLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    gradient (vectorEnergyLegendrePotential s β t p j) m=
      β⁻¹ • vectorLegendreField s β t p j m:=by
  have hd:HasFDerivAt (vectorEnergyLegendrePotential s β t p j)
      (β⁻¹ • innerSL ℝ (vectorLegendreField s β t p j m)) m:=by
    convert (hasFDerivAt_vectorLegendrePotential s β t p j m hm).const_smul β⁻¹ using 1
    funext y
    simp only [vectorEnergyLegendrePotential,div_eq_mul_inv,mul_comm,Pi.smul_apply,smul_eq_mul]
  have hg:HasGradientAt (vectorEnergyLegendrePotential s β t p j)
      (β⁻¹ • vectorLegendreField s β t p j m) m:=by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hd using 1
    ext w
    simp [real_inner_smul_left]
  exact hg.gradient

theorem hessian_vectorEnergyLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    hessianOperator (vectorEnergyLegendrePotential s β t p j) m=
      β⁻¹ • ((vectorFieldHessianEquiv s β t p j (vectorLegendreField s β t p j m)).symm :
        Field n→L[ℝ]Field n):=by
  have hd:=hasFDerivAt_gradient_of_contDiffAt (vectorEnergyLegendrePotential s β t p j) m
    ((contDiffAt_vectorEnergyLegendrePotential s β t p j m hm).of_le (by simp))
  have hY:= (hasFDerivAt_vectorLegendreField s β t p j m hm).const_smul β⁻¹
  have he:gradient (vectorEnergyLegendrePotential s β t p j)=ᶠ[𝓝 m]
      (fun y=>β⁻¹ • vectorLegendreField s β t p j y):=by
    filter_upwards [(isOpen_vectorOpenSpinCube n).mem_nhds hm] with y hy
    exact gradient_vectorEnergyLegendrePotential s β t p j y hy
  exact hd.unique (hY.congr_of_eventuallyEq he)

theorem inverse_hessian_vectorEnergyLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ:β ≠ 0) (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    Ring.inverse (hessianOperator (vectorEnergyLegendrePotential s β t p j) m)=
      β • vectorFieldHessian s β t p j (vectorLegendreField s β t p j m):=by
  let e:=vectorFieldHessianEquiv s β t p j (vectorLegendreField s β t p j m)
  let u:(Field n→L[ℝ]Field n)ˣ:={
    val:=β⁻¹ • (e.symm : Field n→L[ℝ]Field n)
    inv:=β • (e : Field n→L[ℝ]Field n)
    val_inv:=by
      ext w
      simp [ContinuousLinearMap.mul_apply,map_smul,smul_smul,hβ]
    inv_val:=by
      ext w
      simp [ContinuousLinearMap.mul_apply,map_smul,smul_smul,hβ] }
  rw [hessian_vectorEnergyLegendrePotential s β t p j m hm]
  change Ring.inverse (u : Field n→L[ℝ]Field n)=_
  rw [Ring.inverse_unit]
  change β • (e : Field n→L[ℝ]Field n)=_
  rw [show (e : Field n→L[ℝ]Field n)=vectorFieldHessian s β t p j (vectorLegendreField s β t p j m) from
    vectorFieldHessianEquiv_coe s β t p j (vectorLegendreField s β t p j m)]

end QuantitativePaper
