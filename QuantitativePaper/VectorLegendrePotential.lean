module
public import QuantitativePaper.VectorLegendreCoordinates
public import QuantitativePaper.VectorClampedScheme

@[expose] public section

/-! The literal Legendre value and its genuine first and second field
derivatives for the finite vector Cole--Hopf potential. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem isOpen_vectorOpenSpinCube (n : ℕ) : IsOpen (vectorOpenSpinCube n):=by
  have he:vectorOpenSpinCube n=⋂i : Fin n,{m : Field n | |m i| < 1}:=by
    ext m
    simp [vectorOpenSpinCube]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Iio.preimage ((EuclideanSpace.proj i).continuous.abs)

def vectorLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) : ℝ:=
  inner ℝ m (vectorLegendreField s β t p j m)-
    vectorRecursion s β t p j (vectorLegendreField s β t p j m)

theorem contDiffAt_vectorLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorLegendrePotential s β t p j) m:=by
  have hY:=contDiffAt_vectorLegendreField s β t p j m hm
  exact (contDiffAt_id.inner ℝ hY).sub
    ((contDiff_vectorRecursion_field s β t p j).contDiffAt.comp m hY)

theorem hasFDerivAt_vectorLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    HasFDerivAt (vectorLegendrePotential s β t p j)
      (innerSL ℝ (vectorLegendreField s β t p j m)) m:=by
  let Y:=vectorLegendreField s β t p j
  have hY:=hasFDerivAt_vectorLegendreField s β t p j m hm
  have hF:=((contDiff_vectorRecursion_field s β t p j).differentiable (by simp) (Y m)).hasFDerivAt
  have hd:=((hasFDerivAt_id m).inner ℝ hY).sub (hF.comp m hY)
  convert hd using 1
  · funext y
    rfl
  · ext w
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
      fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,id_eq]
    rw [real_inner_comm w (Y m),←inner_gradient_left,
      ←vectorMagnetization_eq_gradient,vectorMagnetization_legendreField s β t p j m hm]
    ring

theorem gradient_vectorLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    gradient (vectorLegendrePotential s β t p j) m=vectorLegendreField s β t p j m:=by
  have hg:HasGradientAt (vectorLegendrePotential s β t p j)
      (vectorLegendreField s β t p j m) m:=by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hasFDerivAt_vectorLegendrePotential s β t p j m hm
  exact hg.gradient

theorem hessian_vectorLegendrePotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    hessianOperator (vectorLegendrePotential s β t p j) m=
      ((vectorFieldHessianEquiv s β t p j (vectorLegendreField s β t p j m)).symm :
        Field n→L[ℝ]Field n):=by
  have hφ:ContDiffAt ℝ 2 (vectorLegendrePotential s β t p j) m:=
    (contDiffAt_vectorLegendrePotential s β t p j m hm).of_le (by simp)
  have hf:=((InnerProductSpace.toDual ℝ (Field n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp
    m ((hφ.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt
  have hd:HasFDerivAt (gradient (vectorLegendrePotential s β t p j))
      (hessianOperator (vectorLegendrePotential s β t p j) m) m:=hf
  have he:gradient (vectorLegendrePotential s β t p j)=ᶠ[𝓝 m]vectorLegendreField s β t p j:=by
    filter_upwards [(isOpen_vectorOpenSpinCube n).mem_nhds hm] with y hy
    exact gradient_vectorLegendrePotential s β t p j y hy
  exact hd.unique ((hasFDerivAt_vectorLegendreField s β t p j m hm).congr_of_eventuallyEq he)

theorem vectorTailRecursion_fieldHessian_isUnit {n k : ℕ} (s : RSBScheme k) (β t q : ℝ)
    (hq:q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    IsUnit (hessianOperator (vectorTailRecursion s β t q p (k+2)) x):=by
  rw [vectorTailRecursion_eq_clamped s β t q hq p (by omega : k+2 ≤ k+2)]
  exact vectorFieldHessian_isUnit (vectorClampedScheme s q hq) β t p (k+2) x

end QuantitativePaper
