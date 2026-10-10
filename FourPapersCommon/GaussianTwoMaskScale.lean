module
public import FourPapersCommon.GaussianSelectedCoordinateScale

@[expose] public section

/-! The actual disjoint root/path Gaussian clocks sqrt(u) and
sqrt(d-alpha*u), retaining unit scale on every other coordinate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianTwoMaskCoefficient (pR pP : ι→Bool) (d alpha u : ℝ) (i : ι) : ℝ:=
  if pR i then Real.sqrt u else if pP i then Real.sqrt (d-alpha*u) else 1
def gaussianTwoMaskCoefficientDerivative (pR pP : ι→Bool) (d alpha u : ℝ) (i : ι) : ℝ:=
  if pR i then 1/(2*Real.sqrt u) else if pP i then -alpha/(2*Real.sqrt (d-alpha*u)) else 0
def gaussianTwoMaskScale (pR pP : ι→Bool) (d alpha u : ℝ) :
    EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι:=
  ∑i,(PiLp.proj 2 (fun _ : ι=>ℝ) i).smulRight
    (gaussianTwoMaskCoefficient pR pP d alpha u i •EuclideanSpace.basisFun ι ℝ i)
def gaussianTwoMaskScaleDerivative (pR pP : ι→Bool) (d alpha u : ℝ) :
    EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι:=
  ∑i,(PiLp.proj 2 (fun _ : ι=>ℝ) i).smulRight
    (gaussianTwoMaskCoefficientDerivative pR pP d alpha u i •EuclideanSpace.basisFun ι ℝ i)

theorem gaussianTwoMaskScale_apply (pR pP : ι→Bool) (d alpha u : ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianTwoMaskScale pR pP d alpha u z=
      ∑i,(gaussianTwoMaskCoefficient pR pP d alpha u i*z i)•EuclideanSpace.basisFun ι ℝ i := by
  simp only [gaussianTwoMaskScale,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul]
  congr 1
  funext i
  rw [mul_comm]

theorem gaussianTwoMaskScaleDerivative_apply (pR pP : ι→Bool) (d alpha u : ℝ)
    (z : EuclideanSpace ℝ ι) :
    gaussianTwoMaskScaleDerivative pR pP d alpha u z=
      ∑i,(gaussianTwoMaskCoefficientDerivative pR pP d alpha u i*z i)•EuclideanSpace.basisFun ι ℝ i := by
  simp only [gaussianTwoMaskScaleDerivative,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul]
  congr 1
  funext i
  rw [mul_comm]

@[simp] theorem gaussianTwoMaskScale_basis (pR pP : ι→Bool) (d alpha u : ℝ) (i : ι) :
    gaussianTwoMaskScale pR pP d alpha u (EuclideanSpace.basisFun ι ℝ i)=
      gaussianTwoMaskCoefficient pR pP d alpha u i•EuclideanSpace.basisFun ι ℝ i := by
  rw [gaussianTwoMaskScale_apply]
  simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp

theorem hasDerivAt_gaussianTwoMaskCoefficient (pR pP : ι→Bool) (d alpha u : ℝ)
    (hu : 0<u) (hb : 0<d-alpha*u) (i : ι) :
    HasDerivAt (fun q=>gaussianTwoMaskCoefficient pR pP d alpha q i)
      (gaussianTwoMaskCoefficientDerivative pR pP d alpha u i) u := by
  by_cases hr:pR i=true
  · simp only [gaussianTwoMaskCoefficient,gaussianTwoMaskCoefficientDerivative,hr,ite_true]
    exact Real.hasDerivAt_sqrt hu.ne'
  · have hr0:pR i=false:=Bool.eq_false_iff.mpr hr
    simp only [gaussianTwoMaskCoefficient,gaussianTwoMaskCoefficientDerivative,hr0,
      Bool.false_eq_true,ite_false]
    by_cases hp:pP i=true
    · simp only [hp,ite_true]
      have hh:=(Real.hasDerivAt_sqrt hb.ne').comp u
        ((hasDerivAt_const u d).sub ((hasDerivAt_id u).const_mul alpha))
      simp only [Function.comp_def,Pi.sub_apply,id_eq,mul_one,zero_sub] at hh
      convert hh using 1 <;> ring
    · have hp0:pP i=false:=Bool.eq_false_iff.mpr hp
      simp only [hp0,Bool.false_eq_true,ite_false]
      exact hasDerivAt_const u 1

theorem hasDerivAt_gaussianTwoMaskScale (pR pP : ι→Bool) (d alpha u : ℝ)
    (hu : 0<u) (hb : 0<d-alpha*u) (z : EuclideanSpace ℝ ι) :
    HasDerivAt (fun q=>gaussianTwoMaskScale pR pP d alpha q z)
      (gaussianTwoMaskScaleDerivative pR pP d alpha u z) u := by
  simp_rw [gaussianTwoMaskScale_apply,gaussianTwoMaskScaleDerivative_apply]
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hasDerivAt_gaussianTwoMaskCoefficient pR pP d alpha u hu hb i).mul_const (z i)).smul_const _

theorem gaussianTwoMaskCoefficient_rate_product (pR pP : ι→Bool) (d alpha u : ℝ)
    (hu : 0<u) (hb : 0<d-alpha*u) (i : ι) :
    gaussianTwoMaskCoefficientDerivative pR pP d alpha u i*
      gaussianTwoMaskCoefficient pR pP d alpha u i=
      if pR i then (1/2:ℝ) else if pP i then -alpha/2 else 0 := by
  unfold gaussianTwoMaskCoefficientDerivative gaussianTwoMaskCoefficient
  cases hr:pR i <;> cases hp:pP i <;> simp only [hr,hp,Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp [(Real.sqrt_pos.mpr hu).ne',(Real.sqrt_pos.mpr hb).ne'] <;> ring

end FourPapersCommon
