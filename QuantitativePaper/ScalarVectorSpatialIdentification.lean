module
public import QuantitativePaper.VectorScalarTail
public import QuantitativePaper.ResponseModel

@[expose] public section

/-! Actual one-spin zero-time vector jets are the scalar Parisi jets.
This follows by differentiating the already proved exact potential identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped BigOperators RealInnerProductSpace
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorMeasureGradient_one_zero_time (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (q : Paper.Overlap) (p : Couplings 1×ℝ) (x : Field 1) :
    vectorMeasureGradient μ β 0 q p x 0=parisiGradient β μ (q,x 0) := by
  let e : Field 1:=EuclideanSpace.single 0 1
  have hline : HasDerivAt (fun y:ℝ=>x+y • e) e 0 := by
    convert! (hasDerivAt_id (0:ℝ)).smul_const e |>.const_add x using 1 <;> simp
  have hd:=(hasFDerivAt_vectorMeasureTailPotential μ β 0 (by norm_num) q p x).comp_hasDerivAt_of_eq 0 hline (by simp)
  have he : (fun y:ℝ=>vectorMeasureTailPotential μ β 0 q p (x+y • e))=
      (fun y:ℝ=>Real.log 2+parisiPotential β μ (q,x 0+y)) := by
    funext y
    rw [vectorMeasureTailPotential_zero_time μ β hβ q q.property]
    simp [e,Fin.sum_univ_one,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply]
  have hshift : HasDerivAt (fun y:ℝ=>x 0+y) 1 0:=by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add (x 0)
  have hs:=((hasDerivAt_parisiPotential_spatial_all β μ q (x 0) q.property).comp_of_eq 0
    hshift (by simp)).const_add (Real.log 2)
  have hd' : HasDerivAt (fun y:ℝ=>Real.log 2+parisiPotential β μ (q,x 0+y))
      (vectorMeasureGradient μ β 0 q p x 0) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero,he,
      InnerProductSpace.toDual_apply_apply,e,EuclideanSpace.inner_single_right,
      one_mul,starRingEnd_apply,star_trivial] using hd
  have hs' : HasDerivAt (fun y:ℝ=>Real.log 2+parisiPotential β μ (q,x 0+y))
      (parisiGradient β μ (q,x 0)) 0 := by
    simpa only [Function.comp_def,id_eq,add_zero,mul_one] using hs
  exact hd'.unique hs'

theorem vectorMeasureHessian_one_zero_time (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (q : Paper.Overlap) (p : Couplings 1×ℝ) (x : Field 1) :
    (vectorMeasureHessian μ β 0 q p x (EuclideanSpace.single 0 1)) 0=
      parisiHessian β μ (q,x 0) := by
  let e : Field 1:=EuclideanSpace.single 0 1
  have hline : HasDerivAt (fun y:ℝ=>x+y • e) e 0 := by
    convert! (hasDerivAt_id (0:ℝ)).smul_const e |>.const_add x using 1 <;> simp
  have hd:=(hasFDerivAt_vectorMeasureGradient μ β 0 (by norm_num) q p x).comp_hasDerivAt_of_eq 0 hline (by simp)
  have hc:=(EuclideanSpace.proj (0:Fin 1)).hasFDerivAt.comp_hasDerivAt 0 hd
  have he : (fun y:ℝ=>vectorMeasureGradient μ β 0 q p (x+y • e) 0)=
      (fun y:ℝ=>parisiGradient β μ (q,x 0+y)) := by
    funext y
    rw [vectorMeasureGradient_one_zero_time μ β hβ]
    simp [e,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply]
  have hshift : HasDerivAt (fun y:ℝ=>x 0+y) 1 0:=by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add (x 0)
  have hs:=(hasDerivAt_parisiGradient_spatial_all β μ q (x 0)).comp_of_eq 0
    hshift (by simp)
  have hc' : HasDerivAt (fun y:ℝ=>parisiGradient β μ (q,x 0+y))
      ((vectorMeasureHessian μ β 0 q p x e) 0) 0 := by
    simpa only [Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply,
      zero_smul,add_zero,he] using hc
  have hs' : HasDerivAt (fun y:ℝ=>parisiGradient β μ (q,x 0+y))
      (parisiHessian β μ (q,x 0)) 0 := by
    simpa only [Function.comp_def,id_eq,add_zero,mul_one] using hs
  exact hc'.unique hs'

end QuantitativePaper
