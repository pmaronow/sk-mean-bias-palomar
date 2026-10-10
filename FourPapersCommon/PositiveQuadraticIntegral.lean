module
public import FourPapersCommon.PositiveQuadraticBounds
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-! Jensen and the two-term splitting inequality for an actual finite
positive-semidefinite matrix quadratic form. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators MatrixOrder
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem positive_matrix_quadratic_integral_le {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (v : Ω→EuclideanSpace ℝ I)
    (hv : Integrable v P)
    (hquad : Integrable (fun ω=>∑i : I,∑j : I,C i j*v ω i*v ω j) P) :
    (∑i : I,∑j : I,C i j*(∫ω,v ω ∂P) i*(∫ω,v ω ∂P) j)≤
      ∫ω,(∑i : I,∑j : I,C i j*v ω i*v ω j) ∂P := by
  let L:EuclideanSpace ℝ I→ₗ[ℝ]EuclideanSpace ℝ I:=(CFC.sqrt C).toEuclideanLin
  have hcv : ConvexOn ℝ univ (fun z : EuclideanSpace ℝ I=>‖L z‖^2) := by
    simpa only [preimage_univ,Function.comp_def,Pi.pow_apply] using
      ((convexOn_univ_norm (E:=EuclideanSpace ℝ I)).pow (fun _ _=>norm_nonneg _) 2).comp_linearMap L
  have hcont : Continuous (fun z : EuclideanSpace ℝ I=>‖L z‖^2) :=
    (L.continuous_of_finiteDimensional.norm).pow 2
  have hi : Integrable (fun ω=>‖L (v ω)‖^2) P := by
    simpa only [positive_matrix_quadratic_eq_sqrt_norm_sq C hC] using hquad
  have h:=hcv.map_integral_le hcont.continuousOn isClosed_univ (.of_forall fun _=>mem_univ _) hv hi
  simpa only [positive_matrix_quadratic_eq_sqrt_norm_sq C hC] using h

theorem positive_matrix_quadratic_add_le {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (v w : EuclideanSpace ℝ I) :
    (∑i : I,∑j : I,C i j*(v+w) i*(v+w) j)≤
      2*(∑i : I,∑j : I,C i j*v i*v j)+2*(∑i : I,∑j : I,C i j*w i*w j) := by
  have h:=positive_matrix_quadratic_sum_le C hC ![v,w]
  simpa [Fin.sum_univ_two,mul_add] using h

theorem positive_matrix_quadratic_mean_split {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (m : EuclideanSpace ℝ I)
    (v : Ω→EuclideanSpace ℝ I) (hv : Integrable v P)
    (hres : Integrable (fun ω=>∑i : I,∑j : I,C i j*(m-v ω) i*(m-v ω) j) P) :
    (∑i : I,∑j : I,C i j*m i*m j)≤
      2*(∑i : I,∑j : I,C i j*(∫ω,v ω ∂P) i*(∫ω,v ω ∂P) j)+
        2*∫ω,(∑i : I,∑j : I,C i j*(m-v ω) i*(m-v ω) j) ∂P := by
  have hi : Integrable (fun ω=>m-v ω) P:=(integrable_const m).sub hv
  have he : (∫ω,m-v ω ∂P)=m-∫ω,v ω ∂P := by
    rw [integral_sub (integrable_const m) hv]
    simp only [integral_const,probReal_univ,one_smul]
  have hJ:=positive_matrix_quadratic_integral_le P C hC (fun ω=>m-v ω) hi hres
  rw [he] at hJ
  have hs:=positive_matrix_quadratic_add_le C hC (∫ω,v ω ∂P) (m-∫ω,v ω ∂P)
  rw [add_sub_cancel] at hs
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ (by norm_num)))

end FourPapersCommon
