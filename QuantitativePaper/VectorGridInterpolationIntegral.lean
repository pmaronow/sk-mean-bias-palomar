module
public import QuantitativePaper.VectorInterpolationLipschitz
public import QuantitativePaper.VectorInterpolationTimeDefect

@[expose] public section

/-! The genuine finite interpolation identity on arbitrary closed physical
subintervals follows from the proved derivative and Lipschitz FTC. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1600000

theorem vectorMeasureFunctional_grid_interpolation_integral
    (hn : 0<n) (μ : Paper.ParisiMeasure) (j : ℕ) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0)
    (r u : ℝ) (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) (hru : r≤u) :
    IntervalIntegrable (vectorInterpolationTimeDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β) volume r u ∧
    vectorMeasureFunctional n (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β u s-
      vectorMeasureFunctional n (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β r s=
      -β^2/4*(∫t in r..u,vectorInterpolationTimeDefect (n:=n)
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t) := by
  let F:=fun t=>vectorMeasureFunctional n
    (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s
  let D:=vectorInterpolationTimeDefect (n:=n)
    (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β
  let c:ℝ := -β^2/4
  have hc:c≠0:=div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hβ)) (by norm_num)
  have hl : LipschitzOnWith (vectorInterpolationLipschitzConstant β s hs.2.le) F (uIcc r u) := by
    rw [uIcc_of_le hru]
    exact (vectorMeasureFunctional_grid_interpolation_lipschitz hn μ j β s hs hμ hβ).mono
      (Icc_subset_Icc hr.1 hu.2)
  obtain ⟨hi,_,he⟩:=lipschitz_envelope_endpoint_integral F r u _ hl
  have hEq : EqOn (deriv F) (fun t=>c*D t) (uIoo r u) := by
    rw [uIoo_of_le hru]
    intro t ht
    have ht01 : t∈Ioo (0:ℝ) 1:=⟨hr.1.trans_lt ht.1,ht.2.trans_le hu.2⟩
    have hd:=hasDerivAt_vectorMeasureFunctional_grid_interpolation hn μ j β s hs.1 hμ hβ t ht01
    simpa only [F,D,c,vectorInterpolationTimeDefect_of_lt _ _ _ _ ht01.2] using hd.deriv
  have hD : IntervalIntegrable D volume r u := by
    apply (hi.div_const c).congr_uIoo
    intro t ht
    change deriv F t/c=D t
    rw [hEq ht]
    exact mul_div_cancel_left₀ (D t) hc
  refine ⟨hD,?_⟩
  have hI:=intervalIntegral.integral_congr_uIoo (μ:=volume) hEq
  rw [intervalIntegral.integral_const_mul] at hI
  exact he.symm.trans hI

end QuantitativePaper
