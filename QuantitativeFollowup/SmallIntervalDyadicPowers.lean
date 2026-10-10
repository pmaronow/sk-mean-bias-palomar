module
public import FourPapersCommon.AbsoluteComparisonDyadicPowers
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Genuine dyadic mass sums, including the upward positive-power sum
terminated at its last admissible level. -/
noncomputable section
open Set FourPapersCommon
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

def smallIntervalDyadicConstant : ℝ := 2+1/(1-(2:ℝ)^(-(1/3:ℝ)))

theorem smallIntervalDyadicConstant_pos : 0 < smallIntervalDyadicConstant := by
  have hr : (2:ℝ)^(-(1/3:ℝ))<1:=Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold smallIntervalDyadicConstant
  positivity

theorem smallIntervalDyadic_inverse_sum (s : ℝ) (hs : 0<s) (N : ℕ) :
    (∑j∈Finset.range (N+1),1/((2:ℝ)^j*s))  ≤  2/s := by
  have hgeom : Summable (fun j:ℕ=>(1/2:ℝ)^j):=summable_geometric_of_abs_lt_one (by norm_num)
  have hg:=hgeom.sum_le_tsum (Finset.range (N+1)) (fun j _=>by positivity)
  have he : (∑'j:ℕ,(1/2:ℝ)^j)=2:=by rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)];norm_num
  have hscale (j:ℕ) : 1/((2:ℝ)^j*s)=(1/s)*(1/2:ℝ)^j := by
    rw [div_pow]
    field_simp
    simp
  simp_rw [hscale]
  rw [←Finset.mul_sum]
  rw [he] at hg
  convert mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 1/s) using 1 <;> ring

theorem smallIntervalDyadic_negative_third_sum (s : ℝ) (hs : 0<s) (N : ℕ) :
    (∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(-(1/3:ℝ)))  ≤ 
      s^(-(1/3:ℝ))/(1-(2:ℝ)^(-(1/3:ℝ))) := by
  obtain ⟨hSummable,hSum⟩:=absoluteComparisonDyadic_third_sum s hs
  have hh:=hSummable.sum_le_tsum (Finset.range (N+1)) (fun j _=>by
    unfold absoluteComparisonDyadicScale
    positivity)
  rw [hSum] at hh
  simpa only [absoluteComparisonDyadicScale] using hh

theorem smallIntervalDyadic_positive_third_sum (s : ℝ) (hs : 0<s) (N : ℕ)
    (hN : (2:ℝ)^N*s  ≤  1) :
    (∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(1/3:ℝ))  ≤ 
      1/(1-(2:ℝ)^(-(1/3:ℝ))) := by
  let r:=(2:ℝ)^(-(1/3:ℝ))
  have hr : |r|<1:=by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hg : Summable (fun j:ℕ=>r^j):=summable_geometric_of_abs_lt_one hr
  have hlow (j:ℕ) (hj:j ≤ N) : ((2:ℝ)^j*s)^(1/3:ℝ)  ≤  r^(N-j) := by
    have hprod : ((2:ℝ)^j*s)*(2:ℝ)^(N-j)=(2:ℝ)^N*s := by
      rw [mul_assoc,mul_comm s,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
    have hratio : (2:ℝ)^j*s  ≤  1/(2:ℝ)^(N-j) := by
      apply (le_div_iff₀ (by positivity)).mpr
      rw [hprod]
      exact hN
    apply (Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^j*s) hratio (by norm_num)).trans_eq
    rw [one_div,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity),
      ←Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      mul_comm ((N-j:ℕ):ℝ) (-(1/3:ℝ)),Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ ∑j∈Finset.range (N+1),r^(N-j):=Finset.sum_le_sum (fun j hj=>hlow j (by simpa using Finset.mem_range.mp hj))
    _=∑j∈Finset.range (N+1),r^j:=by simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun j=>r^j) (N+1)
    _ ≤ ∑'j:ℕ,r^j:=hg.sum_le_tsum _ (fun j _=>by positivity [r])
    _=_:=by simpa only [r,one_div] using tsum_geometric_of_abs_lt_one hr

end QuantitativeFollowup
