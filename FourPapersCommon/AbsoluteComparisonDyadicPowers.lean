module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! Genuine infinite dyadic power sums. The mixed sum changes from a
positive power to a negative power at the actual unit scale. -/
noncomputable section
open Set
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def absoluteComparisonDyadicScale (lam : ℝ) (j : ℕ) : ℝ := (2:ℝ)^j*lam

def absoluteComparisonDyadicBudget (lam : ℝ) (j : ℕ) : ℝ :=
  if absoluteComparisonDyadicScale lam j≤1
  then (absoluteComparisonDyadicScale lam j)^(1/6:ℝ)
  else (absoluteComparisonDyadicScale lam j)^(-(1/3:ℝ))

def absoluteComparisonDyadicConstant : ℝ :=
  1/(1-(2:ℝ)^(-(1/6:ℝ)))+1/(1-(2:ℝ)^(-(1/3:ℝ)))

theorem absoluteComparisonDyadicScale_rpow (lam a : ℝ) (hlam : 0<lam) (j : ℕ) :
    (absoluteComparisonDyadicScale lam j)^a=lam^a*((2:ℝ)^a)^j := by
  unfold absoluteComparisonDyadicScale
  rw [Real.mul_rpow (by positivity) hlam.le]
  have hp : ((2:ℝ)^j)^a=((2:ℝ)^a)^j := by
    rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
      mul_comm (j:ℝ) a,Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [hp,mul_comm]

theorem absoluteComparisonDyadic_negative_sum (lam b : ℝ) (hlam : 0<lam)
    (hb : 0<b) :
    Summable (fun j : ℕ=>(absoluteComparisonDyadicScale lam j)^(-b)) ∧
      (∑'j : ℕ,(absoluteComparisonDyadicScale lam j)^(-b))=
        lam^(-b)/(1-(2:ℝ)^(-b)) := by
  have hr : |(2:ℝ)^(-b)|<1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hb)
  have hs : Summable (fun j : ℕ=>lam^(-b)*((2:ℝ)^(-b))^j):=
    (summable_geometric_of_abs_lt_one hr).mul_left _
  simp_rw [absoluteComparisonDyadicScale_rpow lam (-b) hlam]
  refine ⟨hs,?_⟩
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one hr,div_eq_mul_inv]

theorem absoluteComparisonDyadic_half_sum (lam : ℝ) (hlam : 0<lam) :
    Summable (fun j : ℕ=>(absoluteComparisonDyadicScale lam j)^(-(1/2:ℝ))) ∧
      (∑'j : ℕ,(absoluteComparisonDyadicScale lam j)^(-(1/2:ℝ)))=
        lam^(-(1/2:ℝ))/(1-(2:ℝ)^(-(1/2:ℝ))) :=
  absoluteComparisonDyadic_negative_sum lam (1/2) hlam (by norm_num)

theorem absoluteComparisonDyadic_third_sum (lam : ℝ) (hlam : 0<lam) :
    Summable (fun j : ℕ=>(absoluteComparisonDyadicScale lam j)^(-(1/3:ℝ))) ∧
      (∑'j : ℕ,(absoluteComparisonDyadicScale lam j)^(-(1/3:ℝ)))=
        lam^(-(1/3:ℝ))/(1-(2:ℝ)^(-(1/3:ℝ))) :=
  absoluteComparisonDyadic_negative_sum lam (1/3) hlam (by norm_num)

theorem absoluteComparisonDyadic_mixed_sum (lam : ℝ) (hlam : lam∈Ioc (0:ℝ) 1) :
    Summable (absoluteComparisonDyadicBudget lam) ∧
      (∑'j : ℕ,absoluteComparisonDyadicBudget lam j)≤absoluteComparisonDyadicConstant := by
  let ra:=(2:ℝ)^(-(1/6:ℝ))
  let rb:=(2:ℝ)^(-(1/3:ℝ))
  have ha : |ra|<1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hb : |rb|<1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hga : Summable (fun j : ℕ=>ra^j):=summable_geometric_of_abs_lt_one ha
  have hgb : Summable (fun j : ℕ=>rb^j):=summable_geometric_of_abs_lt_one hb
  obtain ⟨N,hN,hNnext⟩:=exists_nat_pow_near (one_le_one_div hlam.1 hlam.2)
    (by norm_num : (1:ℝ)<2)
  have hNU : absoluteComparisonDyadicScale lam N≤1 := by
    exact (le_div_iff₀ hlam.1).mp hN
  have hNext : 1<absoluteComparisonDyadicScale lam (N+1) := by
    exact (div_lt_iff₀ hlam.1).mp hNnext
  have hscale (j : ℕ) : 0<absoluteComparisonDyadicScale lam j := by
    unfold absoluteComparisonDyadicScale
    exact mul_pos (by positivity) hlam.1
  have hnonneg (j : ℕ) : 0≤absoluteComparisonDyadicBudget lam j := by
    unfold absoluteComparisonDyadicBudget
    split <;> exact Real.rpow_nonneg ((hscale _).le) _
  have hlow (j : ℕ) (hj : j≤N) : absoluteComparisonDyadicBudget lam j≤ra^(N-j) := by
    have hprod : absoluteComparisonDyadicScale lam j*(2:ℝ)^(N-j)=
        absoluteComparisonDyadicScale lam N := by
      unfold absoluteComparisonDyadicScale
      rw [mul_assoc,mul_comm lam,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
    have hU : absoluteComparisonDyadicScale lam j≤1 := by
      have hpow : 1≤(2:ℝ)^(N-j):=one_le_pow₀ (by norm_num)
      have hup : absoluteComparisonDyadicScale lam j≤
          absoluteComparisonDyadicScale lam j*(2:ℝ)^(N-j):=by
        nlinarith [show 0≤absoluteComparisonDyadicScale lam j from (hscale _).le]
      exact hup.trans (hprod ▸ hNU)
    have hratio : absoluteComparisonDyadicScale lam j≤1/(2:ℝ)^(N-j) := by
      apply (le_div_iff₀ (by positivity)).mpr
      rw [hprod]
      exact hNU
    rw [absoluteComparisonDyadicBudget,if_pos hU]
    apply (Real.rpow_le_rpow ((hscale _).le) hratio (by norm_num)).trans_eq
    rw [one_div,Real.inv_rpow (by positivity)]
    change (((2:ℝ)^(N-j))^(1/6:ℝ))⁻¹=ra^(N-j)
    rw [←Real.rpow_neg (by positivity),←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
      mul_comm ((N-j:ℕ):ℝ) (-(1/6:ℝ)),Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  have hhigh (j : ℕ) : absoluteComparisonDyadicBudget lam (j+(N+1))≤rb^j := by
    have hprod : absoluteComparisonDyadicScale lam (j+(N+1))=
        (2:ℝ)^j*absoluteComparisonDyadicScale lam (N+1) := by
      simp only [absoluteComparisonDyadicScale,pow_add,mul_assoc]
    have hbase : (2:ℝ)^j≤absoluteComparisonDyadicScale lam (j+(N+1)) := by
      rw [hprod]
      nlinarith [show 0≤(2:ℝ)^j by positivity]
    have hU : 1<absoluteComparisonDyadicScale lam (j+(N+1)) := by
      rw [hprod]
      have hp : 1≤(2:ℝ)^j:=one_le_pow₀ (by norm_num)
      nlinarith
    rw [absoluteComparisonDyadicBudget,if_neg (not_le_of_gt hU)]
    apply (Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)).trans_eq
    rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
      mul_comm (j:ℝ) (-(1/3:ℝ)),Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  have htail : Summable (fun j : ℕ=>absoluteComparisonDyadicBudget lam (j+(N+1))):=
    hgb.of_nonneg_of_le (fun j=>hnonneg _) hhigh
  have hs : Summable (absoluteComparisonDyadicBudget lam):=(summable_nat_add_iff (N+1)).mp htail
  refine ⟨hs,?_⟩
  have hlowSum : (∑j∈Finset.range (N+1),absoluteComparisonDyadicBudget lam j)≤1/(1-ra) := by
    calc
      _≤∑j∈Finset.range (N+1),ra^(N-j):=Finset.sum_le_sum (fun j hj=>hlow j (by simpa using Finset.mem_range.mp hj))
      _=∑j∈Finset.range (N+1),ra^j := by simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun j=>ra^j) (N+1)
      _≤∑'j : ℕ,ra^j:=hga.sum_le_tsum _ (fun j _=>by positivity [ra])
      _=1/(1-ra):=by simpa only [one_div] using tsum_geometric_of_abs_lt_one ha
  have htailSum : (∑'j : ℕ,absoluteComparisonDyadicBudget lam (j+(N+1)))≤1/(1-rb):=
    (htail.tsum_le_tsum hhigh hgb).trans_eq (by simpa only [one_div] using tsum_geometric_of_abs_lt_one hb)
  rw [←hs.sum_add_tsum_nat_add (N+1)]
  exact add_le_add hlowSum htailSum

theorem absoluteComparisonDyadicConstant_pos : 0<absoluteComparisonDyadicConstant := by
  have ha : (2:ℝ)^(-(1/6:ℝ))<1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hb : (2:ℝ)^(-(1/3:ℝ))<1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold absoluteComparisonDyadicConstant
  exact add_pos (one_div_pos.mpr (sub_pos.mpr ha)) (one_div_pos.mpr (sub_pos.mpr hb))

end FourPapersCommon
