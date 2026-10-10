module
public import FRSB.MStochasticSum

@[expose] public section

/-! Deterministic uniform grids on an arbitrary physical overlap interval,
including coincident endpoints, and their genuine Riemann-sum limit. -/
noncomputable section
open Set Filter StochasticCalculus
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def vectorUniformOverlapGrid (r q : Paper.Overlap) (hrq : r ≤ q) (N : ℕ)
    (i : Fin (N+2)) : Paper.Overlap :=
  ⟨(r : ℝ)+((q : ℝ)-r)*(i : ℝ)/(N+1), by
    have hd : (0:ℝ)<N+1 := by positivity
    have hi : (0:ℝ)≤(i:ℝ) := by positivity
    have hi' : (i:ℝ)≤N+1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hf : (i:ℝ)/(N+1)∈Icc (0:ℝ) 1 :=
      ⟨div_nonneg hi hd.le, (div_le_one hd).mpr hi'⟩
    have hrq' : (r:ℝ)≤q := hrq
    constructor
    · rw [mul_div_assoc]
      nlinarith [mul_nonneg (sub_nonneg.mpr hrq') hf.1, r.property.1]
    · rw [mul_div_assoc]
      nlinarith [mul_le_mul_of_nonneg_left hf.2 (sub_nonneg.mpr hrq'), q.property.2]⟩

@[simp] theorem vectorUniformOverlapGrid_coe (r q : Paper.Overlap) (hrq : r≤q)
    (N : ℕ) (i : Fin (N+2)) :
    (vectorUniformOverlapGrid r q hrq N i : ℝ)=(r:ℝ)+((q:ℝ)-r)*(i:ℝ)/(N+1) := rfl

@[simp] theorem vectorUniformOverlapGrid_zero (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    vectorUniformOverlapGrid r q hrq N 0=r := by ext; simp

@[simp] theorem vectorUniformOverlapGrid_last (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    vectorUniformOverlapGrid r q hrq N (Fin.last (N+1))=q := by
  ext
  simp only [vectorUniformOverlapGrid_coe, Fin.val_last, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel_right₀ _ (by positivity : (N:ℝ)+1≠0)]
  ring

theorem monotone_vectorUniformOverlapGrid (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    Monotone (vectorUniformOverlapGrid r q hrq N) := by
  intro i j hij
  change (r:ℝ)+((q:ℝ)-(r:ℝ))*(i:ℝ)/((N:ℝ)+1)≤(r:ℝ)+((q:ℝ)-(r:ℝ))*(j:ℝ)/((N:ℝ)+1)
  have hij' : (i:ℝ)≤(j:ℝ) := by exact_mod_cast hij
  have hd : (0:ℝ)≤(N:ℝ)+1 := by positivity
  exact add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hij' (sub_nonneg.mpr (show (r:ℝ)≤q from hrq))) hd) _

theorem vectorUniformOverlapGrid_width (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ)
    (i : Fin (N+1)) :
    (vectorUniformOverlapGrid r q hrq N i.succ:ℝ)-vectorUniformOverlapGrid r q hrq N i.castSucc =
      ((q:ℝ)-r)/(N+1) := by
  simp only [vectorUniformOverlapGrid_coe, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem vectorUniformOverlapGrid_riemann_tendsto (r q : Paper.Overlap) (hrq : r≤q)
    (f : ℝ→ℝ) (hf : Continuous f) :
    Tendsto (fun N => ∑i : Fin (N+1), f (vectorUniformOverlapGrid r q hrq N i.castSucc)*
      ((vectorUniformOverlapGrid r q hrq N i.succ:ℝ)-vectorUniformOverlapGrid r q hrq N i.castSucc))
      atTop (𝓝 (∫s in (r:ℝ)..(q:ℝ), f s)) := by
  let d : ℝ≥0 := ⟨(q:ℝ)-r, sub_nonneg.mpr hrq⟩
  have h := FRSB.uniform_left_riemann_tendsto (fun s => f ((r:ℝ)+s))
    (hf.comp (continuous_const.add continuous_id)) d
  have hi : (∫s in (0:ℝ)..(d:ℝ), f ((r:ℝ)+s))=∫s in (r:ℝ)..(q:ℝ),f s := by
    have hd : (r:ℝ)+(d:ℝ)=(q:ℝ) := by change (r:ℝ)+((q:ℝ)-r)=(q:ℝ); ring
    simpa only [add_zero, hd] using
      intervalIntegral.integral_comp_add_left f (r:ℝ) (a:=0) (b:=(d:ℝ))
  rw [hi] at h
  convert h using 1
  funext N
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hc (j : ℕ) : (uniformPartitionTime d (N+1) j : ℝ)=
      ((q:ℝ)-r)*(j:ℝ)/(N+1) := by
    unfold uniformPartitionTime
    rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
    rw [show (d:ℝ)=(q:ℝ)-r from rfl, Nat.cast_add, Nat.cast_one]
  simp only [vectorUniformOverlapGrid_coe, Fin.val_castSucc, Fin.val_succ, Nat.cast_add,
    Nat.cast_one, hc]
  ring

end QuantitativePaper
