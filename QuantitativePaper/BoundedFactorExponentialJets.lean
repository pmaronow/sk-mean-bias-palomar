module
public import QuantitativePaper.LocalJetBounds
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-! Genuine finite-order exponential envelopes survive multiplication by
a factor with uniformly bounded actual jets. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

theorem bounded_factor_exponential_jets (N : ℕ) (f g : E→ℝ) (U : Set E)
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    (C R M : ℝ) (hC : 0≤C) (hR : 0≤R) (hM : 0≤M)
    (hfj : ∀r,r≤N→∀x∈U,‖iteratedFDeriv ℝ r f x‖≤C*Real.exp (R*‖x‖))
    (hgj : ∀r,r≤N→∀x∈U,‖iteratedFDeriv ℝ r g x‖≤M) :
    ∀r,r≤N→∀x∈U,‖iteratedFDeriv ℝ r (fun y=>g y*f y) x‖≤
      (2:ℝ)^N*M*C*Real.exp (R*‖x‖) := by
  intro r hr x hx
  have hn:=norm_iteratedFDeriv_mul_le_on_open g f U hU hg hf hr x hx
  have hs : (∑i∈Finset.range (r+1),(r.choose i:ℝ)*
      ‖iteratedFDeriv ℝ i g x‖*‖iteratedFDeriv ℝ (r-i) f x‖)≤
      (2:ℝ)^r*M*(C*Real.exp (R*‖x‖)):=by
    calc
      _≤∑i∈Finset.range (r+1),(r.choose i:ℝ)*M*(C*Real.exp (R*‖x‖)):=by
        apply Finset.sum_le_sum
        intro i hi
        have hir : i≤r:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hgj i (hir.trans hr) x hx) (by positivity))
          (hfj (r-i) ((Nat.sub_le _ _).trans hr) x hx) (norm_nonneg _) (by positivity)
      _=_:=by
        rw [←Finset.sum_mul,←Finset.sum_mul]
        have he : (∑i∈Finset.range (r+1),(r.choose i:ℝ))=(2:ℝ)^r:=by
          exact_mod_cast Nat.sum_range_choose r
        rw [he]
  refine hn.trans (hs.trans ?_)
  have hp : (2:ℝ)^r≤(2:ℝ)^N:=pow_le_pow_right₀ (by norm_num) hr
  have hm:=mul_le_mul_of_nonneg_right hp
    (mul_nonneg hM (mul_nonneg hC (Real.exp_pos (R*‖x‖)).le))
  nlinarith

end QuantitativePaper
