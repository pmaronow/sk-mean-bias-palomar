module
public import QuantitativePaper.SixthWindowProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The exact real fifth-root tilts and sixth/fifth event exponent. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem fifthRoot_pow_five {x : ℝ} (hx : 0≤x) : (x^(1/5:ℝ))^5=x := by
  rw [←Real.rpow_mul_natCast hx]
  norm_num

theorem sixth_power_fifthRoot {x : ℝ} (hx : 0≤x) : (x^(1/5:ℝ))^6=x^(6/5:ℝ) := by
  rw [←Real.rpow_mul_natCast hx]
  norm_num

theorem upper_sixth_tilt_identity (C x : ℝ) (hC : 0<C) (hx : 0<x) :
    let s:=x^(1/5:ℝ)/(6*C)^(1/5:ℝ)
    C*s^6-s*x=-(5/(6*(6*C)^(1/5:ℝ)))*x^(6/5:ℝ) := by
  dsimp only
  have hd : 0<(6*C)^(1/5:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hd5 := fifthRoot_pow_five (show 0≤6*C by positivity)
  have hx5 := fifthRoot_pow_five hx.le
  have hx6 : x^(6/5:ℝ)=x*x^(1/5:ℝ) := by
    rw [show (6/5:ℝ)=1+1/5 by norm_num,Real.rpow_add hx,Real.rpow_one]
  rw [hx6]
  field_simp
  ring_nf at hd5 hx5 ⊢
  nlinarith

theorem lower_sixth_tilt_identity (a x : ℝ) (ha : 0<a) (hx : 0<x) :
    let s:=(2*x/a)^(1/5:ℝ)
    s^5=2*x/a ∧ s^6=(2/a)^(6/5:ℝ)*x^(6/5:ℝ) := by
  dsimp only
  have hz : 0≤2*x/a := by positivity
  refine ⟨fifthRoot_pow_five hz,?_⟩
  rw [sixth_power_fifthRoot hz,show 2*x/a=(2/a)*x by ring,Real.mul_rpow (by positivity) hx.le]

theorem upper_sixth_tilt_mem (C x L : ℝ) (hC : 0<C) (hx : 0<x)
    (hL : 0<L) (hbound : x≤6*C*L^5) :
    0<x^(1/5:ℝ)/(6*C)^(1/5:ℝ) ∧ x^(1/5:ℝ)/(6*C)^(1/5:ℝ)≤L := by
  have hden : 0<(6*C)^(1/5:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨div_pos (Real.rpow_pos_of_pos hx _) hden,(div_le_iff₀ hden).2 ?_⟩
  have hh := Real.rpow_le_rpow hx.le hbound (by norm_num : (0:ℝ)≤1/5)
  rw [Real.mul_rpow (by positivity) (by positivity)] at hh
  have he : (L^5)^(1/5:ℝ)=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL.le]
    norm_num
  rw [he] at hh
  nlinarith

theorem lower_sixth_tilt_mem (a x L : ℝ) (ha : 0<a) (hx : 0<x)
    (hL : 0<L) (hbound : x≤a/2*(L/2)^5) :
    0<(2*x/a)^(1/5:ℝ) ∧ (2*x/a)^(1/5:ℝ)≤L/2 := by
  have hz : 0<2*x/a := by positivity
  refine ⟨Real.rpow_pos_of_pos hz _,?_⟩
  have hh : 2*x/a≤(L/2)^5 := by apply (div_le_iff₀ ha).2; nlinarith
  have ht := Real.rpow_le_rpow hz.le hh (by norm_num : (0:ℝ)≤1/5)
  have he : ((L/2)^5)^(1/5:ℝ)=L/2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (show 0≤L/2 by positivity)]
    norm_num
  simpa only [he] using ht

theorem lower_sixth_tilt_cutoff (a A N x : ℝ) (ha : 0<a) (hA : 0≤A)
    (hN : 0<N) (hx : 0<x) (hbound : a/2*A^5*N^(-(2/3:ℝ))≤x) :
    A*N^(-(2/15:ℝ))≤(2*x/a)^(1/5:ℝ) := by
  have hs0 : 0≤(2*x/a)^(1/5:ℝ) := Real.rpow_nonneg (by positivity) _
  apply le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ)≠0) hs0
  rw [fifthRoot_pow_five (by positivity : 0≤2*x/a),mul_pow,
    ←Real.rpow_mul_natCast hN.le]
  norm_num
  apply (le_div_iff₀ ha).2
  nlinarith

theorem lower_sixth_tilt_size (a A N s : ℝ) (ha : 0≤a) (hA : 0≤A)
    (hN : 0<N) (hs : A*N^(-(2/15:ℝ))≤s) :
    a*A^6*N^(1/5:ℝ)≤a*N*s^6 := by
  have hp := pow_le_pow_left₀ (by positivity : 0≤A*N^(-(2/15:ℝ))) hs 6
  have he : N*(A*N^(-(2/15:ℝ)))^6=A^6*N^(1/5:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    norm_num
    have hr : N*N^(-(4/5:ℝ))=N^(1/5:ℝ) := by
      calc
        _=N^(1:ℝ)*N^(-(4/5:ℝ)) := by rw [Real.rpow_one]
        _=N^(1/5:ℝ) := by rw [←Real.rpow_add hN];norm_num
    calc
      _=A^6*(N*N^(-(4/5:ℝ))) := by ring
      _=_ := by rw [hr]
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg ha hN.le)
  nlinarith [he]

end QuantitativePaper
