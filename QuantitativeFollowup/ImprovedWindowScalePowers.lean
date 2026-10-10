module
public import QuantitativeFollowup.FourTermBudgetWindowPowers

@[expose] public section

/-! The literal improved tilt has the sixth-moment size N^(4/25) and
inverse-square scale N^(7/25). -/
noncomputable section
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem improved_window_sixth_size (N A : ℝ) (hN : 0<N) :
    N*(A*N^(-(7/50:ℝ)))^6=A^6*N^(4/25:ℝ) := by
  rw [mul_pow,←Real.rpow_mul_natCast hN.le]
  have he : N*N^((-(7/50:ℝ))*(6:ℕ))=N^(4/25:ℝ):=by
    calc
      _=N^(1:ℝ)*N^((-(7/50:ℝ))*(6:ℕ)):=by rw [Real.rpow_one]
      _=_:=by rw [←Real.rpow_add hN];congr 1 <;> norm_num
  calc
    _=A^6*(N*N^((-(7/50:ℝ))*(6:ℕ))):=by ring
    _=_:=by rw [he]

theorem improved_window_inverse_square (N A b : ℝ) (hN : 0<N) (hA : 0<A) :
    b^2/(A*N^(-(7/50:ℝ)))^2=(b^2/A^2)*N^(7/25:ℝ) := by
  rw [mul_pow,←Real.rpow_mul_natCast hN.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg hN.le]
  field_simp

end QuantitativeFollowup
