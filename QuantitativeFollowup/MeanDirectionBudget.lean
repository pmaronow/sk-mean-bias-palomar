module
public import QuantitativeFollowup.DyadicLogOptimization

@[expose] public section

/-! Exact scalar assembly of the absolute constant in the mean-direction bound. -/
noncomputable section
namespace QuantitativeFollowup

theorem mean_direction_budget {j V R M y : ℝ} (hM : 0<M) (hy : 0<y)
    (hSplit : j≤2*V+2*R) (hV : V≤4/(M*y^2))
    (hR : R≤224*(1+logPlus M)^2/(M*y^2)) :
    j≤456*(1+logPlus M)^2/(M*y^2) := by
  have hD : 0<M*y^2:=mul_pos hM (sq_pos_of_pos hy)
  have hL : 1≤(1+logPlus M)^2:=by nlinarith [logPlus_nonneg M]
  calc
    j≤2*(4/(M*y^2))+2*(224*(1+logPlus M)^2/(M*y^2)) :=
      hSplit.trans (add_le_add (mul_le_mul_of_nonneg_left hV (by norm_num))
        (mul_le_mul_of_nonneg_left hR (by norm_num)))
    _=8/(M*y^2)+448*(1+logPlus M)^2/(M*y^2) := by ring
    _≤8*(1+logPlus M)^2/(M*y^2)+448*(1+logPlus M)^2/(M*y^2) := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    _=456*(1+logPlus M)^2/(M*y^2) := by ring

end QuantitativeFollowup
