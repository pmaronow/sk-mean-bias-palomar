module
public import QuantitativePaper.ResponseC1Limits

@[expose] public section

/-! A convergent actual signal and positive denominator upper bound give
an honest lower comparison sequence for the approximating curvatures. -/
noncomputable section
open Filter
open scoped Topology
namespace QuantitativePaper

theorem response_curvature_lower_sequence (Sj Dj Fj : ℕ→ℝ) (S D Y A C : ℝ)
    (hS : Tendsto Sj atTop (nhds S)) (hD : Tendsto Dj atTop (nhds D))
    (hY : 0<Y) (hDY : D≤Y) (hC : C*Y≤A*S^2)
    (hF : ∀j,0≤Fj j) (hbound : ∀j,A*(Sj j)^2≤Fj j*Dj j) :
    ∃Rj : ℕ→ℝ,∃R : ℝ,C≤R ∧ Tendsto Rj atTop (nhds R) ∧ ∀j,Rj j≤Fj j:=by
  refine ⟨fun j=>A*(Sj j)^2/(max Y (Dj j)),A*S^2/Y,?_,?_,?_⟩
  · exact (le_div_iff₀ hY).mpr hC
  · have hm : Tendsto (fun j=>max Y (Dj j)) atTop (nhds Y):=by
      simpa only [max_eq_left hDY] using (tendsto_const_nhds (x:=Y)).max hD
    exact (tendsto_const_nhds.mul (hS.pow 2)).div hm hY.ne'
  · intro j
    apply (div_le_iff₀ (hY.trans_le (le_max_left _ _))).mpr
    exact (hbound j).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (hF j))

end QuantitativePaper
