module
public import QuantitativePaper.ResponseScalarIntegralCauchySchwarz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! True finite-cell integral Cauchy–Schwarz. Pointwise inequalities are
needed only in cell interiors; all three actual sources are integrable
on the closed cell. Repeated nodes contribute zero. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem response_cell_integral_cauchy_schwarz (N : ℕ) (Q : ℕ→ℝ)
    (e p x : ℕ→ℝ→ℝ) (hQ : ∀i<N,Q i≤Q (i+1))
    (he : ∀i<N,IntervalIntegrable (e i) volume (Q i) (Q (i+1)))
    (hp : ∀i<N,IntervalIntegrable (p i) volume (Q i) (Q (i+1)))
    (hx : ∀i<N,IntervalIntegrable (x i) volume (Q i) (Q (i+1)))
    (hpoint : ∀i<N,∀q∈Ioo (Q i) (Q (i+1)),
      0≤e i q ∧ 0≤x i q ∧ (p i q)^2≤e i q*x i q) :
    (∑i∈Finset.range N,∫q in Q i..Q (i+1),p i q)^2≤
      (∑i∈Finset.range N,∫q in Q i..Q (i+1),e i q)*
      (∑i∈Finset.range N,∫q in Q i..Q (i+1),x i q) := by
  have hquad (v : ℝ) : 0≤
      (∑i∈Finset.range N,∫q in Q i..Q (i+1),e i q)*(v*v)+
      (2*(∑i∈Finset.range N,∫q in Q i..Q (i+1),p i q))*v+
      (∑i∈Finset.range N,∫q in Q i..Q (i+1),x i q):=by
    have hcell (i : ℕ) (hi : i<N) : 0≤
        (∫q in Q i..Q (i+1),e i q)*(v*v)+
        (2*(∫q in Q i..Q (i+1),p i q))*v+
        (∫q in Q i..Q (i+1),x i q):=by
      have hh : 0≤∫q in Q i..Q (i+1),e i q*v^2+2*p i q*v+x i q:=by
        rw [intervalIntegral.integral_of_le (hQ i hi)]
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc,
          (volume.ae_ne (Q (i+1))).filter_mono (ae_mono Measure.restrict_le_self)] with q hq hqne
        have h:=hpoint i hi q ⟨hq.1,lt_of_le_of_ne hq.2 hqne⟩
        exact response_nonnegative_quadratic h.1 h.2.1 h.2.2 v
      have e₁:=intervalIntegral.integral_add
        (((he i hi).mul_const (v^2)).add (((hp i hi).const_mul 2).mul_const v)) (hx i hi)
      have e₂:=intervalIntegral.integral_add (he i hi |>.mul_const (v^2))
        (((hp i hi).const_mul 2).mul_const v)
      try simp only [Pi.add_apply] at e₁ e₂
      rw [e₁,e₂,intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul] at hh
      nlinarith only [hh]
    have hh:=Finset.sum_nonneg (s:=Finset.range N) (fun i hi=>hcell i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,mul_assoc] using hh
  have hd:=discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

end QuantitativePaper
