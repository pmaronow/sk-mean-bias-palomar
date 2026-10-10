module
public import QuantitativePaper.VectorUniformTail

@[expose] public section

/-! Actual refinement of clamped Gaussian cells, including the cell that
contains the restarted overlap. Its two variances telescope exactly. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorUniformTailCascade_double_prefix {n : ℕ} (N : ℕ) (hN : 0<N)
    (c q : ℝ) (hc : 0 ≤ c) (a b : ℝ→ℝ) (ha : ∀x,0 ≤ a x)
    (hab : ∀j<N,
      b ((2*N-1-2*j : ℕ)/(2*N : ℝ))=a ((N-1-j : ℕ)/(N : ℝ)) ∧
      b ((2*N-1-(2*j+1) : ℕ)/(2*N : ℝ))=a ((N-1-j : ℕ)/(N : ℝ)))
    (f : Field n→ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) {j : ℕ} (hj : j ≤ N) :
    vectorUniformTailCascade (2*N) c q b f (2*j)=
      vectorUniformTailCascade N c q a f j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j<N := by omega
    rw [show 2*(j+1)=(2*j+1)+1 by omega,vectorUniformTailCascade,
      vectorUniformTailCascade,ih (by omega),vectorUniformTailCascade]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [(hab j hj').1,(hab j hj').2]
    have hu : 2*N-2*j=2*(N-j) := by omega
    have hl : 2*N-1-(2*j+1)=2*(N-1-j) := by omega
    have hm : 2*N-(2*j+1)=2*N-1-2*j := by omega
    have hn0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
    have heu : ((2*N-2*j : ℕ) : ℝ)/(2*N : ℝ)=((N-j : ℕ) : ℝ)/(N : ℝ) := by
      rw [hu,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
    have hel : ((2*N-1-(2*j+1) : ℕ) : ℝ)/(2*N : ℝ)=
        ((N-1-j : ℕ) : ℝ)/(N : ℝ) := by
      rw [hl,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
    funext x
    have hv0 : 0 ≤ c*(max q ((2*N-1-2*j : ℕ)/(2*N : ℝ))-
        max q ((2*N-1-(2*j+1) : ℕ)/(2*N : ℝ))) := by
      apply mul_nonneg hc
      apply sub_nonneg.mpr
      apply max_le_max le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : 2*N-1-(2*j+1) ≤ 2*N-1-2*j)
    have hv1 : 0 ≤ c*(max q ((2*N-2*j : ℕ)/(2*N : ℝ))-
        max q ((2*N-1-2*j : ℕ)/(2*N : ℝ))) := by
      apply mul_nonneg hc
      apply sub_nonneg.mpr
      apply max_le_max le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : 2*N-1-2*j ≤ 2*N-2*j)
    rw [hm]
    rw [vectorColeHopfStep_semigroup _ K
      (vectorUniformTailCascade_lipschitz N c q a ha f K hf j)
      _ (ha _) _ _ hv0 hv1 x]
    congr 1
    rw [heu,hel]
    ring

theorem vectorUniformTailCascade_coarse_double {n : ℕ} (μ : Paper.ParisiMeasure)
    (N : ℕ) (c q : ℝ) (hc : 0 ≤ c) (f : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) :
    vectorUniformTailCascade (2*(N+1)) c q (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f
      (2*(N+1))=vectorUniformTailCascade (N+1) c q (Paper.parisiCDF μ) f (N+1) := by
  apply vectorUniformTailCascade_double_prefix (N+1) (by omega) c q hc _ _
    (Paper.parisiCDF_nonneg μ) _ f K hf le_rfl
  intro j hj
  simpa only [Nat.cast_add,Nat.cast_one] using parisiCDF_coarse_half_cell μ N j hj

theorem vectorTailRecursion_grid_refine_coarse {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t q : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) :
    vectorTailRecursion (Paper.parisiGridRSBScheme (Paper.parisiGridMeasure μ N) (2*N+1))
      β t q p (2*N+4)=
      vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (N+3) := by
  rw [show 2*N+4=(2*N+1)+3 by omega,vectorTailRecursion_grid_eq_uniform,
    vectorTailRecursion_grid_eq_uniform]
  simpa only [show 2*N+1+1=2*(N+1) by omega] using
    vectorUniformTailCascade_coarse_double μ N ((1-t)*β^2) q
      (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) _ _
      (vectorTerminalPotential_lipschitz n β t p)

end QuantitativePaper
