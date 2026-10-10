module
public import QuantitativePaper.VectorUniformGrid

@[expose] public section

/-! Actual refinement of uniform Gaussian cells. Two adjacent equal-mass
half-cells equal one full cell; this is proved for the genuine integral recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorUniformGridCascade_double_prefix {n : ℕ} (N : ℕ) (hN : 0 < N)
    (c : ℝ) (hc : 0 ≤ c) (a b : ℝ→ℝ) (ha : ∀x,0 ≤ a x)
    (hab : ∀j<N,
      b ((2*N-1-2*j : ℕ)/(2*N : ℝ))=a ((N-1-j : ℕ)/(N : ℝ)) ∧
      b ((2*N-1-(2*j+1) : ℕ)/(2*N : ℝ))=a ((N-1-j : ℕ)/(N : ℝ)))
    (f : Field n→ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) {j : ℕ} (hj : j ≤ N) :
    vectorUniformGridCascade (2*N) c b f (2*j)=vectorUniformGridCascade N c a f j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j<N := by omega
    rw [show 2*(j+1)=(2*j+1)+1 by omega,vectorUniformGridCascade,
      vectorUniformGridCascade,ih (by omega),vectorUniformGridCascade]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [(hab j hj').1,(hab j hj').2]
    funext x
    have hv : 0 ≤ c/(2*N : ℝ) := div_nonneg hc (by positivity)
    have hh := vectorColeHopfStep_semigroup (vectorUniformGridCascade N c a f j) K
      (vectorUniformGridCascade_lipschitz N c a ha f K hf j)
      (a ((N-1-j : ℕ)/(N : ℝ))) (ha ((N-1-j : ℕ)/(N : ℝ)))
      (c/(2*N : ℝ)) (c/(2*N : ℝ)) hv hv x
    rw [hh]
    congr 1
    have hn0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
    field_simp [hn0]
    ring

theorem parisiCDF_coarse_half_cell (μ : Paper.ParisiMeasure) (N j : ℕ) (hj : j<N+1) :
    Paper.parisiCDF (Paper.parisiGridMeasure μ N)
        ((2*(N+1)-1-2*j : ℕ)/(2*(N+1) : ℝ))=
        Paper.parisiCDF μ ((N+1-1-j : ℕ)/(N+1 : ℝ)) ∧
    Paper.parisiCDF (Paper.parisiGridMeasure μ N)
        ((2*(N+1)-1-(2*j+1) : ℕ)/(2*(N+1) : ℝ))=
        Paper.parisiCDF μ ((N+1-1-j : ℕ)/(N+1 : ℝ)) := by
  have hn : (0 : ℝ)<(N+1 : ℝ) := by positivity
  have hi0 : N+1-1-j=N-j := by omega
  have hi1 : 2*(N+1)-1-2*j=2*(N-j)+1 := by omega
  have hi2 : 2*(N+1)-1-(2*j+1)=2*(N-j) := by omega
  rw [hi0,hi1,hi2]
  have hcast : ((2*(N-j) : ℕ) : ℝ)/(2*(N+1) : ℝ)=((N-j : ℕ) : ℝ)/(N+1 : ℝ) := by
    push_cast
    field_simp
  have hmid : ((2*(N-j)+1 : ℕ) : ℝ)/(2*(N+1 : ℝ))=
      ((N-j : ℕ) : ℝ)/(N+1 : ℝ)+1/(2*(N+1 : ℝ)) := by
    push_cast
    field_simp
  have hstep : (((N-j)+1 : ℕ) : ℝ)/(N+1 : ℝ)=((N-j : ℕ) : ℝ)/(N+1 : ℝ)+1/(N+1 : ℝ) := by
    push_cast
    ring
  simp only [Nat.cast_add,Nat.cast_one] at hmid hstep
  have hcell : ((2*(N-j)+1 : ℕ) : ℝ)/(2*(N+1 : ℝ))∈
      Ico (((N-j : ℕ) : ℝ)/(N+1 : ℕ)) ((((N-j)+1 : ℕ) : ℝ)/(N+1 : ℕ)) := by
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hmid]
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have hh : (0 : ℝ)<1/(N+1 : ℝ) := by positivity
      have he : 1/(2*(N+1 : ℝ))=(1/(N+1 : ℝ))/2 := by field_simp
      rw [he]
      have he' : (((N-j : ℕ) : ℝ)+1)/(N+1 : ℝ)=((N-j : ℕ) : ℝ)/(N+1 : ℝ)+1/(N+1 : ℝ) := by ring
      rw [he']
      linarith
  constructor
  · rw [Paper.parisiCDF_grid_eq_node μ N (N-j) hcell,parisiCDF_grid_at_node]
    simp only [Nat.cast_add,Nat.cast_one]
  · rw [hcast]
    simpa only [Nat.cast_add,Nat.cast_one] using parisiCDF_grid_at_node μ N (N-j)

theorem vectorUniformGridCascade_coarse_double {n : ℕ} (μ : Paper.ParisiMeasure)
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (f : Field n→ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) :
    vectorUniformGridCascade (2*(N+1)) c (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f
      (2*(N+1))=vectorUniformGridCascade (N+1) c (Paper.parisiCDF μ) f (N+1) := by
  apply vectorUniformGridCascade_double_prefix (N+1) (by omega) c hc _ _
    (Paper.parisiCDF_nonneg μ)
    _ f K hf le_rfl
  intro j hj
  simpa only [Nat.cast_add,Nat.cast_one] using parisiCDF_coarse_half_cell μ N j hj

theorem vectorRecursion_grid_refine_coarse {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) :
    vectorRecursion (Paper.parisiGridRSBScheme (Paper.parisiGridMeasure μ N) (2*N+1)) β t p (2*N+4)=
      vectorRecursion (Paper.parisiGridRSBScheme μ N) β t p (N+3) := by
  rw [show 2*N+4=(2*N+1)+3 by omega,vectorRecursion_grid_eq_uniform,
    vectorRecursion_grid_eq_uniform]
  simpa only [show 2*N+1+1=2*(N+1) by omega] using
    vectorUniformGridCascade_coarse_double μ N ((1-t)*β^2)
      (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) _ _
      (vectorTerminalPotential_lipschitz n β t p)

end QuantitativePaper
