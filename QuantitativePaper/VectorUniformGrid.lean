module
public import QuantitativePaper.VectorSemigroup
public import Paper.ParisiGridCDF

@[expose] public section

/-! A concrete uniform-cell representation of the actual grid approximation.
The repeated endpoint cells are proved to be identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem parisiCDF_grid_at_node (μ : Paper.ParisiMeasure) (n i : ℕ) :
    Paper.parisiCDF (Paper.parisiGridMeasure μ n) ((i : ℝ)/(n+1 : ℕ))=
      Paper.parisiCDF μ ((i : ℝ)/(n+1 : ℕ)) := by
  have hd : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have he : {q : Paper.Overlap | (Paper.parisiGridRound n q : ℝ) ≤ (i : ℝ)/(n+1 : ℕ)}=
      {q : Paper.Overlap | (q : ℝ) ≤ (i : ℝ)/(n+1 : ℕ)} := by
    ext q
    change ((Nat.ceil ((n+1 : ℕ)*(q : ℝ)) : ℝ)/(n+1 : ℕ) ≤ (i : ℝ)/(n+1 : ℕ)) ↔
      (q : ℝ) ≤ (i : ℝ)/(n+1 : ℕ)
    rw [div_le_div_iff_of_pos_right hd,le_div_iff₀ hd]
    constructor
    · intro h
      have hc : Nat.ceil ((n+1 : ℕ)*(q : ℝ)) ≤ i := by exact_mod_cast h
      simpa only [mul_comm] using Nat.ceil_le.mp hc
    · intro h
      have hc : Nat.ceil ((n+1 : ℕ)*(q : ℝ)) ≤ i := Nat.ceil_le.mpr (by simpa only [mul_comm] using h)
      exact_mod_cast hc
  unfold Paper.parisiCDF Paper.parisiGridMeasure
  rw [ProbabilityMeasure.toMeasure_map,Measure.map_apply (Paper.measurable_parisiGridRound n)
    (isClosed_le continuous_subtype_val continuous_const).measurableSet]
  exact congrArg (fun E : Set Paper.Overlap => ((μ : Measure Paper.Overlap) E).toReal) he

def vectorUniformGridCascade {n : ℕ} (N : ℕ) (c : ℝ) (a : ℝ→ℝ) (f : Field n→ℝ) :
    ℕ→(Field n→ℝ)
  | 0 => f
  | j+1 => vectorColeHopfStep (c/(N : ℝ)) (a ((N-1-j : ℕ)/(N : ℝ)))
      (vectorUniformGridCascade N c a f j)

theorem vectorUniformGridCascade_lipschitz {n : ℕ} (N : ℕ) (c : ℝ)
    (a : ℝ→ℝ) (ha : ∀x,0  ≤  a x) (f : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (j : ℕ) :
    LipschitzWith K (vectorUniformGridCascade N c a f j) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact vectorColeHopfStep_lipschitz _ _ ih _ _ (ha _)

theorem vectorRecursion_grid_prefix {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t : ℝ) (p : Couplings n×ℝ) {j : ℕ} (hj : j  ≤  N+1) :
    vectorRecursion (Paper.parisiGridRSBScheme μ N) β t p (j+1)=
      vectorUniformGridCascade (N+1) ((1-t)*β^2) (Paper.parisiCDF μ)
        (vectorTerminalPotential n β t p) j := by
  induction j with
  | zero =>
    funext x
    simp [vectorRecursion,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeOverlap,
      vectorUniformGridCascade]
  | succ j ih =>
    rw [vectorRecursion,ih (by omega),vectorUniformGridCascade]
    have hi0 : N+2-(j+1)=N+1-j := by omega
    have hi1 : N+3-(j+1)=N+2-j := by omega
    have hj' : j  ≤  N := by omega
    have hm0 : N+1-j ≠ 0 := by omega
    have hq0 : (N+1-j)-1=N-j := by omega
    have hq1 : (N+2-j)-1=N+1-j := by omega
    simp only [hi0,hi1,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeMass,ite_eq_right hm0,
      Paper.parisiGridSchemeOverlap,hq0,hq1,Nat.min_eq_left (by omega : N-j  ≤  N+1),
      Nat.min_eq_left (by omega : N+1-j  ≤  N+1),parisiCDF_grid_at_node]
    have he : (1-t)*(β^2*((N+1-j : ℕ)/(N+1 : ℕ)-(N-j : ℕ)/(N+1 : ℕ)))=
        ((1-t)*β^2)/(N+1 : ℕ) := by
      have hs : N+1-j=(N-j)+1 := by omega
      rw [hs,Nat.cast_add,Nat.cast_one]
      ring
    rw [he]
    simp only [Nat.add_sub_cancel]

theorem vectorRecursion_grid_eq_uniform {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t : ℝ) (p : Couplings n×ℝ) :
    vectorRecursion (Paper.parisiGridRSBScheme μ N) β t p (N+3)=
      vectorUniformGridCascade (N+1) ((1-t)*β^2) (Paper.parisiCDF μ)
        (vectorTerminalPotential n β t p) (N+1) := by
  rw [show N+3=(N+2)+1 by omega,vectorRecursion]
  simp only [show N+1+2-(N+2)=1 by omega,
    show N+1+1-(N+2)=0 by omega,Paper.parisiGridRSBScheme,
    Paper.parisiGridSchemeOverlap,show 1-1=0 by omega,
    Nat.zero_min,Nat.cast_zero,zero_div,sub_self,mul_zero]
  funext x
  rw [vectorColeHopfStep_zero_variance]
  exact congrFun (vectorRecursion_grid_prefix μ N β t p le_rfl) x

end QuantitativePaper
