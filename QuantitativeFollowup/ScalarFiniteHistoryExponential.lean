module
public import QuantitativeFollowup.ScalarFiniteMarkedDensity
public import QuantitativePaper.HistoryDensityExponential

@[expose] public section

/-! Telescoping the actual finite scalar path density on arbitrary retained
histories, including histories with repeated time coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {k : ℕ}

theorem scalar_finiteHistoryDensity_eq_common (w : ℕ→ℝ→ℝ→ℝ≥0∞) (n : ℕ)
    (h : Fin (n+1)→ℝ) :
    FRSB.finiteHistoryDensity w n h=FourPapersCommon.finiteHistoryDensity w n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FRSB.finiteHistoryDensity,FourPapersCommon.finiteHistoryDensity,ih]
    rfl

theorem scalarFiniteHistory_transition_exponent (s : RSBScheme k) (β : ℝ)
    (h : Fin (k+3)→ℝ) :
    QuantitativePaper.historyTransitionSum
      (fun i x y => FRSB.forwardSchemeMass s i *
        (Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 (i+1),y)-
         Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 i,x)))
      (k+2) h =
    Real.log (Real.cosh (h (Fin.last (k+2))))-
      ∑i∈Finset.range (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),h (Fin.ofNat (k+3) (i+1))) := by
  let U : ℕ→ℝ := fun i => Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 i,h (Fin.ofNat (k+3) i))
  have hi0 (i : Fin (k+2)) : (Fin.ofNat (k+3) (i:ℕ))=i.castSucc := by
    apply Fin.ext
    change (i:ℕ) % (k+3)=(i:ℕ)
    exact Nat.mod_eq_of_lt (by have := i.isLt;omega)
  have hi1 (i : Fin (k+2)) : (Fin.ofNat (k+3) ((i:ℕ)+1))=i.succ := by
    apply Fin.ext
    change ((i:ℕ)+1) % (k+3)=(i:ℕ)+1
    exact Nat.mod_eq_of_lt (by have := i.isLt;omega)
  have hsum : QuantitativePaper.historyTransitionSum
      (fun i x y => FRSB.forwardSchemeMass s i *
        (Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 (i+1),y)-
         Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 i,x)))
      (k+2) h = ∑i∈Finset.range (k+2),FRSB.forwardSchemeMass s i*(U (i+1)-U i) := by
    rw [←Fin.sum_univ_eq_sum_range]
    unfold QuantitativePaper.historyTransitionSum
    apply Finset.sum_congr rfl
    intro i _
    simp only [U,hi0 i,hi1 i]
  rw [hsum,FRSB.finite_weighted_difference_telescope]
  have hlast : Fin.ofNat (k+3) (k+2)=Fin.last (k+2) := by
    apply Fin.ext
    change (k+2)%(k+3)=k+2
    exact Nat.mod_eq_of_lt (by omega)
  rw [show FRSB.forwardSchemeMass s (k+1)=1 by simp [FRSB.forwardSchemeMass,s.m_top],
    show FRSB.forwardSchemeMass s 0=0 by simp [FRSB.forwardSchemeMass,s.m_zero]]
  simp only [one_mul,zero_mul,sub_zero]
  have ht : U (k+1+1)=Real.log (Real.cosh (h (Fin.last (k+2)))) := by
    change Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (k+2),h (Fin.ofNat (k+3) (k+2)))=_
    rw [hlast,FRSB.forwardSchemeTime_top s 1 (by norm_num) le_rfl]
    exact Paper.parisiPotential_terminal β _ _
  rw [ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i+1≤k+1 := by have := Finset.mem_range.mp hi;omega
  simp only [FRSB.forwardSchemeMass,min_eq_left hile,min_eq_left (by omega : i≤k+1),U]

theorem scalarFiniteHistory_transition_density (s : RSBScheme k) (β : ℝ)
    (h : Fin (k+3)→ℝ) :
    FRSB.finiteHistoryDensity (FRSB.forwardSchemeWeight s β 1) (k+2) h =
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h (Fin.last (k+2))))-
        ∑i∈Finset.range (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
          (FRSB.forwardSchemeTime s 1 (i+1),h (Fin.ofNat (k+3) (i+1))))) := by
  rw [scalar_finiteHistoryDensity_eq_common]
  change FourPapersCommon.finiteHistoryDensity (fun i x y => ENNReal.ofReal (Real.exp
    (FRSB.forwardSchemeMass s i*(Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),y)-Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 i,x))))) (k+2) h=_
  rw [QuantitativePaper.finiteHistoryDensity_exp_sum,scalarFiniteHistory_transition_exponent]

theorem scalarFiniteHistory_transition_spin_density (s : RSBScheme k) (β : ℝ)
    (p : (Fin (k+3)→ℝ)×Bool) :
    FRSB.finiteHistoryDensity (FRSB.forwardSchemeWeight s β 1) (k+2) p.1*
      ENNReal.ofReal (scalarSpinWeight (p.1 (Fin.last (k+2))) p.2)=scalarFiniteHistoryDensity s β p := by
  rw [scalarFiniteHistory_transition_density,←ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold scalarFiniteHistoryDensity scalarSpinWeight
  rw [show (1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)];norm_num,
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
  congr 1
  rw [Real.exp_sub,Real.exp_log (Real.cosh_pos _),Real.exp_sub]
  field_simp

end QuantitativeFollowup
