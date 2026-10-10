module
public import QuantitativeFollowup.AnisotropicUniformGrid
public import QuantitativeFollowup.GaussianShiftTailSemigroup
public import QuantitativePaper.VectorTailProfileStability

@[expose] public section

/-! A restarted anisotropic recursion is a literal prefix of an admissible
clamped profile. Its stability is uniform in the restart overlap. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 200000

def anisotropicTailRecursion (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : ℝ) :
    ℕ→AnisotropicParameter n→ℝ
  | 0 => anisotropicGridTerminalPotential D
  | j+1 => gaussianShiftColeHopf
      (Real.sqrt (max q (s.q (k+2-j))-max q (s.q (k+1-j))) • anisotropicUnitInput D)
      (s.m (k+1-j)) (anisotropicTailRecursion D s q j)

theorem anisotropicTailRecursion_eq_clamped (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) (hq : q∈Icc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ k+2) :
    anisotropicTailRecursion D s q j=anisotropicFinitePotential D (vectorClampedScheme s q hq) j := by
  induction j with
  | zero => exact (anisotropicFinitePotential_terminal_softmax D _).symm
  | succ j ih =>
    rw [anisotropicTailRecursion,anisotropicFinitePotential_gaussianShiftColeHopf,ih (by omega)]
    have hi : k+1+1-j=(k+1-j)+1 := by omega
    have hi' : k+1+2-j=(k+2-j)+1 := by omega
    simp only [anisotropicSchemeMass,anisotropicSchemeInput,hi,hi',
      vectorClampedScheme_mass_succ,vectorClampedScheme_overlap_succ,anisotropicUnitInput]

theorem anisotropicTailRecursion_zero (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} (hj : j ≤ k+2) : anisotropicTailRecursion D s 0 j=anisotropicFinitePotential D s j := by
  induction j with
  | zero => exact (anisotropicFinitePotential_terminal_softmax D s).symm
  | succ j ih =>
    rw [anisotropicTailRecursion,anisotropicFinitePotential_gaussianShiftColeHopf,ih (by omega),
      max_eq_right (s.q_nonneg (by omega : k+2-j ≤ k+2)),
      max_eq_right (s.q_nonneg (by omega : k+1-j ≤ k+2))]
    rfl

theorem anisotropicTailRecursion_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} (hj : j ≤ k+2) : anisotropicTailRecursion D s 1 j=anisotropicGridTerminalPotential D := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [anisotropicTailRecursion,ih (by omega),
      max_eq_left (s.q_le_one (by omega : k+2-j ≤ k+2)),
      max_eq_left (s.q_le_one (by omega : k+1-j ≤ k+2))]
    simp only [sub_self,Real.sqrt_zero]
    have hA : (0 : ℝ) • anisotropicUnitInput D=(0 : Field n→L[ℝ]AnisotropicParameter n) := by
      ext w i
      simp
    rw [hA]
    exact funext fun P => gaussianShiftColeHopf_zero_input (n:=n) _ _ P

theorem anisotropicTailRecursion_aligned_profile_abs_sub_le (D : AnisotropicSpinModel n)
    (s r : RSBScheme k) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1)
    (hgrid : ∀i,i ≤ k+2 → s.q i=r.q i) (P : AnisotropicParameter n) :
    |anisotropicTailRecursion D s q (k+2) P-anisotropicTailRecursion D r q (k+2) P| ≤
      anisotropicAlignedProfileError D s r (k+2) := by
  have hclamp : ∀i,i ≤ k+1+2 →
      (vectorClampedScheme s q hq).q i=(vectorClampedScheme r q hq).q i := by
    intro i hi
    by_cases h0 : i=0
    · subst i;simp [vectorClampedScheme,clampedSchemeOverlap]
    · simp only [vectorClampedScheme,clampedSchemeOverlap,ite_eq_right h0]
      rw [hgrid (i-1) (by omega)]
  have hh := anisotropicFinitePotential_aligned_profile_abs_sub_le D
    (vectorClampedScheme s q hq) (vectorClampedScheme r q hq) hclamp (k+2) P
  rw [←anisotropicTailRecursion_eq_clamped D s q hq le_rfl,
    ←anisotropicTailRecursion_eq_clamped D r q hq le_rfl] at hh
  apply hh.trans
  unfold anisotropicAlignedProfileError
  apply Finset.sum_le_sum
  intro l hl
  have hl' : l<k+2 := Finset.mem_range.mp hl
  have hi0 : k+1+1-l=(k+1-l)+1 := by omega
  have hi1 : k+1+2-l=(k+2-l)+1 := by omega
  rw [hi0,hi1,vectorClampedScheme_mass_succ,vectorClampedScheme_mass_succ,
    vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ]
  rw [show k+1-l+1=k+2-l by omega]
  have hlength := clamped_interval_length_le q (s.q (k+1-l)) (s.q (k+2-l))
    (s.q_mono' (k+2-l) (by omega) (k+1-l) (by omega))
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlength (anisotropicProfileStabilityConstant_nonneg D))
    (abs_nonneg (s.m (k+1-l)-r.m (k+1-l)))
  exact hb

theorem anisotropicTailRecursion_aligned_CDFDistance_abs_sub_le (D : AnisotropicSpinModel n)
    (s r : RSBScheme k) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1)
    (hgrid : ∀i,i ≤ k+2 → s.q i=r.q i) (P : AnisotropicParameter n) :
    |anisotropicTailRecursion D s q (k+2) P-anisotropicTailRecursion D r q (k+2) P| ≤
      anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance
        (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  simpa only [anisotropicAlignedProfileError_eq_CDFDistance D s r hgrid] using
    anisotropicTailRecursion_aligned_profile_abs_sub_le D s r q hq hgrid P

end QuantitativeFollowup
