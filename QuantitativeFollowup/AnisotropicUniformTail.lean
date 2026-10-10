module
public import QuantitativeFollowup.AnisotropicTailRecursion

@[expose] public section

/-! Exact dyadic refinement and profile estimates for the actual restarted
anisotropic Gaussian recursion at every overlap, including atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 300000

theorem anisotropicTailRecursion_grid_prefix (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (q : ℝ) {j : ℕ} (hj : j ≤ N+1) :
    anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ N) q (j+1)=
      gaussianUniformTailCascade (N+1) q (anisotropicUnitInput D) (Paper.parisiCDF μ)
        (anisotropicGridTerminalPotential D) j := by
  induction j with
  | zero =>
    rw [anisotropicTailRecursion]
    have hA : Real.sqrt
        (max q ((Paper.parisiGridRSBScheme μ N).q (N+1+2))-
          max q ((Paper.parisiGridRSBScheme μ N).q (N+1+1))) • anisotropicUnitInput D=
        (0 : Field n→L[ℝ]AnisotropicParameter n) := by
      simp [Paper.parisiGridRSBScheme,Paper.parisiGridSchemeOverlap]
      ext w i
      simp
    simp only [Nat.sub_zero] 
    rw [hA]
    exact funext fun P => gaussianShiftColeHopf_zero_input (n:=n) _ _ P
  | succ j ih =>
    rw [anisotropicTailRecursion,ih (by omega),gaussianUniformTailCascade]
    have hi0 : N+2-(j+1)=N+1-j := by omega
    have hi1 : N+3-(j+1)=N+2-j := by omega
    have hm0 : N+1-j≠0 := by omega
    have hq0 : N+1-j-1=N-j := by omega
    have hq1 : N+2-j-1=N+1-j := by omega
    simp only [hi0,hi1,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeMass,ite_eq_right hm0,
      Paper.parisiGridSchemeOverlap,hq0,hq1,Nat.min_eq_left (by omega : N-j ≤ N+1),
      Nat.min_eq_left (by omega : N+1-j ≤ N+1),parisiCDF_grid_at_node,Nat.add_sub_cancel]

theorem anisotropicTailRecursion_grid_eq_uniform (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (q : ℝ) :
    anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ N) q (N+3)=
      gaussianUniformTailCascade (N+1) q (anisotropicUnitInput D) (Paper.parisiCDF μ)
        (anisotropicGridTerminalPotential D) (N+1) := by
  rw [show N+3=(N+2)+1 by omega,anisotropicTailRecursion]
  simp only [show N+1+2-(N+2)=1 by omega,
    show N+1+1-(N+2)=0 by omega,Paper.parisiGridRSBScheme,
    Paper.parisiGridSchemeOverlap,show 1-1=0 by omega,Nat.zero_min,Nat.cast_zero,
    zero_div,sub_self,Real.sqrt_zero]
  have hA : (0 : ℝ) • anisotropicUnitInput D=(0 : Field n→L[ℝ]AnisotropicParameter n) := by
    ext w i
    simp
  rw [hA]
  funext P
  rw [gaussianShiftColeHopf_zero_input]
  exact congrFun (anisotropicTailRecursion_grid_prefix D μ N q le_rfl) P

theorem anisotropicTailRecursion_grid_refine_coarse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (q : ℝ) :
    anisotropicTailRecursion D
      (Paper.parisiGridRSBScheme (Paper.parisiGridMeasure μ N) (2*N+1)) q (2*N+4)=
      anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ N) q (N+3) := by
  rw [show 2*N+4=(2*N+1)+3 by omega,anisotropicTailRecursion_grid_eq_uniform,
    anisotropicTailRecursion_grid_eq_uniform]
  simpa only [show 2*N+1+1=2*(N+1) by omega] using gaussianUniformTailCascade_coarse_double μ N q
    (anisotropicUnitInput D) (anisotropicGridTerminalPotential D) ‖anisotropicEnergyMap D‖₊
    (anisotropicGridTerminalPotential_lipschitz D)

theorem anisotropicTailRecursion_grid_profile_abs_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (N : ℕ) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1)
    (P : AnisotropicParameter n) :
    |anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ N) q (N+3) P-
      anisotropicTailRecursion D (Paper.parisiGridRSBScheme ν N) q (N+3) P| ≤
      anisotropicProfileStabilityConstant D*(Paper.parisiCDFDistance μ ν+2/(N+1 : ℕ)) := by
  have hh := anisotropicTailRecursion_aligned_CDFDistance_abs_sub_le D
    (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) q hq (fun _ _ => rfl) P
  rw [FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (parisiCDFDistance_grid_pair_le μ ν N)
    (anisotropicProfileStabilityConstant_nonneg D))

theorem anisotropicTailRecursion_grid_adjacent_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1)
    (P : AnisotropicParameter n) :
    |anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ (2*N+1)) q (2*N+4) P-
      anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ N) q (N+3) P| ≤
      2*anisotropicProfileStabilityConstant D/(N+1 : ℕ) := by
  have hh := anisotropicTailRecursion_grid_profile_abs_sub_le D μ (Paper.parisiGridMeasure μ N)
    (2*N+1) q hq P
  rw [anisotropicTailRecursion_grid_refine_coarse D μ N q] at hh
  have he : anisotropicProfileStabilityConstant D*(1/(N+1 : ℕ)+2/(2*N+1+1 : ℕ))=
      2*anisotropicProfileStabilityConstant D/(N+1 : ℕ) := by push_cast;field_simp;ring
  exact hh.trans (he ▸ mul_le_mul_of_nonneg_left
    (add_le_add (Paper.parisiCDFDistance_grid_le μ N) le_rfl) (anisotropicProfileStabilityConstant_nonneg D))

end QuantitativeFollowup
