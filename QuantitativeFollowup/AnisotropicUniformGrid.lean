module
public import QuantitativeFollowup.AnisotropicProfileStability
public import QuantitativeFollowup.GaussianShiftSemigroup
public import QuantitativePaper.VectorGridCDFBound

@[expose] public section

/-! Actual anisotropic grid potentials have an honest uniform Gaussian
representation. Repeated endpoint levels are identities, and true Gaussian
semigroup composition identifies coarse profiles on the refined grid. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem gaussianShiftColeHopf_zero_input {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E→ℝ) (a : ℝ) (x : E) : gaussianShiftColeHopf (0 : Field n→L[ℝ]E) a f x=f x := by
  by_cases ha : a=0
  · simp [gaussianShiftColeHopf,gaussianShiftAverage,ha]
  · simp only [gaussianShiftColeHopf,ha,ite_false,gaussianShiftPartition,zero_apply,add_zero,
      integral_const,probReal_univ,smul_eq_mul,one_mul,Real.log_exp]
    exact mul_div_cancel_left₀ (f x) ha

def anisotropicUnitInput (D : AnisotropicSpinModel n) : Field n→L[ℝ]AnisotropicParameter n :=
  (anisotropicFieldInjection n).comp (anisotropicNoiseMap D)

def anisotropicGridTerminalPotential (D : AnisotropicSpinModel n) : AnisotropicParameter n→ℝ :=
  finiteLinearSoftmax (anisotropicTerminalLinear D)

theorem anisotropicFinitePotential_grid_prefix (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) {j : ℕ} (hj : j ≤ N+1) :
    anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ N) (j+1)=
      gaussianUniformGridCascade (N+1) (anisotropicUnitInput D) (Paper.parisiCDF μ)
        (anisotropicGridTerminalPotential D) j := by
  induction j with
  | zero =>
    rw [anisotropicFinitePotential_gaussianShiftColeHopf,anisotropicFinitePotential_terminal_softmax]
    have hA : anisotropicSchemeInput D (Paper.parisiGridRSBScheme μ N) 0=0 := by
      simp [anisotropicSchemeInput,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeOverlap]
      ext x i
      simp
    rw [hA]
    exact funext fun P => gaussianShiftColeHopf_zero_input _ _ _
  | succ j ih =>
    rw [anisotropicFinitePotential_gaussianShiftColeHopf,ih (by omega),gaussianUniformGridCascade]
    have hi0 : N+2-(j+1)=N+1-j := by omega
    have hi1 : N+3-(j+1)=N+2-j := by omega
    have hj' : j ≤ N := by omega
    have hm0 : N+1-j≠0 := by omega
    have hq0 : N+1-j-1=N-j := by omega
    have hq1 : N+2-j-1=N+1-j := by omega
    simp only [anisotropicSchemeInput,anisotropicSchemeMass,hi0,hi1,Paper.parisiGridRSBScheme,
      Paper.parisiGridSchemeMass,ite_eq_right hm0,Paper.parisiGridSchemeOverlap,hq0,hq1,
      Nat.min_eq_left (by omega : N-j ≤ N+1),Nat.min_eq_left (by omega : N+1-j ≤ N+1),parisiCDF_grid_at_node]
    have he : ((N+1-j : ℕ)/(N+1 : ℕ)-(N-j : ℕ)/(N+1 : ℕ) : ℝ)=1/(N+1 : ℕ) := by
      have hs : N+1-j=N-j+1 := by omega
      rw [hs,Nat.cast_add,Nat.cast_one]
      ring
    rw [he]
    simp only [Nat.add_sub_cancel,anisotropicUnitInput]

theorem anisotropicFinitePotential_grid_eq_uniform (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) :
    anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ N) (N+3)=
      gaussianUniformGridCascade (N+1) (anisotropicUnitInput D) (Paper.parisiCDF μ)
        (anisotropicGridTerminalPotential D) (N+1) := by
  rw [show N+3=(N+2)+1 by omega,anisotropicFinitePotential_gaussianShiftColeHopf]
  have hA : anisotropicSchemeInput D (Paper.parisiGridRSBScheme μ N) (N+2)=0 := by
    simp only [anisotropicSchemeInput,show N+1+2-(N+2)=1 by omega,
      show N+1+1-(N+2)=0 by omega,Paper.parisiGridRSBScheme,
      Paper.parisiGridSchemeOverlap,show 1-1=0 by omega,Nat.zero_min,Nat.cast_zero,
      zero_div,sub_self,Real.sqrt_zero,zero_smul]
    ext x i
    simp
  rw [hA]
  funext P
  rw [gaussianShiftColeHopf_zero_input]
  exact congrFun (anisotropicFinitePotential_grid_prefix D μ N le_rfl) P

theorem anisotropicGridTerminalPotential_lipschitz (D : AnisotropicSpinModel n) :
    LipschitzWith ‖anisotropicEnergyMap D‖₊ (anisotropicGridTerminalPotential D) := by
  let s := Paper.parisiGridRSBScheme (Paper.diracOverlap 0 (by norm_num)) 0
  rw [anisotropicGridTerminalPotential,←anisotropicFinitePotential_terminal_softmax D s]
  exact anisotropicFinitePotential_lipschitz D s 0

theorem anisotropicFinitePotential_grid_refine_coarse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) :
    anisotropicFinitePotential D (Paper.parisiGridRSBScheme (Paper.parisiGridMeasure μ N) (2*N+1)) (2*N+4)=
      anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ N) (N+3) := by
  rw [show 2*N+4=(2*N+1)+3 by omega,anisotropicFinitePotential_grid_eq_uniform,
    anisotropicFinitePotential_grid_eq_uniform]
  simpa only [show 2*N+1+1=2*(N+1) by omega] using gaussianUniformGridCascade_coarse_double μ N
    (anisotropicUnitInput D) (anisotropicGridTerminalPotential D) ‖anisotropicEnergyMap D‖₊
    (anisotropicGridTerminalPotential_lipschitz D)

theorem anisotropicFinitePotential_grid_profile_abs_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (N : ℕ) (P : AnisotropicParameter n) :
    |anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ N) (N+3) P-
      anisotropicFinitePotential D (Paper.parisiGridRSBScheme ν N) (N+3) P| ≤
      anisotropicProfileStabilityConstant D*(Paper.parisiCDFDistance μ ν+2/(N+1 : ℕ)) := by
  have hh := anisotropicFinitePotential_aligned_CDFDistance_abs_sub_le D
    (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) (fun _ _ => rfl) P
  rw [FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (parisiCDFDistance_grid_pair_le μ ν N)
    (anisotropicProfileStabilityConstant_nonneg D))

theorem anisotropicFinitePotential_grid_adjacent_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (P : AnisotropicParameter n) :
    |anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ (2*N+1)) (2*N+4) P-
      anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ N) (N+3) P| ≤
      2*anisotropicProfileStabilityConstant D/(N+1 : ℕ) := by
  have hh := anisotropicFinitePotential_grid_profile_abs_sub_le D μ (Paper.parisiGridMeasure μ N) (2*N+1) P
  rw [anisotropicFinitePotential_grid_refine_coarse D μ N] at hh
  have he : anisotropicProfileStabilityConstant D*(1/(N+1 : ℕ)+2/(2*N+1+1 : ℕ))=
      2*anisotropicProfileStabilityConstant D/(N+1 : ℕ) := by push_cast;field_simp;ring
  exact hh.trans (he ▸ mul_le_mul_of_nonneg_left
    (add_le_add (Paper.parisiCDFDistance_grid_le μ N) le_rfl) (anisotropicProfileStabilityConstant_nonneg D))

end QuantitativeFollowup
