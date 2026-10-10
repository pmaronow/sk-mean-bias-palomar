module
public import QuantitativePaper.Model
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Exact independent-Gaussian completion formulas. In particular, the
lambda/(4N) ground-state correction is retained for all positive tilts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace QuantitativePaper

theorem hasLaw_diagonalNoise (n : ℕ) :
    HasLaw (diagonalNoise n) (gaussianReal 0 (1/2)) (completionLaw n) where
  aemeasurable := measurable_snd.aemeasurable
  map_eq := by
    unfold completionLaw diagonalNoise
    rw [Measure.map_snd_prod]
    simp

theorem diagonalNoise_independent_logPartition (n : ℕ) (β : ℝ) :
    IndepFun (fun p : Couplings n × ℝ => logPartition n β p.1) (diagonalNoise n) (completionLaw n) :=
  indepFun_prod (continuous_logPartition n β).measurable measurable_id

theorem diagonalNoise_independent_groundState (n : ℕ) :
    IndepFun (fun p : Couplings n × ℝ => groundState n p.1) (diagonalNoise n) (completionLaw n) :=
  indepFun_prod (continuous_groundState n).measurable measurable_id

theorem integrable_completedLogPartition (n : ℕ) (β : ℝ) :
    Integrable (completedLogPartition n β) (completionLaw n) := by
  exact ((integrable_logPartition n β).comp_fst _).add
    (((memLp_id_gaussianReal (μ := 0) (v := 1/2) 1).integrable le_rfl).const_mul β |>.comp_snd _)

theorem integrable_completedGroundState (n : ℕ) :
    Integrable (completedGroundState n) (completionLaw n) := by
  exact ((integrable_groundState n).comp_fst _).add
    (((memLp_id_gaussianReal (μ := 0) (v := 1/2) 1).integrable le_rfl).comp_snd _)

theorem integral_completedLogPartition (n : ℕ) (β : ℝ) :
    (∫ p,completedLogPartition n β p ∂completionLaw n) =
      ∫ g,logPartition n β g ∂couplingLaw n := by
  have h1 := (integrable_logPartition n β).comp_fst (gaussianReal 0 (1/2))
  have h2 : Integrable (fun p : Couplings n × ℝ => β*p.2) (completionLaw n) := by
    simpa [id_eq,completionLaw] using
      ((((memLp_id_gaussianReal (μ := 0) (v := 1/2) 1).integrable le_rfl).const_mul β).comp_snd (couplingLaw n))
  have hadd := integral_add h1 h2
  unfold completedLogPartition completionLaw
  rw [hadd,integral_fun_fst (logPartition n β),integral_fun_snd (fun x : ℝ => β*x),
    integral_const_mul,integral_id_gaussianReal]
  simp

theorem integral_completedGroundState (n : ℕ) :
    (∫ p,completedGroundState n p ∂completionLaw n) = ∫ g,groundState n g ∂couplingLaw n := by
  have h1 := (integrable_groundState n).comp_fst (gaussianReal 0 (1/2))
  have h2 : Integrable (fun p : Couplings n × ℝ => p.2) (completionLaw n) := by
    simpa [id_eq,completionLaw] using
      (((memLp_id_gaussianReal (μ := 0) (v := 1/2) 1).integrable le_rfl).comp_snd (couplingLaw n))
  have hadd := integral_add h1 h2
  unfold completedGroundState completionLaw
  rw [hadd,integral_fun_fst (groundState n),integral_fun_snd (fun x : ℝ => x),integral_id_gaussianReal]
  simp

theorem variance_completedLogPartition (n : ℕ) (β : ℝ) :
    variance (completedLogPartition n β) (completionLaw n) = freeEnergyVariance n β+β^2/2 := by
  have h2 : MemLp (fun x : ℝ => β*x) 2 (gaussianReal 0 (1/2)) := by
    simpa [id_eq,completionLaw] using (memLp_id_gaussianReal (μ := 0) (v := 1/2) 2).const_mul β
  have hh := variance_add_prod (memLp_two_logPartition n β) h2
  change variance (completedLogPartition n β) (completionLaw n) = _ at hh
  rw [hh]
  unfold freeEnergyVariance
  rw [variance_const_mul,variance_fun_id_gaussianReal]
  norm_num
  ring

theorem variance_completedGroundState (n : ℕ) :
    variance (completedGroundState n) (completionLaw n) = groundStateVariance n+1/2 := by
  have h2 : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 (1/2)) := by
    exact MemLp.ae_eq (Eventually.of_forall fun x => rfl)
      (memLp_id_gaussianReal' (μ := 0) (v := 1/2) (p := 2) (by norm_num))
  have hh := variance_add_prod (memLp_two_groundState n) h2
  change variance (completedGroundState n) (completionLaw n) = _ at hh
  rw [hh]
  unfold groundStateVariance
  rw [variance_fun_id_gaussianReal]
  norm_num

theorem integrable_exp_completedLogPartition (n : ℕ) (β a : ℝ) :
    Integrable (fun p => Real.exp (a*completedLogPartition n β p)) (completionLaw n) := by
  have hi := (integrable_exp_logPartition n β a).mul_prod
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1/2) (a*β))
  convert hi using 1
  · funext p
    rw [completedLogPartition,mul_add,Real.exp_add]
    congr 1
    ring
  · rfl

theorem integrable_exp_completedGroundState (n : ℕ) (a : ℝ) :
    Integrable (fun p => Real.exp (a*completedGroundState n p)) (completionLaw n) := by
  have hi := (integrable_exp_groundState n a).mul_prod
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1/2) a)
  convert hi using 1
  · funext p
    rw [completedGroundState,mul_add,Real.exp_add]
  · rfl

theorem mgf_completedLogPartition (n : ℕ) (β a : ℝ) :
    mgf (completedLogPartition n β) (completionLaw n) a =
      mgf (logPartition n β) (couplingLaw n) a*Real.exp (β^2*a^2/4) := by
  unfold mgf completedLogPartition completionLaw
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun g => Real.exp (a*logPartition n β g))
    (fun d : ℝ => Real.exp (a*(β*d)))]
  have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1/2)) (a*β)
  simp only [mgf,zero_mul,zero_add] at hg
  have hgauss : (∫ d,Real.exp (a*(β*d)) ∂gaussianReal 0 (1/2)) = Real.exp (β^2*a^2/4) := by
    convert hg using 1
    · apply integral_congr_ae
      exact .of_forall fun d => by ring_nf
    · norm_num
      ring
  rw [hgauss]

theorem mgf_completedGroundState (n : ℕ) (a : ℝ) :
    mgf (completedGroundState n) (completionLaw n) a =
      mgf (groundState n) (couplingLaw n) a*Real.exp (a^2/4) := by
  unfold mgf completedGroundState completionLaw
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun g => Real.exp (a*groundState n g))
    (fun d : ℝ => Real.exp (a*d))]
  have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1/2)) a
  simp only [mgf,zero_mul,zero_add] at hg
  rw [hg]
  congr 2
  norm_num
  ring

theorem cgf_completedLogPartition (n : ℕ) (β a : ℝ) :
    cgf (completedLogPartition n β) (completionLaw n) a =
      cgf (logPartition n β) (couplingLaw n) a+β^2*a^2/4 := by
  unfold cgf
  rw [mgf_completedLogPartition,Real.log_mul
    (mgf_pos (integrable_exp_logPartition n β a)).ne' (Real.exp_ne_zero _),Real.log_exp]

theorem cgf_completedGroundState (n : ℕ) (a : ℝ) :
    cgf (completedGroundState n) (completionLaw n) a =
      cgf (groundState n) (couplingLaw n) a+a^2/4 := by
  unfold cgf
  rw [mgf_completedGroundState,Real.log_mul
    (mgf_pos (integrable_exp_groundState n a)).ne' (Real.exp_ne_zero _),Real.log_exp]

theorem centeredCGF_eq (n : ℕ) (β a : ℝ) :
    centeredCGF n β a = cgf (logPartition n β) (couplingLaw n) a-
      a*(∫ g,logPartition n β g ∂couplingLaw n) := by
  unfold centeredCGF cgf
  have heq : (fun g => logPartition n β g-∫ z,logPartition n β z ∂couplingLaw n) =
      fun g => logPartition n β g+(-(∫ z,logPartition n β z ∂couplingLaw n)) := by
    funext g
    ring
  rw [heq,mgf_add_const,Real.log_mul
    (mgf_pos (integrable_exp_logPartition n β a)).ne' (Real.exp_ne_zero _),Real.log_exp]
  ring

/-- The exact finite-N completion decomposition from the introduction. -/
theorem completedFractionalPressure_eq (n : ℕ) (hn : 0 < n) (β a : ℝ) (ha : a ≠ 0) :
    completedFractionalPressure n β a = pressure n β+
      centeredCGF n β a/((n : ℝ)*a)+β^2*a/(4*(n : ℝ)) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold completedFractionalPressure
  rw [ite_eq_right ha,cgf_completedLogPartition,centeredCGF_eq]
  unfold pressure
  field_simp
  ring

/-- Removing the independent common Gaussian contributes exactly lambda/(4N). -/
theorem completedGroundLaplace_eq (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : a ≠ 0) :
    completedGroundLaplace n a = cgf (groundState n) (couplingLaw n) a/((n : ℝ)*a)+
      a/(4*(n : ℝ)) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold completedGroundLaplace
  rw [ite_eq_right ha,cgf_completedGroundState]
  field_simp [hnr,ha]

end QuantitativePaper
