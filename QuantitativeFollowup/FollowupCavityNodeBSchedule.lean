module
public import QuantitativeFollowup.FollowupCavityNodeBModel

@[expose] public section

/-! The literal threefold covariance schedule for changing exactly one
anisotropic auxiliary variance. The two rest-field copies cancel their time
responses; the last coordinate changes by the prescribed positive scale. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def cavityNodeBScheduleMass (s : RSBScheme k) (j : ℕ) : ℝ :=
  anisotropicSchemeMass s (j/3)

def cavityNodeBScheduleUp (j : ℕ) : Bool := decide (j%3≠0)

def cavityNodeBScheduleDirection (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M : ℝ) (j : ℕ) : Field n→L[ℝ]FiniteStateField (Configuration n) :=
  if j%3=2 then cavityCoordinateEnergyInput s i (j/3) M else cavityRestEnergyInput D s i (j/3)

def cavityNodeBCurrentInput (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) : Field n→L[ℝ]FiniteStateField (Configuration n) :=
  finiteStateScheduleScale (cavityNodeBScheduleUp j) t • cavityNodeBScheduleDirection D s i M j

theorem cavityNodeBScheduleMass_nonneg (s : RSBScheme k) (j : ℕ) :
    0 ≤ cavityNodeBScheduleMass s j := anisotropicSchemeMass_nonneg s _

@[simp] theorem cavityNodeBScheduleMass_three (s : RSBScheme k) (j : ℕ) :
    cavityNodeBScheduleMass s (3*j)=anisotropicSchemeMass s j := by
  simp [cavityNodeBScheduleMass,Nat.mul_comm]

@[simp] theorem cavityNodeBScheduleMass_three_one (s : RSBScheme k) (j : ℕ) :
    cavityNodeBScheduleMass s (3*j+1)=anisotropicSchemeMass s j := by
  simp [cavityNodeBScheduleMass,Nat.mul_comm,Nat.add_div]

@[simp] theorem cavityNodeBScheduleMass_three_two (s : RSBScheme k) (j : ℕ) :
    cavityNodeBScheduleMass s (3*j+2)=anisotropicSchemeMass s j := by
  simp [cavityNodeBScheduleMass,Nat.mul_comm,Nat.add_div]

@[simp] theorem cavityNodeBCurrentInput_three (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) :
    cavityNodeBCurrentInput D s i M t (3*j)=Real.sqrt (1-t) • cavityRestEnergyInput D s i j := by
  simp [cavityNodeBCurrentInput,cavityNodeBScheduleUp,cavityNodeBScheduleDirection,
    finiteStateScheduleScale,Nat.mul_comm]

@[simp] theorem cavityNodeBCurrentInput_three_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) :
    cavityNodeBCurrentInput D s i M t (3*j+1)=Real.sqrt t • cavityRestEnergyInput D s i j := by
  simp [cavityNodeBCurrentInput,cavityNodeBScheduleUp,cavityNodeBScheduleDirection,
    finiteStateScheduleScale,Nat.mul_comm,Nat.add_mod,Nat.add_div]

@[simp] theorem cavityNodeBCurrentInput_three_two (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) :
    cavityNodeBCurrentInput D s i M t (3*j+2)=Real.sqrt t • cavityCoordinateEnergyInput s i j M := by
  simp [cavityNodeBCurrentInput,cavityNodeBScheduleUp,cavityNodeBScheduleDirection,
    finiteStateScheduleScale,Nat.mul_comm,Nat.add_mod,Nat.add_div]

private theorem spectral_smul (r : ℝ) (L : Field n→L[ℝ]FiniteStateField (Configuration n))
    (σ τ : Configuration n) :
    finiteStateSpectralCovariance (r • L) σ τ=r^2*finiteStateSpectralCovariance L σ τ := by
  simp only [finiteStateSpectralCovariance,ContinuousLinearMap.smul_apply,PiLp.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem cavityNodeBCurrentInput_rest_covariance (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (ht : t∈Icc 0 1) (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ=
      finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j)) σ τ+
        finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j+1)) σ τ := by
  rw [cavityNodeBCurrentInput_three,cavityNodeBCurrentInput_three_one,
    spectral_smul,spectral_smul,Real.sq_sqrt (by linarith [ht.2]),Real.sq_sqrt ht.1]
  ring

theorem cavityNodeBCurrentInput_coordinate (s : RSBScheme k) (i : Fin n)
    (M t : ℝ) (ht : 0≤t) (j : ℕ) :
    Real.sqrt t • cavityCoordinateEnergyInput s i j M=cavityCoordinateEnergyInput s i j (M*t) := by
  unfold cavityCoordinateEnergyInput
  rw [smul_smul,←Real.sqrt_mul ht]
  congr 1
  congr 1
  ring

theorem cavityNodeBCurrentInput_combined_covariance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1)
    (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityFiniteEnergyInput (anisotropicReplaceVariance D i (M*t)) s j) σ τ=
      finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ+
        finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j+2)) σ τ := by
  rw [cavityNodeBCurrentInput_three_two,cavityNodeBCurrentInput_coordinate s i M t ht.1.le]
  exact cavityReplaceVariance_spectral_split D s i j (M*t) (mul_pos hM ht.1) σ τ

/-- Genuine analytic time derivative of the actual covariance schedule;
only the changing coordinate contributes to the normalized response. -/
theorem hasDerivAt_cavityNodeBSchedule (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (ht : t∈Ioo 0 1) (J : ℕ)
    (H : FiniteStateField (Configuration n)) :
    HasDerivAt (fun u=>finiteStateGaussianScheduledTerminalCascade
      (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
      (cavityNodeBScheduleDirection D s i M) cavityNodeBScheduleUp (3*J) u H)
      ((1/2 : ℝ)*∑j∈Finset.range J,finiteStateCascadeCovarianceResponse
        (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
        (cavityNodeBCurrentInput D s i M t) (3*j+2) (3*J-(3*j+2)) H
        (cavityCoordinateEnergyInput s i j M)) t := by
  have hd:=hasDerivAt_finiteStateGaussianScheduledTerminal_time
    (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s) (cavityNodeBScheduleMass_nonneg s)
    (cavityNodeBScheduleDirection D s i M) cavityNodeBScheduleUp (3*J) t ht H
  rw [finiteStateGaussianScheduledTerminal_time_threefold
    (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s) (cavityNodeBScheduleMass_nonneg s)
    (cavityNodeBScheduleDirection D s i M) cavityNodeBScheduleUp J
    (fun j _=>by simp [cavityNodeBScheduleUp,Nat.mul_comm,Nat.add_mod])
    (fun j _=>by simp) (fun j _=>by simp [cavityNodeBScheduleDirection,Nat.mul_comm,Nat.add_mod,Nat.add_div])
    t ht H] at hd
  have hdir (j : ℕ) : cavityNodeBScheduleDirection D s i M (3*j+2)=
      cavityCoordinateEnergyInput s i j M := by
    simp [cavityNodeBScheduleDirection,Nat.mul_comm,Nat.add_mod,Nat.add_div]
  simp_rw [hdir] at hd
  exact hd

end QuantitativeFollowup
