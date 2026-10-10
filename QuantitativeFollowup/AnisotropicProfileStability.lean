module
public import QuantitativeFollowup.AnisotropicFiniteSmooth
public import QuantitativeFollowup.GaussianShiftMassStability
public import QuantitativePaper.VectorProfileCDFStability

@[expose] public section

/-! Genuine profile stability for anisotropic finite Gaussian recursions.
Every error coefficient is an actual variance increment; the final bound
depends on the model and coefficient L1 distance, not the profile depth. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicProfileStabilityConstant (D : AnisotropicSpinModel n) : ℝ :=
  ‖anisotropicEnergyMap D‖^2 * ‖(anisotropicFieldInjection n).comp (anisotropicNoiseMap D)‖^2

theorem anisotropicProfileStabilityConstant_nonneg (D : AnisotropicSpinModel n) :
    0 ≤ anisotropicProfileStabilityConstant D := mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem anisotropicSchemeInput_norm_sq (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    ‖anisotropicSchemeInput D s j‖^2=(s.q (k+2-j)-s.q (k+1-j))*
      ‖(anisotropicFieldInjection n).comp (anisotropicNoiseMap D)‖^2 := by
  have hd : 0 ≤ s.q (k+2-j)-s.q (k+1-j) :=
    sub_nonneg.mpr (s.q_mono' _ (Nat.sub_le _ _) _ (by omega))
  rw [anisotropicSchemeInput,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hd]

theorem anisotropicFinitePotential_mass_abs_sub_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |gaussianShiftColeHopf (anisotropicSchemeInput D s j) a (anisotropicFinitePotential D s j) P-
      gaussianShiftColeHopf (anisotropicSchemeInput D s j) b (anisotropicFinitePotential D s j) P| ≤
      anisotropicProfileStabilityConstant D*(s.q (k+2-j)-s.q (k+1-j))*|a-b| := by
  have hh := gaussianShiftColeHopf_mass_abs_sub_le (anisotropicFinitePotential D s j)
    ‖anisotropicEnergyMap D‖₊ (anisotropicFinitePotential_lipschitz D s j)
    ((contDiff_anisotropicFinitePotential D s j).of_le (by simp)) (anisotropicSchemeInput D s j) P a b ha hb
  rw [coe_nnnorm,mul_pow,anisotropicSchemeInput_norm_sq] at hh
  convert hh using 1
  unfold anisotropicProfileStabilityConstant
  ring

def anisotropicAlignedProfileError (D : AnisotropicSpinModel n) (s r : RSBScheme k) (j : ℕ) : ℝ :=
  ∑l∈Finset.range j,anisotropicProfileStabilityConstant D*(s.q (k+2-l)-s.q (k+1-l))*
    |s.m (k+1-l)-r.m (k+1-l)|

theorem anisotropicFinitePotential_aligned_profile_abs_sub_le (D : AnisotropicSpinModel n)
    (s r : RSBScheme k) (hq : ∀i,i ≤ k+2 → s.q i=r.q i)
    (j : ℕ) (P : AnisotropicParameter n) :
    |anisotropicFinitePotential D s j P-anisotropicFinitePotential D r j P| ≤
      anisotropicAlignedProfileError D s r j := by
  induction j generalizing P with
  | zero => simp [anisotropicFinitePotential,FourPapersCommon.finiteStateGaussianTerminalCascade,
      FourPapersCommon.finiteStateGaussianCascade,anisotropicAlignedProfileError]
  | succ j ih =>
    have hA : anisotropicSchemeInput D r j=anisotropicSchemeInput D s j := by
      unfold anisotropicSchemeInput
      rw [hq _ (Nat.sub_le _ _),hq _ (by omega)]
    rw [anisotropicFinitePotential_gaussianShiftColeHopf,anisotropicFinitePotential_gaussianShiftColeHopf,hA]
    have hn := gaussianShiftColeHopf_input_abs_sub_le (anisotropicFinitePotential D s j)
      (anisotropicFinitePotential D r j) ‖anisotropicEnergyMap D‖₊
      (anisotropicFinitePotential_lipschitz D s j) (anisotropicFinitePotential_lipschitz D r j)
      (anisotropicSchemeInput D s j) (anisotropicSchemeMass s j) (anisotropicSchemeMass_nonneg s j)
      (anisotropicAlignedProfileError D s r j) ih P
    have hm := anisotropicFinitePotential_mass_abs_sub_le D r j P
      (anisotropicSchemeMass s j) (anisotropicSchemeMass r j)
      (anisotropicSchemeMass_nonneg s j) (anisotropicSchemeMass_nonneg r j)
    rw [hA,←hq _ (Nat.sub_le _ _),←hq _ (by omega)] at hm
    calc
      _ ≤ |gaussianShiftColeHopf (anisotropicSchemeInput D s j) (anisotropicSchemeMass s j)
          (anisotropicFinitePotential D s j) P-gaussianShiftColeHopf (anisotropicSchemeInput D s j)
          (anisotropicSchemeMass s j) (anisotropicFinitePotential D r j) P|+
        |gaussianShiftColeHopf (anisotropicSchemeInput D s j) (anisotropicSchemeMass s j)
          (anisotropicFinitePotential D r j) P-gaussianShiftColeHopf (anisotropicSchemeInput D s j)
          (anisotropicSchemeMass r j) (anisotropicFinitePotential D r j) P| := abs_sub_le _ _ _
      _ ≤ anisotropicAlignedProfileError D s r j+
          anisotropicProfileStabilityConstant D*(s.q (k+2-j)-s.q (k+1-j))*
            |s.m (k+1-j)-r.m (k+1-j)| := add_le_add hn hm
      _ = _ := by simp only [anisotropicAlignedProfileError,Finset.sum_range_succ]

theorem anisotropicAlignedProfileError_eq_CDFDistance (D : AnisotropicSpinModel n)
    (s r : RSBScheme k) (hq : ∀i,i ≤ k+2 → s.q i=r.q i) :
    anisotropicAlignedProfileError D s r (k+2)=anisotropicProfileStabilityConstant D*
      Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  rw [parisiSchemeCDFDistance_eq_sum s r hq,Finset.mul_sum]
  unfold anisotropicAlignedProfileError
  rw [←Finset.sum_range_reflect (fun p => anisotropicProfileStabilityConstant D*
    ((s.q (p+1)-s.q p)*|s.m p-r.m p|)) (k+2)]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have hi : k+2-1-l=k+1-l := by omega
  have hs : k+2-l=k+1-l+1 := by omega
  rw [hi,hs]
  ring

theorem anisotropicFinitePotential_aligned_CDFDistance_abs_sub_le (D : AnisotropicSpinModel n)
    (s r : RSBScheme k) (hq : ∀i,i ≤ k+2 → s.q i=r.q i) (P : AnisotropicParameter n) :
    |anisotropicFinitePotential D s (k+2) P-anisotropicFinitePotential D r (k+2) P| ≤
      anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance
        (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  rw [←anisotropicAlignedProfileError_eq_CDFDistance D s r hq]
  exact anisotropicFinitePotential_aligned_profile_abs_sub_le D s r hq (k+2) P

end QuantitativeFollowup
