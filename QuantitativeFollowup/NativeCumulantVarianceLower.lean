module
public import QuantitativeFollowup.NativeCenteredCumulantTail
public import QuantitativePaper.SixthWindowEnergy
public import QuantitativePaper.UniformEnergyVarianceLower

@[expose] public section

/-! Genuine finite-SK variance lower bounds forced by a centered cumulant
larger than one, including the exact small-tilt contradiction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

theorem centeredEnergyCGF_eq_shifted (n : ℕ) (hn : 0<n) (β lam : ℝ) :
    centeredEnergyCGF n β lam=scalarCenteredEnergyLogMoment n β lam+
      (n:ℝ)*lam*energyMeanDeficit n β := by
  have hh:=FourPapersCommon.cgf_add_constant (couplingLaw n) (energyFreeEnergy n β)
    lam (-(∫g,energyFreeEnergy n β g ∂couplingLaw n))
    (integrable_exp_energyFreeEnergy n β lam)
  rw [scalarCenteredEnergyLogMoment_eq]
  unfold centeredEnergyCGF energyMeanDeficit
  have hnR : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  convert hh using 1 <;> (try ring)
  field_simp
  <;> ring

theorem scalarCenteredEnergyLogMoment_le_centered (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (lam : ℝ) (hlam : 0≤lam) :
    scalarCenteredEnergyLogMoment n β lam≤centeredEnergyCGF n β lam := by
  rw [centeredEnergyCGF_eq_shifted n hn]
  exact le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg n) hlam) (energyMeanDeficit_nonneg n hn β hβ))

theorem native_centered_cumulant_le_one_on_radius (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (lam : ℝ) (hlam : 0≤lam)
    (hSmall : lam*varianceTailScale n β≤nativeCumulantRadius) :
    centeredEnergyCGF n β lam≤1 := by
  have hBound:=native_centered_cumulant_tail_bound n hn β hβ lam hlam hSmall
  have hD:=varianceTailScale_pos n β hβ
  have hB:=nativeCumulantConstants.1
  have hb:=nativeCumulantConstants.2.1
  have hs : (lam*varianceTailScale n β)^2≤nativeCumulantRadius^2:=by
    nlinarith [mul_nonneg hlam hD.le]
  have hh:=mul_le_mul_of_nonneg_left hs hB.le
  rw [nativeCumulantConstants.2.2] at hh
  have he : nativeCumulantCoefficient*lam^2*
      (variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2)=
      nativeCumulantCoefficient*(lam*varianceTailScale n β)^2:=by
    rw [mul_pow,varianceTailScale_sq]
    ring
  exact hBound.trans (by rwa [he])

theorem native_energy_variance_lower_at_large_cumulant (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (lam : ℝ) (hlam : 0<lam)
    (hLarge : 1<scalarCenteredEnergyLogMoment n β lam) :
    nativeCumulantRadius^2/lam^2<
      variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2 := by
  have hMean:=(hLarge.trans_le
    (scalarCenteredEnergyLogMoment_le_centered n hn β hβ lam hlam.le))
  have hNot : nativeCumulantRadius<lam*varianceTailScale n β:=by
    by_contra hh
    exact (not_lt_of_ge (native_centered_cumulant_le_one_on_radius n hn β hβ lam
      hlam.le (le_of_not_gt hh))) hMean
  have hb:=nativeCumulantConstants.2.1
  have hs : nativeCumulantRadius^2<(lam*varianceTailScale n β)^2:=by
    nlinarith
  rw [mul_pow,varianceTailScale_sq] at hs
  apply (div_lt_iff₀ (sq_pos_of_pos hlam)).mpr
  nlinarith only [hs]

end QuantitativeFollowup
