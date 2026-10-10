module
public import QuantitativeFollowup.NativeCenteredEnergyMomentBounds

@[expose] public section

/-! The actual positive centered cumulant is bounded by a normalized-CGF
secant at any positive endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem native_centered_energy_cgf_positive_secant (n : ℕ) (β : ℝ) (hβ : 0<β)
    (s r : ℝ) (hs : 0<s) (hr : 0<r) (hsr : s≤r) :
    centeredEnergyCGF n β s≤(s/r)^2*centeredEnergyCGF n β r := by
  have hw0 : 0≤1-s/r:=by have hh:=(div_le_one hr).mpr hsr;linarith
  have hw1 : 0≤ s/r:=div_nonneg hs.le hr.le
  have hc:=(convexOn_normalizedEnergyMoment n β hβ).2 (mem_univ 0) (mem_univ r)
    hw0 hw1 (show (1-s/r)+s/r=1 by ring)
  have he : (1-s/r)*(0:ℝ)+(s/r)*r=s:=by field_simp <;> ring
  simp only [smul_eq_mul,he,normalizedEnergyMoment_zero] at hc
  calc
    centeredEnergyCGF n β s=s*(normalizedEnergyMoment n β s-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)):=centeredEnergyCGF_eq_normalized n β s hs.ne'
    _≤ s*(((1-s/r)*(∫g,energyFreeEnergy n β g ∂couplingLaw n)+
      (s/r)*normalizedEnergyMoment n β r)-(∫g,energyFreeEnergy n β g ∂couplingLaw n)):=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hc _) hs.le
    _=(s/r)^2*centeredEnergyCGF n β r:=by
      rw [centeredEnergyCGF_eq_normalized n β r hr.ne']
      field_simp
      <;> ring

end QuantitativeFollowup
