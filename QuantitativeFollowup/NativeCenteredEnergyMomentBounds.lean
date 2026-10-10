module
public import QuantitativeFollowup.NativeCenteredCumulantTail
public import QuantitativeFollowup.ChenSK
public import FourPapersCommon.LogMGFUniformComparison

@[expose] public section

/-! Genuine mean-centered SK moment identities and the variance-sensitive
negative moment inequality obtained from actual Chen convexity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem integrable_exp_meanCenteredEnergy (n : ℕ) (β s : ℝ) :
    Integrable (fun g=>Real.exp (s*(energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)))) (couplingLaw n) := by
  simp_rw [mul_sub,Real.exp_sub,div_eq_mul_inv]
  exact (integrable_exp_energyFreeEnergy n β s).mul_const _

theorem centeredEnergyCGF_eq_cgf_sub_mean (n : ℕ) (β s : ℝ) :
    centeredEnergyCGF n β s=cgf (energyFreeEnergy n β) (couplingLaw n) s-
      s*(∫g,energyFreeEnergy n β g ∂couplingLaw n) := by
  have hh:=cgf_add_constant (couplingLaw n) (energyFreeEnergy n β) s
    (-(∫g,energyFreeEnergy n β g ∂couplingLaw n)) (integrable_exp_energyFreeEnergy n β s)
  convert hh using 1 <;> (try rfl) <;> ring

theorem centeredEnergyCGF_nonneg (n : ℕ) (β s : ℝ) : 0≤centeredEnergyCGF n β s := by
  let Z : Couplings n → ℝ:=fun g=>energyFreeEnergy n β g-
    (∫g,energyFreeEnergy n β g ∂couplingLaw n)
  have hZi : Integrable Z (couplingLaw n):=
    (integrable_energyFreeEnergy n β).sub (integrable_const _)
  have hCenter : (∫g,Z g ∂couplingLaw n)=0:=by
    rw [show Z=(fun g=>energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)) from rfl,
      integral_sub (integrable_energyFreeEnergy n β) (integrable_const _),integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul,sub_self]
  have hm:=integral_mono ((integrable_const 1).add (hZi.const_mul s))
    (integrable_exp_meanCenteredEnergy n β s)
    (fun g=>by simpa only [Pi.add_apply,add_comm,Z] using Real.add_one_le_exp (s*Z g))
  have he : (∫g,1+s*Z g ∂couplingLaw n)=1:=by
    rw [integral_add (f:=fun _=>1) (g:=fun g=>s*Z g)
      (integrable_const 1) (hZi.const_mul s),integral_const,integral_const_mul,hCenter]
    simp only [probReal_univ,smul_eq_mul,one_mul,mul_zero,add_zero]
  change (∫g,1+s*Z g ∂couplingLaw n)≤_ at hm
  rw [he] at hm
  exact Real.log_nonneg hm

theorem centeredEnergyCGF_eq_normalized (n : ℕ) (β s : ℝ) (hs : s≠0) :
    centeredEnergyCGF n β s=s*(normalizedEnergyMoment n β s-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)) := by
  rw [centeredEnergyCGF_eq_cgf_sub_mean,normalizedEnergyMoment_of_ne n β hs]
  change cgf (energyFreeEnergy n β) (couplingLaw n) s-s*_=
    s*(cgf (energyFreeEnergy n β) (couplingLaw n) s/s-_)
  field_simp
  <;> ring

theorem native_centered_energy_cgf_negative_variance_bound (n : ℕ) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s<0) :
    centeredEnergyCGF n β s≤ s^2/2*variance (energyFreeEnergy n β) (couplingLaw n) := by
  have hd:=hasDerivAt_normalizedEnergyMoment_zero n β
  have hSlope:=(convexOn_normalizedEnergyMoment n β hβ).slope_le_deriv
    (mem_univ s) (mem_univ 0) hs hd.differentiableAt
  rw [hd.deriv] at hSlope
  have hh:=mul_le_mul_of_nonneg_right hSlope (show 0≤-s by linarith)
  have he : slope (normalizedEnergyMoment n β) s 0*(-s)=
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)-normalizedEnergyMoment n β s:=by
    simp only [slope,smul_eq_mul,vsub_eq_sub,zero_sub,normalizedEnergyMoment_zero]
    field_simp [hs.ne]
  rw [he] at hh
  have hTangent : (∫g,energyFreeEnergy n β g ∂couplingLaw n)+
      s*(variance (energyFreeEnergy n β) (couplingLaw n)/2)≤normalizedEnergyMoment n β s:=by
    linarith
  have hMul:=mul_le_mul_of_nonpos_left hTangent hs.le
  rw [centeredEnergyCGF_eq_normalized n β s hs.ne]
  nlinarith only [hMul]

end QuantitativeFollowup
