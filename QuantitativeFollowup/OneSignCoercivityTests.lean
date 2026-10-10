module
public import QuantitativePaper.ResponseLipschitzTest
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Honest nonzero Dirichlet energy, sign pairing, and density control for
arbitrary Lipschitz interior cutoffs. These are deterministic integral facts;
the actual-model response is instantiated in OneSignCoercivity. -/
noncomputable section
open Set MeasureTheory Filter QuantitativePaper
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

theorem oneSignCutoff_energy_integrable (w : ResponseLipschitzTest) :
    IntervalIntegrable (fun q=>(w.slope q)^2) volume 0 1 := by
  simpa only [mul_one] using intervalIntegrable_responseLipschitzSlope_sq_mul w 0 1
    (fun _=>(1:ℝ)) intervalIntegrable_const

theorem oneSignCutoff_energy_pos (w : ResponseLipschitzTest)
    (hne : ∃x∈Icc (0:ℝ) 1,w.value x≠0) :
    0<(∫q in (0:ℝ)..1,(w.slope q)^2) := by
  have hn : 0≤(∫q in (0:ℝ)..1,(w.slope q)^2):=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _=>sq_nonneg _)
  by_contra hnp
  have hz : (∫q in (0:ℝ)..1,(w.slope q)^2)=0:=le_antisymm (le_of_not_gt hnp) hn
  have hae:=(intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (.of_forall fun q=>sq_nonneg (w.slope q)) (oneSignCutoff_energy_integrable w)).mp hz
  have hd : w.slope=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun _=>0) := by
    filter_upwards [hae] with q hq
    exact sq_eq_zero_iff.mp hq
  obtain ⟨x,hx,hne⟩:=hne
  have hdx := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hx.2) hd
  have hI : (∫q in (0:ℝ)..x,deriv w.value q)=0 := by
    rw [intervalIntegral.integral_of_le hx.1]
    simpa only [integral_zero,ResponseLipschitzTest.slope] using integral_congr_ae hdx
  rw [(w.absolutelyContinuous 0 x).integral_deriv_eq_sub,w.zero_left,sub_zero] at hI
  exact hne hI

theorem oneSignCutoff_signed_pairing (I : Set ℝ) (φ ζ ψ : ℝ→ℝ)
    (hφ : Continuous φ) (hζ : Continuous ζ) (hψ : IntervalIntegrable ψ volume 0 1)
    (hφ0 : ∀q,0≤φ q) (hζ0 : ∀q,0≤ζ q)
    (hoff : ∀q∉I,φ q=0) (A σ : ℝ) (hσ : |σ|=1)
    (hsign : ∀q∈I,A/2≤σ*ψ q) :
    A/2*(∫q in (0:ℝ)..1,ζ q*φ q)≤
      |∫q in (0:ℝ)..1,ψ q*ζ q*φ q| := by
  have hi : IntervalIntegrable (fun q=>ψ q*ζ q*φ q) volume 0 1 := by
    convert (hψ.continuousOn_mul hζ.continuousOn).continuousOn_mul hφ.continuousOn using 1
    funext q
    ring
  have hp : ∀q∈Icc (0:ℝ) 1,(A/2)*(ζ q*φ q)≤σ*(ψ q*ζ q*φ q) := by
    intro q _
    by_cases hq : q∈I
    · have hh:=mul_le_mul_of_nonneg_right (hsign q hq) (mul_nonneg (hζ0 q) (hφ0 q))
      convert hh using 1 <;> ring
    · rw [hoff q hq]
      simp
  have hh:=intervalIntegral.integral_mono_on zero_le_one
    (((hζ.mul hφ).intervalIntegrable (μ:=volume) 0 1).const_mul (A/2)) (hi.const_mul σ) hp
  simp only [intervalIntegral.integral_const_mul] at hh
  refine hh.trans ?_
  calc
    σ*(∫q in (0:ℝ)..1,ψ q*ζ q*φ q)≤|σ*(∫q in (0:ℝ)..1,ψ q*ζ q*φ q)|:=le_abs_self _
    _=|∫q in (0:ℝ)..1,ψ q*ζ q*φ q|:=by rw [abs_mul,hσ,one_mul]

theorem oneSignCutoff_density_bound (I : Set ℝ) (hI : I⊆Ioo (0:ℝ) 1)
    (φ ζ : ℝ→ℝ) (hφ : Continuous φ) (hζ : Continuous ζ)
    (hφ01 : ∀q,φ q∈Icc (0:ℝ) 1) (hζ0 : ∀q,0≤ζ q)
    (hoff : ∀q∉I,φ q=0) (η : Measure ℝ) (d : ℝ) (hd : 0≤d)
    (hdensity : η.restrict I≤ENNReal.ofReal d • volume) :
    (∫q : ℝ,(φ q)^2*ζ q∂η)≤d*(∫q in (0:ℝ)..1,ζ q*φ q) := by
  have hsupport : Function.support φ⊆Icc (0:ℝ) 1 := by
    intro q hq
    have hqi : q∈I := by by_contra h;exact hq (hoff q h)
    exact ⟨(hI hqi).1.le,(hI hqi).2.le⟩
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  have hiφ : Integrable (fun q=>ζ q*φ q) volume :=
    (hζ.mul hφ).integrable_of_hasCompactSupport hc.mul_left
  have hcsq : HasCompactSupport (fun q=>(φ q)^2) := by
    have hh : HasCompactSupport (fun q=>φ q*φ q):=hc.mul_right
    simpa only [pow_two] using hh
  have hisq : Integrable (fun q=>(φ q)^2*ζ q) volume :=
    ((hφ.pow 2).mul hζ).integrable_of_hasCompactSupport hcsq.mul_right
  have heq : (∫q in I,(φ q)^2*ζ q∂η)=(∫q : ℝ,(φ q)^2*ζ q∂η) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    rw [hoff q hq]
    simp
  rw [←heq]
  have hm:=integral_mono_measure hdensity
    (.of_forall fun q=>mul_nonneg (sq_nonneg (φ q)) (hζ0 q))
    (hisq.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hd,smul_eq_mul] at hm
  have hs : (∫q : ℝ,(φ q)^2*ζ q)≤(∫q : ℝ,ζ q*φ q) := by
    apply integral_mono hisq hiφ
    intro q
    change (φ q)^2*ζ q≤ζ q*φ q
    have hs : (φ q)^2≤φ q := by nlinarith [(hφ01 q).1,(hφ01 q).2]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs (hζ0 q)
  have hfull : (∫q in (0:ℝ)..1,ζ q*φ q)=(∫q : ℝ,ζ q*φ q) := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro q hq
    by_contra hn
    have ho : q∉I := fun h=>hn ⟨(hI h).1,(hI h).2.le⟩
    apply hq
    change ζ q*φ q=0
    rw [hoff q ho,mul_zero]
  rw [hfull]
  exact hm.trans (mul_le_mul_of_nonneg_left hs hd)

end QuantitativeFollowup
