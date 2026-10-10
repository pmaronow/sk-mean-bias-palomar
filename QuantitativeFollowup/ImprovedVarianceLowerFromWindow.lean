module
public import QuantitativeFollowup.NativeCumulantVarianceLower
public import QuantitativeFollowup.ImprovedWindowScalePowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! A true sixth-power cumulant window forces the improved native 7/25
variance lower power; the inverse-temperature correction is removed only
after a proved size threshold. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_energy_variance_lower_of_sixth_window (β : ℝ) (hβ : 0<β)
    (a A L : ℝ) (ha : 0<a) (hA : 0<A) (hL : 0<L) (Nwin : ℕ)
    (hWindow : ∀n : ℕ,Nwin≤n → ∀lam : ℝ,A*(n:ℝ)^(-(7/50:ℝ))≤lam → lam≤L →
      a*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam) :
    ∃cv : ℝ,∃N0 : ℕ,0<cv ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      cv*(n:ℝ)^(7/25:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) := by
  let cv:=nativeCumulantRadius^2/(2*A^2)
  have hb:=nativeCumulantConstants.2.1
  have hcv : 0<cv:=by dsimp only [cv];positivity
  have hSmall : ∀ᶠn : ℕ in atTop,A*(n:ℝ)^(-(7/50:ℝ))≤L:=by
    have hh:=((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/50)).comp
      tendsto_natCast_atTop_atTop).const_mul A
    exact (show Tendsto (fun n : ℕ=>A*(n:ℝ)^(-(7/50:ℝ))) atTop (𝓝 0) by
      simpa using hh).eventually_le_const hL
  have hLarge : ∀ᶠn : ℕ in atTop,1<a*A^6*(n:ℝ)^(4/25:ℝ):=by
    have hh:=((tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/25)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (mul_pos ha (pow_pos hA 6))
    exact hh.eventually_gt_atTop 1
  have hCorrection : ∀ᶠn : ℕ in atTop,β⁻¹^2≤cv*(n:ℝ)^(7/25:ℝ):=by
    exact (((tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/25)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop hcv).eventually_ge_atTop _
  obtain ⟨Nt,hNt⟩:=eventually_atTop.1 ((hSmall.and hLarge).and hCorrection)
  let N0:=max 2 (max Nwin Nt)
  refine ⟨cv,N0,hcv,le_max_left _ _,?_⟩
  intro n hn
  have hn2 : 2≤n:=(le_max_left _ _).trans hn
  have hn0 : 0<n:=by omega
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  have hnWin : Nwin≤n:=(le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnT : Nt≤n:=(le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hAll:=hNt n hnT
  let lam:=A*(n:ℝ)^(-(7/50:ℝ))
  have hlam : 0<lam:=mul_pos hA (Real.rpow_pos_of_pos hNp _)
  have hNative : 1<scalarCenteredEnergyLogMoment n β lam:=by
    have hh:=hWindow n hnWin lam le_rfl hAll.1.1
    have he : a*(n:ℝ)*lam^6=a*A^6*(n:ℝ)^(4/25:ℝ):=by
      dsimp only [lam]
      rw [mul_assoc,improved_window_sixth_size (n:ℝ) A hNp]
      ring
    rw [he] at hh
    exact hAll.1.2.trans_le hh
  have hVar:=native_energy_variance_lower_at_large_cumulant n hn0 β hβ lam hlam hNative
  rw [show nativeCumulantRadius^2/lam^2=
      (nativeCumulantRadius^2/A^2)*(n:ℝ)^(7/25:ℝ) from
      improved_window_inverse_square (n:ℝ) A nativeCumulantRadius hNp hA] at hVar
  have he : nativeCumulantRadius^2/A^2=2*cv:=by dsimp only [cv];ring
  rw [he] at hVar
  nlinarith only [hVar,hAll.2]

end QuantitativeFollowup
