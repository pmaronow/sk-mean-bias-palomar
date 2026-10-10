module
public import QuantitativeFollowup.SixthWindowFromBudget
public import QuantitativeFollowup.ImprovedSixthWindowConstants
public import QuantitativePaper.MainFluctuationTargets

@[expose] public section

/-! The improved genuine sixth window is instantiated in the actual
finite SK law, and transferred to the original free-energy normalization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_energy_matching_tails_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Ax xstar cx Cx : ℝ,∃N0 : ℕ,
      0<Ax ∧ 0<xstar ∧ 0<cx ∧ 0<Cx ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      ∀x : ℝ,Ax*(n:ℝ)^(-(7/10:ℝ))≤x → x≤xstar →
        Real.exp (-Cx*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g}≤
          Real.exp (-cx*(n:ℝ)*x^(6/5:ℝ)) := by
  obtain ⟨a,Ls,A,L,Nw,ha,hLs,hA,hL,_,_,hNw,hUpper,hLower⟩:=
    improved_sixth_window_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  let Cs:=max Ls a
  have hCs : 0<Cs:=(zero_lt_one.trans_le hLs).trans_le (le_max_left _ _)
  have hAp : 0<A:=zero_lt_one.trans_le hA
  obtain ⟨Nt,Ax,xstar,cx,Cx,hAx,hxs,hcx,hCx,hConvert⟩:=
    improved_sixth_window_uniform_constants a Cs A L ha hCs (le_max_right _ _) hAp hL
  let N0:=max Nw Nt
  refine ⟨Ax,xstar,cx,Cx,N0,hAx,hxs,hcx,hCx,hNw.trans (le_max_left _ _),?_⟩
  intro n hn x hxLow hxHigh
  have hnw : Nw≤n:=(le_max_left _ _).trans hn
  have hnt : Nt≤n:=(le_max_right _ _).trans hn
  have hn2 : 2≤n:=hNw.trans hnw
  have hn0 : 0<n:=by omega
  have hXm : Measurable (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0):=
    (((continuous_logPartition n β).div_const β).sub continuous_const).measurable
  have hNativeUpper (s : ℝ) (hs : 0<s) (hu : s≤L) :
      scalarCenteredEnergyLogMoment n β s≤Cs*(n:ℝ)*s^6:=
    (hUpper n hn2 s ⟨hs,hu⟩).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg n)) (pow_nonneg hs.le _))
  have hh:=hConvert n hnt (Couplings n) (couplingLaw n)
    (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0) hXm
    (fun s _ _=>integrable_exp_scalarCenteredEnergy n β s) hNativeUpper
    (hLower n hnw) x hxLow hxHigh
  have he : {g | (n:ℝ)*x≤energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0}=
      {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g}:=by
    ext g
    simp only [mem_setOf_eq]
    constructor <;> intro hg <;> nlinarith
  simpa only [he] using hh

theorem improved_native_matching_tails_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Ao xo co Co : ℝ,∃N0 : ℕ,
      0<Ao ∧ 0<xo ∧ 0<co ∧ 0<Co ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      ∀x : ℝ,Ao*(n:ℝ)^(-(7/10:ℝ))≤x → x≤xo →
        Real.exp (-Co*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(Paper.parisiPDEValue β 0+x)≤logPartition n β g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(Paper.parisiPDEValue β 0+x)≤logPartition n β g}≤
          Real.exp (-co*(n:ℝ)*x^(6/5:ℝ)) := by
  obtain ⟨A,xstar,c,Ct,N0,hA,hxs,hc,hCt,hN0,hEnergy⟩:=
    improved_energy_matching_tails_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨β*A,β*xstar,c/β^(6/5:ℝ),Ct/β^(6/5:ℝ),N0,
    by positivity,by positivity,by positivity,by positivity,hN0,?_⟩
  intro n hn x hxlo hxhi
  have hxlow : A*(n:ℝ)^(-(7/10:ℝ))≤x/β:=by
    apply (le_div_iff₀ hβp).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hxlo
  have hxhigh : x/β≤xstar:=(div_le_iff₀ hβp).mpr (by simpa only [mul_comm] using hxhi)
  have hh:=hEnergy n hn (x/β) hxlow hxhigh
  have hn0 : 0<n:=by omega
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  have hx : 0<x:=(by positivity : 0<β*A*(n:ℝ)^(-(7/10:ℝ))).trans_le hxlo
  rw [original_free_energy_tail_eq_energy_tail n β x hβp]
  convert hh using 1 <;> congr 1 <;> rw [Real.div_rpow hx.le hβp.le] <;> ring

end QuantitativeFollowup
