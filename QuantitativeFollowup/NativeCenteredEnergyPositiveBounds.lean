module
public import QuantitativeFollowup.NativeCenteredEnergyGaussianBound
public import QuantitativeFollowup.NativeCenteredEnergySecant
public import QuantitativeFollowup.SixthWindowFromBudget
public import QuantitativeFollowup.ImprovedMeanBiasFromBudget
public import QuantitativeFollowup.ImprovedConcentrationScalePowers
public import QuantitativeFollowup.NativeCumulantVarianceLower

@[expose] public section

/-! A genuine all-positive-tilt bound with the improved N^(11/25)
quadratic scale and native sixth-power large-tilt scale. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

theorem improved_centered_energy_positive_cgf_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃K : ℝ,∃N0 : ℕ,0<K ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n → ∀s : ℝ,0<s →
      centeredEnergyCGF n β s≤K*((n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6) := by
  obtain ⟨a,Ls,A,L,Nw,ha,hLs,hA,hL,hL1,hLβ,hNw,hUpper,hLower⟩:=
    improved_sixth_window_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨Cm,hCm,hMean⟩:=improved_energy_mean_bias_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  let K1:=Ls+Cm
  let K:=max K1 (1/(4*L^4))
  have hK1 : 0<K1:=by dsimp only [K1];linarith
  have hK : 0<K:=hK1.trans_le (le_max_left _ _)
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hCut : ∀ᶠn : ℕ in atTop,(n:ℝ)^(-(7/50:ℝ))≤L:=
    ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/50)).comp
      tendsto_natCast_atTop_atTop).eventually_le_const hL
  obtain ⟨Nt,hNt⟩:=eventually_atTop.1 hCut
  let N0:=max 2 Nt
  refine ⟨K,N0,hK,le_max_left _ _,?_⟩
  intro n hn s hs
  have hn2 : 2≤n:=(le_max_left _ _).trans hn
  have hn0 : 0<n:=by omega
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  let r:=(n:ℝ)^(-(7/50:ℝ))
  have hr : 0<r:=Real.rpow_pos_of_pos hNp _
  have hrL : r≤L:=hNt n ((le_max_right _ _).trans hn)
  have hMeanR : energyMeanDeficit n β≤Cm*r^5:=by
    simpa only [improved_optimal_mean_power (n:ℝ) hNp,r] using (hMean n hn2).2
  have hScalar (t : ℝ) (ht : 0<t) (htL : t≤L) :
      centeredEnergyCGF n β t≤Ls*(n:ℝ)*t^6+(n:ℝ)*t*energyMeanDeficit n β:=by
    rw [centeredEnergyCGF_eq_shifted n hn0]
    have hh:=hUpper n hn2 t ⟨ht,htL⟩
    linarith
  have hBoth : 0≤(n:ℝ)^(11/25:ℝ)*s^2 ∧ 0≤(n:ℝ)*s^6:=⟨by positivity,by positivity⟩
  by_cases hsL : s≤L
  · by_cases hsr : s≤r
    · have hEndpoint : centeredEnergyCGF n β r≤K1*(n:ℝ)*r^6:=by
        have hm:=mul_le_mul_of_nonneg_left hMeanR (mul_nonneg hNp.le hr.le)
        have hh:=hScalar r hr hrL
        dsimp only [K1]
        nlinarith only [hh,hm]
      have hb:=(native_centered_energy_cgf_positive_secant n β hβp s r hs hr hsr).trans
        (mul_le_mul_of_nonneg_left hEndpoint (sq_nonneg (s/r)))
      have he : (s/r)^2*(K1*(n:ℝ)*r^6)=K1*(n:ℝ)^(11/25:ℝ)*s^2:=by
        have hp:=improved_optimal_centered_secant_scale (n:ℝ) hNp
        change (n:ℝ)*r^4=(n:ℝ)^(11/25:ℝ) at hp
        rw [←hp]
        field_simp
        <;> ring
      rw [he] at hb
      have hk : K1*(n:ℝ)^(11/25:ℝ)*s^2≤K*((n:ℝ)^(11/25:ℝ)*s^2):=by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (le_max_left K1 (1/(4*L^4))) hBoth.1
      have ha : K*((n:ℝ)^(11/25:ℝ)*s^2)≤
          K*((n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6):=
        mul_le_mul_of_nonneg_left (show (n:ℝ)^(11/25:ℝ)*s^2≤
          (n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6 by linarith only [hBoth.2]) hK.le
      exact hb.trans (hk.trans ha)
    · have hrs : r≤ s:=le_of_not_ge hsr
      have hm:=hMeanR.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrs 5) hCm.le)
      have hmt:=mul_le_mul_of_nonneg_left hm (mul_nonneg hNp.le hs.le)
      have hb:=hScalar s hs hsL
      have hb1 : centeredEnergyCGF n β s≤K1*(n:ℝ)*s^6:=by dsimp only [K1];nlinarith only [hb,hmt]
      have hk : K1*(n:ℝ)*s^6≤K*((n:ℝ)*s^6):=by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (le_max_left K1 (1/(4*L^4))) hBoth.2
      have ha : K*((n:ℝ)*s^6)≤K*((n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6):=
        mul_le_mul_of_nonneg_left (show (n:ℝ)*s^6≤
          (n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6 by linarith only [hBoth.1]) hK.le
      exact hb1.trans (hk.trans ha)
  · have hLs : L≤ s:=le_of_not_ge hsL
    have hs4 : L^4≤ s^4:=pow_le_pow_left₀ hL.le hLs 4
    have hs2 : s^2≤ s^6/L^4:=by
      apply (le_div_iff₀ (pow_pos hL 4)).mpr
      have hh:=mul_le_mul_of_nonneg_left hs4 (sq_nonneg s)
      nlinarith only [hh]
    have hG:=native_centered_energy_cgf_gaussian_bound n hn2 β hβp s
    have hT:=mul_le_mul_of_nonneg_left hs2 (show 0≤(n:ℝ)/4 by positivity)
    have hB : centeredEnergyCGF n β s≤(1/(4*L^4))*(n:ℝ)*s^6:=by
      have he : (n:ℝ)/4*(s^6/L^4)=(1/(4*L^4))*(n:ℝ)*s^6:=by ring
      have hG' : centeredEnergyCGF n β s≤(n:ℝ)/4*s^2:=by convert hG using 1 <;> ring
      exact hG'.trans (hT.trans_eq he)
    have hk : (1/(4*L^4))*(n:ℝ)*s^6≤K*((n:ℝ)*s^6):=by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (le_max_right K1 (1/(4*L^4))) hBoth.2
    have ha : K*((n:ℝ)*s^6)≤K*((n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6):=
      mul_le_mul_of_nonneg_left (show (n:ℝ)*s^6≤
        (n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6 by linarith only [hBoth.1]) hK.le
    exact hB.trans (hk.trans ha)

end QuantitativeFollowup
