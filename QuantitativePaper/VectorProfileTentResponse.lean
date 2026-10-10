module
public import QuantitativePaper.VectorProfileTentEnergyTelescope

@[expose] public section

/-! Genuine quantitative finite-profile tent response bound. The actual
functional curvature controls the literal signal with the exact Xi
denominator, including every node jump. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileTentDenominator_nonneg (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    0≤vectorProfileTentDenominator (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell := by
  rw [←vectorProfile_tent_Xi_integral_sum hn s₀ s₁ β t outer θ hβ ht hθ ell hell]
  apply Finset.sum_nonneg
  intro i hi
  have hin : i≤k+1:=by have:=Finset.mem_range.mp hi;omega
  rw [intervalIntegral.integral_of_le (s₀.q_mono i (by omega))]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.ae_ne (s₀.q (i+1))).filter_mono (ae_mono Measure.restrict_le_self)] with q hq hqne
  exact (vectorProfileTentCell_pointwise_energy_bound hn s₀ s₁ β t outer θ hβ ht hθ ell i hin q
    ⟨hq.1,lt_of_le_of_ne hq.2 hqne⟩).2.1

theorem vectorProfile_tent_signal_energy_bound (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    (1-t)^3*(vectorProfileTentSignal (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell)^2≤
      vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩*
        vectorProfileTentDenominator (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell := by
  have hh:=vectorProfile_tent_integral_energy_bound hn s₀ s₁ β t outer θ hβ ht hθ ell
  rw [vectorProfile_tent_pairing_integral_sum hn s₀ s₁ β t outer θ hβ ht hθ ell hell,
    vectorProfile_tent_Xi_integral_sum hn s₀ s₁ β t outer θ hβ ht hθ ell hell] at hh
  have he (a b : ℝ) : a/(1-t)*b=a*b/(1-t):=by ring
  rw [he] at hh
  have hh':=(le_div_iff₀ (by linarith : 0<1-t)).mp hh
  nlinarith only [hh']

theorem vectorProfile_tent_functional_curvature_bound (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    (1-t)^3*(vectorProfileTentSignal (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell/(n:ℝ))^2≤
      iteratedDeriv 2 (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) θ*
        (vectorProfileTentDenominator (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell/(n:ℝ)) := by
  let S:=vectorProfileTentSignal (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell
  let D:=vectorProfileTentDenominator (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩ ell
  let E:=vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  let F:=iteratedDeriv 2 (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) θ
  have hn0 : (0:ℝ)<n:=by exact_mod_cast hn
  have hh : (1-t)^3*S^2≤E*D:=vectorProfile_tent_signal_energy_bound hn s₀ s₁ β t (lam/β) θ hβ ht hθ ell hell
  have hE : E≤F*(n:ℝ):=(div_le_iff₀ hn0).mp
    (vectorProfileFiniteEnergyFunctional_curvature_ge_total_energy hn s₀ s₁ β t lam θ hβ ht hlam hθ)
  have hD : 0≤D:=vectorProfileTentDenominator_nonneg hn s₀ s₁ β t (lam/β) θ hβ ht hθ ell hell
  have hfinal : (1-t)^3*S^2≤F*(n:ℝ)*D:=hh.trans (mul_le_mul_of_nonneg_right hE hD)
  change (1-t)^3*(S/(n:ℝ))^2≤F*(D/(n:ℝ))
  have hh':=div_le_div_of_nonneg_right hfinal (sq_nonneg (n:ℝ))
  have hnn : (n:ℝ)≠0:=ne_of_gt hn0
  convert hh' using 1 <;> field_simp [hnn] <;> ring

end QuantitativePaper
