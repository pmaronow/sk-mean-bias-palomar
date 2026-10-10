module
public import QuantitativePaper.VectorProfileGridLipschitzDenominator
public import QuantitativePaper.VectorProfileGridFunctionalIdentification

@[expose] public section

/-! Actual measure-profile Lipschitz signal and Xi denominator. The common
dyadic approximation satisfies the literal functional-curvature bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def responseLipschitzSignal (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (ht : t≤1)
    (w : ResponseLipschitzTest) : ℝ:=∫q in (0:ℝ)..1,
  β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q)*w.value q*
    responseAveragedCurvatureReal (n:=n) (Paper.parisiMix μ ν θ) β t lam ht q

def responseLipschitzEnergyDenominator (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (ht : t≤1)
    (w : ResponseLipschitzTest) : ℝ:=
  (∫q in (0:ℝ)..1,(w.slope q)^2*
    responseMeanHessianReal (n:=n) (Paper.parisiMix μ ν θ) β t lam ht q)+
  2*(1-t)*β*(∫q : Paper.Overlap,(w.value q)^2*
    responseAveragedCurvature (n:=n) (Paper.parisiMix μ ν θ) β t lam ht q
    ∂(Paper.parisiMix μ ν θ : Measure Paper.Overlap))

theorem response_grid_Lipschitz_functional_curvature_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ) (hβ : 0<β)
    (ht : t<1) (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest)
    :
    (1-t)^3*(responseLipschitzSignal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w)^2≤
      iteratedDeriv 2 (fun y=>responseEnergyFunctional n
        (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
          (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) θ*
      responseLipschitzEnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w:=by
  have hh:=vectorProfile_Lipschitz_functional_curvature_bound hn
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t lam θ hβ ht hlam hθ w
  have hsig:=vectorProfile_grid_Lipschitz_signal_eq hn μ ν j β t lam θ w ht ⟨hθ.1.le,hθ.2.le⟩
  have hden:=vectorProfile_grid_Lipschitz_denominator_eq hn μ ν j β t lam θ w ht ⟨hθ.1.le,hθ.2.le⟩
  rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ ⟨hθ.1.le,hθ.2.le⟩] at hsig hden
  have he : vectorProfileFiniteEnergyFunctional (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t lam=ᶠ[𝓝 θ]
      (fun y=>responseEnergyFunctional n
        (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
          (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    rw [vectorProfile_grid_functional_eq μ ν j β t lam y ht.le ⟨hy.1.le,hy.2.le⟩,
      parisiGridMeasure_mix μ ν (vectorDyadicIndex j) y ⟨hy.1.le,hy.2.le⟩]
  rw [hsig,hden,he.iteratedDeriv_eq 2] at hh
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  simpa only [responseLipschitzSignal,responseLipschitzEnergyDenominator,mul_div_cancel_left₀ _ hn0] using hh

theorem response_grid_Lipschitz_denominator_nonneg (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ) (hβ : 0<β)
    (ht : t<1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    0≤responseLipschitzEnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w:=by
  have hh:=vectorProfileLipschitzDenominator_nonneg hn
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t (lam/β) θ hβ ht hθ w
  rw [vectorProfile_grid_Lipschitz_denominator_eq hn μ ν j β t lam θ w ht ⟨hθ.1.le,hθ.2.le⟩,
    parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ ⟨hθ.1.le,hθ.2.le⟩] at hh
  change 0≤(n:ℝ)*responseLipschitzEnergyDenominator (n:=n)
    (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
    (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w at hh
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hn : (0:ℝ)<n)).mp hh

end QuantitativePaper
