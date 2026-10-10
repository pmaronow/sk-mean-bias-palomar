module
public import QuantitativePaper.ResponseMidpointModel
public import QuantitativePaper.ResponseTentMidpoint
public import QuantitativePaper.ResponseTentPhysicalBounds

@[expose] public section

/-! Full literal Appendix Proposition A.2. The actual finite response/Dynkin
identity, closed-cell jump telescope, atom-retaining weak-measure passage,
and nonnegative-curvature Fatou argument discharge every analytic input. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

theorem response_midpoint : ResponseMidpointTarget:=by
  intro n hn β t lam hβ ht hlam μ ν hfloor₀ hfloor₁
  refine ⟨responseEnergyFunctional_mix_convex n μ ν β t lam hβ ht.2.le hlam.1,?_⟩
  intro hβ1 ell κ U bbar Sigma hell hκ hU hbbar hSigma hv hγ hb hBudget
  let c:=responseCurvatureConstant U
  let ρ:=1-t
  let Y:=8*bbar/ell+2*Sigma
  let C:=c^4*ρ^3*κ^2*ell^3/(32*(8*bbar+ell*Sigma))
  have hr : 0<ρ:=sub_pos.mpr ht.2
  have hEll : 0<ell:=hell.1
  have hY : 0<Y:=by dsimp only [Y];positivity
  have hC : 0≤C:=by dsimp only [C];positivity
  have hfloor (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
      lam≤β*Paper.parisiCDF (Paper.parisiMix μ ν θ) 0:=by
    rw [Paper.parisiCDF_mix μ ν θ 0 ⟨hθ.1.le,hθ.2.le⟩]
    have h₀:=mul_le_mul_of_nonneg_left hfloor₀ (by linarith [hθ.2] : 0≤1-θ)
    have h₁:=mul_le_mul_of_nonneg_left hfloor₁ hθ.1.le
    nlinarith
  have hh:=response_tent_full_midpoint_lower hn μ ν β t lam hβ ht.2 hlam.1 ell hell
    (fun _=>Y) C hC (fun _ _=>hY)
    (fun θ hθ=>responseTentEnergyDenominator_upper μ ν β t lam θ ell bbar Sigma hβ.le ht.2 hell
      (hb θ hθ) (hBudget θ hθ)) (fun θ hθ=>by
        have hp:=responseTentSignal_lower hn μ ν β t lam θ ell κ U hβ1 ht hlam.1 hell hκ.le
          (hfloor θ hθ) (hv θ hθ) (hγ θ hθ)
        have hconst:=response_tent_curvature_constant c ρ κ ell bbar Sigma
          (responseTentSignal (n:=n) μ ν β t lam θ ht.2.le ell) Y
          (ρ^3*(responseTentSignal (n:=n) μ ν β t lam θ ht.2.le ell)^2/Y)
          hr.le hκ.le hell.1 hbbar hSigma hY hp le_rfl le_rfl
        exact (le_div_iff₀ hY).mp hconst)
  exact response_midpoint_printed_constant c ρ κ ell bbar Sigma _ hh

end QuantitativePaper
