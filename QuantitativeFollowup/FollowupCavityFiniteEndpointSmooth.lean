module
public import QuantitativeFollowup.FollowupCavityMarkedCovariance
public import FourPapersCommon.GaussianSignedAmplitudeSmooth

@[expose] public section

/-! Actual finite-profile physical marked expectations are infinitely smooth
on the closed interpolation interval. The zero incident-row endpoint is
proved by signed Gaussian amplitude and genuine radial differentiation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem contDiffOn_cavityInterpolationSpinWeight_closed (D : AnisotropicSpinModel n)
    (p:AnisotropicCouplingIndex n→Bool) (s:RSBScheme k) (a:ℝ) (i:Fin n)
    {j:ℕ} (T:FiniteTerminalGenealogy j) (hj:j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n⊕GaussianCoordinateIndex (Fin n) T)]
    (σ:TerminalSpins (Configuration n) T) (d alpha:ℝ) (ha:0≤alpha) (hd:0<d-alpha) :
    ContDiffOn ℝ ∞ (fun u=>cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))
      (Icc (0:ℝ) 1) := by
  have h:=contDiffOn_gaussianTwoMask_integral_closed (cavityRootCouplingMask p T)
    (cavitySelectedRootPathMask i T) d alpha ha hd (cavityPathNumerator D s a i T σ)
    (fun l u hl=>exponentialSmoothOn_cavityPathNumerator D s a i T hj σ l u hl)
  simpa only [cavityInterpolationSpinWeight,cavityInterpolationGaussianScale_eq_twoMask] using h

theorem contDiffOn_cavityInterpolationMarkedExpectation_closed (D : AnisotropicSpinModel n)
    (p:AnisotropicCouplingIndex n→Bool) (s:RSBScheme k) (a:ℝ) (i:Fin n)
    {j:ℕ} (T:FiniteTerminalGenealogy j) (hj:j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n⊕GaussianCoordinateIndex (Fin n) T)]
    (F:TerminalSpins (Configuration n) T→ℝ)
    (d alpha:ℝ) (ha:0≤alpha) (hd:0<d-alpha) :
    ContDiffOn ℝ ∞ (fun u=>cavityInterpolationMarkedExpectation D p s a i T F u (d-alpha*u))
      (Icc (0:ℝ) 1) := by
  have hs (σ):=contDiffOn_cavityInterpolationSpinWeight_closed D p s a i T hj σ d alpha ha hd
  have hnum:ContDiffOn ℝ ∞ (fun u=>∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))
      (Icc (0:ℝ) 1):=ContDiffOn.sum (fun σ _=>contDiffOn_const.mul (hs σ))
  have hden:ContDiffOn ℝ ∞ (fun u=>∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))
      (Icc (0:ℝ) 1):=ContDiffOn.sum (fun σ _=>hs σ)
  have hp (u:ℝ) (hu:u∈Icc 0 1):0<d-alpha*u:=by
    have hh:=mul_le_mul_of_nonneg_left hu.2 ha
    linarith
  have hc:=hnum.div hden (fun u hu=>(cavityInterpolationSpinWeight_sum_pos D p s a i T u
    (d-alpha*u) (hp u hu)).ne')
  apply hc.congr
  intro u hu
  exact (cavityInterpolationMarkedExpectation_eq_normalized_weights D p s a i T F u
    (d-alpha*u) (hp u hu))

/-- Native finite-profile version of the smoothness clause in streaming,
with one-sided smooth jets at both endpoints. -/
theorem contDiffOn_followupCavityPhysicalExpectation (n:ℕ) (β ρ:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc 0 1) (s:RSBScheme k) (a:ℝ)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) :
    ContDiffOn ℝ ∞ (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1) := by
  classical
  have hc:=contDiffOn_cavityInterpolationMarkedExpectation_closed
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
    (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T) (by omega)
    (fun σ=>F (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))
    (followupCavityD n β ρ) (followupCavityAlpha n β ρ)
    (followupCavityAlpha_nonneg n β ρ hρ.2) (by
      have h:=followupCavityB_window n β ρ 1 hρ.2 ⟨zero_le_one,le_rfl⟩
      have hp:=mul_pos (sq_pos_of_pos hβ) hρ.1
      dsimp only [followupCavityB,followupCavityC] at h
      simpa only [mul_one] using hp.trans_le h.1)
  unfold followupCavityPhysicalExpectation followupCavityB
  convert! hc using 1

end QuantitativeFollowup
