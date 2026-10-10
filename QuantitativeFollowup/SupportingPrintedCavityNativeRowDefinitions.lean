module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastSquareRowJets

@[expose] public section

/-! Literal deterministic incident-energy row derivatives for the step-profile
part of the cavity calculation. They differentiate the energy offset, including
when the Gaussian coupling coefficient of that row is zero. -/

noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}

def cavityPrintedFiniteRowPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) (z : ℝ) : ℝ :=
  finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
    (anisotropicEnergyMap D P + z • anisotropicPairFeature e)

def cavityPrintedFiniteRowFirst (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) : ℝ :=
  deriv (cavityPrintedFiniteRowPotential D s j P e) 0

def cavityPrintedFiniteRowSecond (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) : ℝ :=
  deriv (deriv (cavityPrintedFiniteRowPotential D s j P e)) 0

theorem cavityPrintedFiniteRow_deriv_affine_line {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hF : Differentiable ℝ F) (H K : E) (t : ℝ) :
    deriv (fun z : ℝ => F (H + z • K)) t = fderiv ℝ F (H + t • K) K :=
  (hasDerivAt_affine_line_of_differentiable F hF H K t).deriv

theorem cavityPrintedFiniteRow_deriv_deriv_affine_line {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hF : ContDiff ℝ ∞ F) (H K : E) :
    deriv (deriv (fun z : ℝ => F (H + z • K))) 0 =
      exponentialDensityHessian F H K K := by
  have he : deriv (fun z : ℝ => F (H + z • K)) =
      fun z => fderiv ℝ F (H + z • K) K :=
    funext (cavityPrintedFiniteRow_deriv_affine_line F (hF.differentiable (by simp)) H K)
  have hd : Differentiable ℝ (fun Q => fderiv ℝ F Q K) :=
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := K))).differentiable (by simp)
  rw [he, cavityPrintedFiniteRow_deriv_affine_line (fun Q => fderiv ℝ F Q K) hd H K 0,
    zero_smul, add_zero,
    (hasFDerivAt_exponential_directional_field F (hF.of_le (by simp)) H K).fderiv,
    ContinuousLinearMap.flip_apply]

theorem cavityPrintedFiniteRowFirst_eq_feature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    cavityPrintedFiniteRowFirst D s j P e =
      anisotropicFiniteFeatureMean D s j (anisotropicPairFeature e) P := by
  unfold cavityPrintedFiniteRowFirst cavityPrintedFiniteRowPotential
  rw [cavityPrintedFiniteRow_deriv_affine_line, zero_smul, add_zero,
    anisotropicFinitePair_energy_first]
  exact (contDiff_finiteStateGaussianTerminalCascade _ _
    (anisotropicSchemeMass_nonneg s) _ j).differentiable (by simp)

theorem cavityPrintedFiniteRowSecond_eq_pairSecond (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    cavityPrintedFiniteRowSecond D s j P e = anisotropicFinitePairSecond D s j P e := by
  unfold cavityPrintedFiniteRowSecond cavityPrintedFiniteRowPotential
  rw [cavityPrintedFiniteRow_deriv_deriv_affine_line _
    (contDiff_finiteStateGaussianTerminalCascade _ _ (anisotropicSchemeMass_nonneg s) _ j)]
  exact (anisotropicFinitePairSecond_eq_energy D s j P e).symm

theorem fderiv_cavityPrintedFiniteRowSecond_eq_pairSecond (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P V : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (fun Q => cavityPrintedFiniteRowSecond D s j Q e) P V =
      fderiv ℝ (fun Q => anisotropicFinitePairSecond D s j Q e) P V := by
  rw [show (fun Q => cavityPrintedFiniteRowSecond D s j Q e) =
      (fun Q => anisotropicFinitePairSecond D s j Q e) from
    funext (fun Q => cavityPrintedFiniteRowSecond_eq_pairSecond D s j Q e)]

end QuantitativeFollowup
