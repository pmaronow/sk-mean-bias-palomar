module
public import QuantitativeFollowup.FollowupCavityPathNumeratorRegularity
public import QuantitativeFollowup.FollowupCavitySelectedPathMask
public import FourPapersCommon.ExponentialParameterHeatBounds
public import FourPapersCommon.GaussianSelectedParameterHeat

@[expose] public section

/-! Genuine simultaneous path-variance differentiation of the actual
marked numerator. Parameter-potential and shared-path Hessian terms both
come from the literal finite model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def cavityPathSpinWeight (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) : ℝ :=
  ∫z : CavityPathGaussianSpace T n,cavityPathNumerator D s a i T σ
    (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)
      ∂stdGaussian (CavityPathGaussianSpace T n)

def cavityPathHeatGenerator (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) : ℝ :=
  fderiv ℝ (cavityPathNumerator D s a i T σ) (b,y) (1,0) +
    (1/2:ℝ)*(∑e,if cavitySelectedRootPathMask i T e then
      fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y
        (EuclideanSpace.basisFun _ ℝ e) (EuclideanSpace.basisFun _ ℝ e) else 0)

theorem hasDerivAt_cavityPathSpinWeight (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) :
    HasDerivAt (cavityPathSpinWeight D s a i T σ)
      (∫z : CavityPathGaussianSpace T n,cavityPathHeatGenerator D s a i T σ b
        (gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)
          ∂stdGaussian (CavityPathGaussianSpace T n)) b := by
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hs.parameter_heat_bounds _ _ _
  exact hasDerivAt_gaussianSelected_parameter_heat_integral (cavitySelectedRootPathMask i T)
    (cavityPathNumerator D s a i T σ) (b/2) (3*b/2) b B K (by linarith)
      ⟨by linarith,by linarith⟩ hB hK (contDiffOn_of_exponentialSmoothOn hs) h0 h1
        (h2 b ⟨by linarith,by linarith⟩)

theorem cavityPathNumerator_scaled_eq_actual_density (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) (z : CavityPathGaussianSpace T n) :
    cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z) /
      finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a j (anisotropicRootEnergyMap D) 0 =
      finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0 (z,σ) := by
  rw [cavityPathVariance_flat_density D s a i b hb T]
  unfold cavityPathNumerator
  rw [cavityPathLogNumerator_eq_actual,gaussianSelectedScale_eq_cavityPathDiagonal]
  rfl

end QuantitativeFollowup
