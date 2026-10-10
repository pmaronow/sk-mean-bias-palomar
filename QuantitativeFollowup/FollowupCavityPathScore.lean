module
public import QuantitativeFollowup.FollowupCavityPathParameterCharge
public import QuantitativeFollowup.FollowupCavityPathHeatDerivative
public import FourPapersCommon.ChargedExponentialHessian

@[expose] public section

/-! Literal score-minus-curvature form of the simultaneous physical path
variance derivative. The scores use the actual retained vertex potentials. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityPathSpatialScore (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (b : ℝ) (y e : CavityPathGaussianSpace T n) : ℝ :=
  chargedDirectionalScore (cavityPathTerminalEnergy D s i T σ)
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth)
    (cavityPathVertexField D s i T) y e

def cavityPathSpatialSecondCharge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (b : ℝ) (y e : CavityPathGaussianSpace T n) : ℝ :=
  chargedDirectionalCurvature (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth)
    (cavityPathVertexField D s i T) y e

theorem fderiv_cavityPathLogNumerator_spatial (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y e : CavityPathGaussianSpace T n) :
    fderiv ℝ (fun z=>cavityPathLogNumerator D s a i T σ (b,z)) y e=
      cavityPathSpatialScore D s a i T σ b y e := by
  exact fderiv_chargedLogPotential _ _ _ _ (fun v : FiniteCascadeRecordVertex T=>
    (contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth).of_le (by norm_num)) y e

theorem hessian_cavityPathNumerator_spatial (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y e : CavityPathGaussianSpace T n) :
    fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y e e=
      cavityPathNumerator D s a i T σ (b,y)*
        ((cavityPathSpatialScore D s a i T σ b y e)^2-
          cavityPathSpatialSecondCharge D s a i T b y e) := by
  exact exponentialDensityHessian_exp_chargedLogPotential _ _ _ _ (fun v : FiniteCascadeRecordVertex T=>
    (contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth).of_le (by norm_num)) y e

def cavityPathScoreGenerator (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) : ℝ :=
  -cavityPathParameterCharge D s a i T b y+(1/2:ℝ)*
    ∑e,if cavitySelectedRootPathMask i T e then
      (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2-
        cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0

theorem cavityPathHeatGenerator_eq_score (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) (y : CavityPathGaussianSpace T n) :
    cavityPathHeatGenerator D s a i T σ b y=
      cavityPathNumerator D s a i T σ (b,y)*cavityPathScoreGenerator D s a i T σ b y := by
  unfold cavityPathHeatGenerator cavityPathScoreGenerator
  rw [fderiv_cavityPathNumerator_parameter D s a i T hj σ b hb y]
  simp_rw [hessian_cavityPathNumerator_spatial D s a i T σ b y]
  have he : (∑e,if cavitySelectedRootPathMask i T e then
      cavityPathNumerator D s a i T σ (b,y)*
        ((cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2-
          cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e)) else 0)=
      cavityPathNumerator D s a i T σ (b,y)*∑e,if cavitySelectedRootPathMask i T e then
        (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2-
          cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp_all only [mul_zero]
  rw [he]
  ring

theorem hasDerivAt_cavityPathSpinWeight_score (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) :
    HasDerivAt (cavityPathSpinWeight D s a i T σ)
      (∫z : CavityPathGaussianSpace T n,
        cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)*
          cavityPathScoreGenerator D s a i T σ b
            (gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)
              ∂ProbabilityTheory.stdGaussian (CavityPathGaussianSpace T n)) b := by
  simpa only [cavityPathHeatGenerator_eq_score D s a i T hj σ b hb] using
    hasDerivAt_cavityPathSpinWeight D s a i T hj σ b hb

end QuantitativeFollowup
