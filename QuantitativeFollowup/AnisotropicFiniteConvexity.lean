module
public import QuantitativeFollowup.AnisotropicFiniteSmooth
public import FourPapersCommon.FiniteStateCascadeConvexity
public import QuantitativePaper.ConvexHessian

@[expose] public section

/-! Genuine joint disorder/field convexity and positive Hessians for the
literal anisotropic Gaussian Hopf--Cole potential. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}

theorem convexOn_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : ConvexOn ℝ univ (anisotropicFinitePotential D s j) := by
  exact (convexOn_finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).comp_linearMap
      (anisotropicEnergyMap D).toLinearMap

theorem anisotropicFinitePotential_hessian_nonneg (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P K : AnisotropicParameter n) :
    0 ≤ fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P K K :=
  directionalHessian_nonneg_of_convex _
    ((contDiff_anisotropicFinitePotential D s j).of_le (by simp))
    (convexOn_anisotropicFinitePotential D s j) P K

end QuantitativeFollowup
