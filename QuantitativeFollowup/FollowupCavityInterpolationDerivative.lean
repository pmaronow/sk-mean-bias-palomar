module
public import QuantitativeFollowup.FollowupCavityInterpolationScore

@[expose] public section

/-! Genuine normalized simultaneous interpolation derivative. The numerator
and denominator are differentiated under their actual finite Gaussian laws,
then the quotient is identified with the actual marked expectation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityInterpolationSpinResponse (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (d alpha u : ℝ) : ℝ :=
  ∫z : CavityPathGaussianSpace T n,
    cavityPathNumerator D s a i T σ (d-alpha*u,cavityInterpolationGaussianScale p i T u (d-alpha*u) z)*
      cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u)
        (cavityPathFixedRecord D s i T σ (cavityInterpolationGaussianScale p i T u (d-alpha*u) z))
          ∂stdGaussian (CavityPathGaussianSpace T n)

theorem hasDerivAt_cavityInterpolationMarkedExpectation (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (d alpha u : ℝ)
    (ha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    HasDerivAt (fun q=>cavityInterpolationMarkedExpectation D p s a i T F q (d-alpha*q))
      ((∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha u)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))-
      cavityInterpolationMarkedExpectation D p s a i T F u (d-alpha*u)*
        ((∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha u)/
          (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u)))) u := by
  have hnum : HasDerivAt (fun q=>∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha u) u := by
    apply HasDerivAt.fun_sum
    intro σ _
    exact (hasDerivAt_cavityInterpolationSpinWeight_record_score D p s a i T hj σ d alpha u ha hu hb).const_mul _
  have hden : HasDerivAt (fun q=>∑σ,cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha u) u := by
    apply HasDerivAt.fun_sum
    intro σ _
    exact hasDerivAt_cavityInterpolationSpinWeight_record_score D p s a i T hj σ d alpha u ha hu hb
  have hn : (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))≠0:=
    (cavityInterpolationSpinWeight_sum_pos D p s a i T u (d-alpha*u) hb).ne'
  have hd:=hnum.div hden hn
  have he : ((∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha u)*
      (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))-
      (∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))*
        (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha u))/
      (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))^2=
      (∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha u)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))-
      cavityInterpolationMarkedExpectation D p s a i T F u (d-alpha*u)*
        ((∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha u)/
          (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))) := by
    rw [cavityInterpolationMarkedExpectation_eq_normalized_weights D p s a i T F u (d-alpha*u) hb]
    field_simp [hn]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  have hq : ∀ᶠq in 𝓝 u,0<d-alpha*q :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).eventually (Ioi_mem_nhds hb)
  filter_upwards [hq] with q hq
  dsimp only [Pi.div_apply]
  exact cavityInterpolationMarkedExpectation_eq_normalized_weights D p s a i T F q (d-alpha*q) hq

end QuantitativeFollowup
