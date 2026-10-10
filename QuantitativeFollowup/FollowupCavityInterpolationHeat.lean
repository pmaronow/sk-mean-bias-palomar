module
public import QuantitativeFollowup.FollowupCavityInterpolationWeights
public import FourPapersCommon.GaussianTwoMaskHeat
public import FourPapersCommon.ExponentialParameterHeatBounds

@[expose] public section

/-! The simultaneous physical clock derivative, proved from the actual
Gaussian product: the incident row increases while the last-spin path
variance decreases. No derivative or integrability conclusion is a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityGaussianTwoMaskScale_coordinate {A : Type} [Fintype A] [DecidableEq A]
    (pR pP : A→Bool) (d alpha u : ℝ) (z : EuclideanSpace ℝ A) (e : A) :
    gaussianTwoMaskScale pR pP d alpha u z e=gaussianTwoMaskCoefficient pR pP d alpha u e*z e := by
  rw [gaussianTwoMaskScale_apply]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp

theorem cavityInterpolationGaussianScale_eq_twoMask (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (d alpha u : ℝ) :
    cavityInterpolationGaussianScale p i T u (d-alpha*u)=
      gaussianTwoMaskScale (cavityRootCouplingMask p T) (cavitySelectedRootPathMask i T) d alpha u := by
  ext z e
  rw [cavityGaussianTwoMaskScale_coordinate]
  change gaussianSelectedScale (cavityRootCouplingMask p T) u
      (gaussianSelectedScale (cavitySelectedRootPathMask i T) (d-alpha*u) z) e=_
  rw [cavityGaussianSelectedScale_coordinate,cavityGaussianSelectedScale_coordinate]
  cases e with
  | inl e => cases hp:p e <;> simp [cavityRootCouplingMask,cavitySelectedRootPathMask,
      gaussianTwoMaskCoefficient,hp]
  | inr e => cases hp:cavitySelectedEdgeMask i T e <;>
      simp [cavityRootCouplingMask,cavitySelectedRootPathMask,gaussianTwoMaskCoefficient,hp]

def cavityInterpolationHeatGenerator (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (alpha b : ℝ) (y : CavityPathGaussianSpace T n) : ℝ :=
  -alpha*fderiv ℝ (cavityPathNumerator D s a i T σ) (b,y) (1,0)+
    (1/2:ℝ)*(∑e,if cavityRootCouplingMask p T e then
      fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y
        (EuclideanSpace.basisFun _ ℝ e) (EuclideanSpace.basisFun _ ℝ e) else 0)-
    (alpha/2)*(∑e,if cavitySelectedRootPathMask i T e then
      fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y
        (EuclideanSpace.basisFun _ ℝ e) (EuclideanSpace.basisFun _ ℝ e) else 0)

theorem hasDerivAt_cavityInterpolationSpinWeight (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (d alpha u : ℝ)
    (ha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    HasDerivAt (fun q=>cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∫z : CavityPathGaussianSpace T n,cavityInterpolationHeatGenerator D p s a i T σ alpha
        (d-alpha*u) (cavityInterpolationGaussianScale p i T u (d-alpha*u) z)
          ∂stdGaussian (CavityPathGaussianSpace T n)) u := by
  let b:=d-alpha*u
  let L:=u/2
  let U:=u+b/(4*(alpha+1))
  have hd : 0<d:=by nlinarith
  have hden : 0<4*(alpha+1):=by positivity
  have hstep : 0<b/(4*(alpha+1)):=div_pos hb hden
  have hr : alpha*(b/(4*(alpha+1)))≤b/4:=by
    rw [←mul_div_assoc,div_le_iff₀ hden]
    dsimp only [b] at *
    nlinarith
  have hqb (q : ℝ) (hq : q∈Ioo L U) : d-alpha*q∈Ioo (b/2) (d+1) := by
    have hq0 : 0<q:=(show 0<L by dsimp only [L];linarith).trans hq.1
    have hmul:=mul_le_mul_of_nonneg_left hq.2.le ha
    dsimp only [U] at hmul
    have hup : alpha*q≤alpha*u+b/4:=by nlinarith
    constructor
    · dsimp only [b] at *;linarith
    · have :=mul_nonneg ha hq0.le;linarith
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (d+1) (by dsimp only [b];linarith)
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hs.parameter_heat_bounds _ _ _
  have hdis : ∀e,cavityRootCouplingMask p T e=true→cavitySelectedRootPathMask i T e=false := by
    intro e he
    cases e <;> simp_all [cavityRootCouplingMask,cavitySelectedRootPathMask]
  have huI : u∈Ioo L U:=⟨by dsimp only [L];linarith,by dsimp only [U];linarith⟩
  have h:=hasDerivAt_gaussianTwoMask_heat_integral (cavityRootCouplingMask p T)
    (cavitySelectedRootPathMask i T) d alpha hdis (cavityPathNumerator D s a i T σ)
    L U (b/2) (d+1) u B K ha (by dsimp only [L];linarith) (by dsimp only [b];linarith)
    huI hqb hB hK (contDiffOn_of_exponentialSmoothOn hs) h0 h1 (h2 b (hqb u huI))
  simpa only [cavityInterpolationSpinWeight,cavityInterpolationGaussianScale_eq_twoMask,
    cavityInterpolationHeatGenerator,b] using h

end QuantitativeFollowup
