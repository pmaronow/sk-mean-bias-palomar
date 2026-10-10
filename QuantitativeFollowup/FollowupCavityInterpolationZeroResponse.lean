module
public import QuantitativeFollowup.FollowupCavityFiniteEndpointSmooth
public import FourPapersCommon.GaussianExponentialParameterContinuity
public import FourPapersCommon.GaussianSelectedMovingZeroHeat

@[expose] public section

/-! The genuine finite spin-weight response extends to zero incident
variance. Its Gaussian heat generator is continuous by actual exponential
jet domination, and the true interior derivative extends by mean value. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

private theorem continuous_selectedScale_joint {A:Type}[Fintype A][DecidableEq A](p:A→Bool):
    Continuous (fun z:ℝ×EuclideanSpace ℝ A=>gaussianSelectedScale p z.1 z.2):=by
  simp_rw [gaussianSelectedScale_apply]
  apply continuous_finsetSum
  intro i _
  by_cases hi:p i=true
  · simp only [hi,ite_true]
    fun_prop
  · simp only [ite_eq_right hi,one_mul]
    fun_prop

theorem continuousAt_cavityInterpolationSpinResponse_zero
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hj:j ≤ k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ:TerminalSpins (Configuration n) T)(d alpha:ℝ)(hd:0<d):
    ContinuousAt (cavityInterpolationSpinResponse D p s a i T σ d alpha) 0:=by
  let S:=fun u=>cavityInterpolationGaussianScale p i T u (d-alpha*u)
  let G:=fun z:ℝ×CavityPathGaussianSpace T n=>cavityInterpolationHeatGenerator D p s a i T σ alpha z.1 z.2
  let M:ℝ:=((Fintype.card (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T):ℝ)*2)*
    ((Fintype.card (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T):ℝ)*(1+Real.sqrt (d+1)))
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (d/2) (d+1) (by linarith)
  have hG:ExponentialSmoothOn G ((Ioo (d/2) (d+1))×ˢ(univ:Set (CavityPathGaussianSpace T n))):=
    exponentialSmoothOn_parameter_heat_generator (cavityRootCouplingMask p T) (cavitySelectedRootPathMask i T)
      (cavityPathNumerator D s a i T σ) alpha (d/2) (d+1) hs
  have hb:ContinuousAt (fun u:ℝ=>d-alpha*u) 0:=by fun_prop
  have hSc (z:CavityPathGaussianSpace T n):ContinuousAt (fun u=>S u z) 0:=by
    dsimp only [S,cavityInterpolationGaussianScale,ContinuousLinearMap.comp_apply]
    have hP:Continuous (fun u:ℝ=>gaussianSelectedScale (cavitySelectedRootPathMask i T) (d-alpha*u) z):=
      (continuous_gaussianSelectedScale_apply _ z).comp (by fun_prop)
    exact ((continuous_selectedScale_joint (cavityRootCouplingMask p T)).comp
      (continuous_id.prodMk hP)).continuousAt
  have hM:0≤M:=by dsimp only [M];positivity
  have hbI:∀ᶠu:ℝ in 𝓝 0,d-alpha*u∈Ioo (d/2) (d+1):=by
    have hh:Tendsto (fun u:ℝ=>d-alpha*u) (𝓝 0) (𝓝 d):=by
      simpa only [mul_zero,sub_zero] using hb.tendsto
    exact hh.eventually (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hSb:∀ᶠu in 𝓝 (0:ℝ),∀z:CavityPathGaussianSpace T n,‖S u z‖≤M*‖z‖:=by
    have hu:∀ᶠu:ℝ in 𝓝 0,u<1:=Iio_mem_nhds (by norm_num)
    filter_upwards [hu,hbI] with u hu hbu
    intro z
    dsimp only [S,cavityInterpolationGaussianScale,ContinuousLinearMap.comp_apply]
    have h1:=norm_gaussianSelectedScale_le (cavityRootCouplingMask p T) u 1 hu.le
      (gaussianSelectedScale (cavitySelectedRootPathMask i T) (d-alpha*u) z)
    have h2:=norm_gaussianSelectedScale_le (cavitySelectedRootPathMask i T) (d-alpha*u) (d+1) hbu.2.le z
    apply h1.trans
    have hh:=mul_le_mul_of_nonneg_left h2
      (show 0≤(Fintype.card (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T):ℝ)*(1+Real.sqrt 1) by positivity)
    convert! hh using 1 <;> simp only [Real.sqrt_one,M] <;> ring
  have hc:=continuousAt_gaussian_exponential_parameter_integral G (d/2) (d+1) hG
    (fun u=>d-alpha*u) S 0 (by simp only [mul_zero,sub_zero];constructor <;> linarith) hb hSc M hM hSb
  have he:(cavityInterpolationSpinResponse D p s a i T σ d alpha)=ᶠ[𝓝 (0:ℝ)]
      (fun u=>∫z:CavityPathGaussianSpace T n,G (d-alpha*u,S u z)∂stdGaussian (CavityPathGaussianSpace T n)):=by
    filter_upwards [hbI] with u hu
    unfold cavityInterpolationSpinResponse
    apply integral_congr_ae
    exact .of_forall fun z=>(cavityInterpolationHeatGenerator_eq_record_score D p s a i T hj σ alpha
      (d-alpha*u) (by linarith [hu.1]) _).symm
  exact hc.congr_of_eventuallyEq he

theorem hasDerivWithinAt_cavityInterpolationSpinWeight_zero
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hj:j ≤ k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ:TerminalSpins (Configuration n) T)(d alpha:ℝ)(halpha:0≤alpha)(hd:0<d-alpha):
    HasDerivWithinAt (fun u=>cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u))
      (cavityInterpolationSpinResponse D p s a i T σ d alpha 0) (Ici (0:ℝ)) 0:=by
  let f:=fun u=>cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u)
  let R:=cavityInterpolationSpinResponse D p s a i T σ d alpha
  have hd0:0<d:=by linarith
  have hf:ContinuousOn f (Icc (0:ℝ) 1):=
    (contDiffOn_cavityInterpolationSpinWeight_closed D p s a i T hj σ d alpha halpha hd).continuousOn
  have hR:ContinuousAt (fun z:ℝ×ℝ=>R z.2) (0,0):=
    ContinuousAt.comp (f:=fun z:ℝ×ℝ=>z.2) (g:=R)
      (continuousAt_cavityInterpolationSpinResponse_zero D p s a i T hj σ d alpha hd0) continuous_snd.continuousAt
  have hx:=hasDerivWithinAt_moving_increment_zero (fun _=>f) (fun _=>R) univ 0 0 (by simp)
    (fun _ _=>hf) (fun _ _ u hu=>hasDerivAt_cavityInterpolationSpinWeight_record_score D p s a i T hj σ
      d alpha u halpha hu.1 (by nlinarith [hu.2,halpha])) hR
  have ha:=hx.add_const (f 0)
  simpa only [zero_mul,sub_zero,sub_add_cancel,f,R] using ha

end QuantitativeFollowup
