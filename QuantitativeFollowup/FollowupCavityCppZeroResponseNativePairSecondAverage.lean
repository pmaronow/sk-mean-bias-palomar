module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFinitePairSecondAverage
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFutureDerivative
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeRestHessian
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarNodeJets
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! The averaged actual incident second response is evaluated at the
native independent-endpoint state. Its current coefficient is the true
right CDF; the future term is the actual scalar derivative times the rest
conditional square, with every finite free charge retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem nativeAverage_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteRestMean_at_zero_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample))=
      anisotropicProcessSpinResponse Rest μ q i (cavityRestSampleProjection n sample) :=by
  dsimp only
  rw [cavityRestProcessParameter_zero]
  exact cavityFiniteRestSpinMean_at_native_scheme_node _ s J hJ i _

theorem cavityFiniteRestSelf_at_zero_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    (∑i : Fin n,(anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample)))^2)/(n:ℝ)=
      cavitySignedResponseSelfOverlap Rest μ q (cavityRestSampleProjection n sample) :=by
  dsimp only
  simp_rw [cavityFiniteRestMean_at_zero_native_scheme_node s n β ρ hβ hρ J hJ]
  simp only [cavitySignedResponseSelfOverlap,anisotropicSelectedMeanSquare,
    Finset.card_univ,Fintype.card_fin,anisotropicProcessSpinResponse]

theorem cavityFinitePairSecond_average_last_at_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q sample
    (∑i : Fin n,fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
        (anisotropicCoordinateDirection (n+1) (Fin.last n)))/(n:ℝ)=
      -2*Paper.parisiCDF μ q*M B μ q (sample.2 (Fin.last n))*C B μ q (sample.2 (Fin.last n))*
        cavitySignedResponseSelfOverlap Rest μ q (cavityRestSampleProjection n sample)-
      ∫r,if q<r then cavityRestFutureSquare Rest μ q r (cavityRestSampleProjection n sample)*
        scalarFutureSquareDerivativeExtended B μ q r
          (parisiPhysicalSplitState B 0 μ q (sample.2 (Fin.last n))) else 0 ∂parisiFreeMeasure μ a :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeAverage_zero_mem
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  have hnode : scalarSchemeTransportNode s (k+2-J)=q:=by
    apply Subtype.ext
    exact scalarSchemeTransportNode_coe s _ (by omega)
  rw [cavityFinitePairSecond_average_last_current s n β ρ hβ hρ J hJ a ha has hq]
  rw [hnode,cavityFiniteScalarMean_at_native_scheme_node s n β ρ hβ hρ J hJ,
    cavityFiniteScalarHessian_at_native_scheme_node s n β ρ hβ hρ J hJ,
    cavityFiniteRestSelf_at_zero_native_scheme_node s n β ρ hβ hρ J hJ,
    cavityFiniteFreeFutureSquare_average_last_derivative_eq_native_product s n β ρ hβ hρ
      a ha has hq J hJ]

end QuantitativeFollowup
