module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFinitePairSecondAverage
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFutureDerivative
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeRestHessian
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarNodeJets

@[expose] public section

/-! The old-coordinate differential of the averaged incident second
response at the actual native independent-endpoint state. The current
term has the genuine right CDF and the future term retains the complete
finite free measure, including root and repeated charges. -/
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

 theorem oldAverage_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

private theorem oldAverage_rest_direction (n : ℕ) (l : Fin n) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) l.castSucc)=
      anisotropicCoordinateDirection n l :=by
  ext i
  cases i <;> simp [cavityRestParameterProjection,anisotropicCoordinateDirection,
    anisotropicFieldInjection,EuclideanSpace.single_apply]

private theorem oldAverage_last_direction (n : ℕ) (l : Fin n) :
    anisotropicCoordinateDirection (n+1) l.castSucc (Sum.inr (Fin.last n))=0 :=by
  have hn : Fin.last n≠l.castSucc :=by
    intro h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_last,Fin.val_castSucc] at hv
    omega
  simp [anisotropicCoordinateDirection,anisotropicFieldInjection,EuclideanSpace.single_apply,hn]

private theorem oldAverage_finite_mean_spatial (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (J : ℕ) (i l : Fin n) (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 oldAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    fderiv ℝ (anisotropicFiniteFeatureMean D s J
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))) P
        (anisotropicCoordinateDirection (n+1) l.castSucc)=
      parisiFDeriv s (followupCavityScalarBeta n β ρ) J (P (Sum.inr (Fin.last n)))*
        fderiv ℝ (anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i)))
          (cavityRestParameterProjection n P) (anisotropicCoordinateDirection n l) :=by
  dsimp only
  rw [cavityFiniteIncidentMean_parameter_spatial s n β ρ hβ hρ J i P]
  simp only [oldAverage_rest_direction,oldAverage_last_direction,mul_zero,zero_add]

theorem cavityFinitePairSecond_average_old_at_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (sample : AnisotropicDisorderBrownianSample (n+1)) (l : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 oldAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q sample
    let z:=cavityRestSampleProjection n sample
    (∑i : Fin n,fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
        (anisotropicCoordinateDirection (n+1) l.castSucc))/(n:ℝ)=
      -2*Paper.parisiCDF μ q*(M B μ q (sample.2 (Fin.last n)))^2*
        (∑i : Fin n,anisotropicProcessSpinResponse Rest μ q i z*
          nativeAnisotropicProcessHessianMatrix Rest μ q z l i)/(n:ℝ)-
      ∫r,if q<r then scalarFutureSquareExtended B μ q r
          (parisiPhysicalSplitState B 0 μ q (sample.2 (Fin.last n)))*
        fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ z.1 q x r)
          (anisotropicMeasureState Rest μ q z) (EuclideanSpace.single l 1)
        else 0 ∂parisiFreeMeasure μ a :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 oldAverage_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let z:=cavityRestSampleProjection n sample
  have hnode : scalarSchemeTransportNode s (k+2-J)=q :=by
    apply Subtype.ext
    exact scalarSchemeTransportNode_coe s _ (by omega)
  rw [cavityFinitePairSecond_average_free_spatial _ s J hJ a ha has hq]
  rw [hnode,cavityFiniteFreeFutureSquare_average_old_derivative_eq_native_product
    s n β ρ hβ hρ a ha has hq J hJ sample l]
  have hm:=cavityFiniteScalarMean_at_native_scheme_node s n β ρ hβ hρ J hJ sample
  have hP:=cavityRestProcessParameter_zero μ n β ρ hβ hρ q sample
  have hM (i : Fin n):anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample))=
      anisotropicProcessSpinResponse Rest μ q i z :=by
    rw [hP]
    exact cavityFiniteRestSpinMean_at_native_scheme_node Rest s J hJ i z
  have hH (i : Fin n):fderiv ℝ (anisotropicFiniteFeatureMean Rest s J
      (fun σ=>Paper.spinSign (σ i)))
      (cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample))
      (anisotropicCoordinateDirection n l)=nativeAnisotropicProcessHessianMatrix Rest μ q z l i :=by
    rw [hP]
    exact cavityFiniteRestHessian_at_native_scheme_node Rest s J hJ i l z
  have hsum:
      (∑i : Fin n,anisotropicFiniteFeatureMean D s J
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))
          (anisotropicProcessParameter D μ q sample)*
        fderiv ℝ (anisotropicFiniteFeatureMean D s J
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))))
          (anisotropicProcessParameter D μ q sample)
          (anisotropicCoordinateDirection (n+1) l.castSucc))=
      ∑i : Fin n,(anisotropicProcessSpinResponse Rest μ q i z*
        M (followupCavityScalarBeta n β ρ) μ q (sample.2 (Fin.last n)))*
        (M (followupCavityScalarBeta n β ρ) μ q (sample.2 (Fin.last n))*
          nativeAnisotropicProcessHessianMatrix Rest μ q z l i) :=by
    apply Finset.sum_congr rfl
    intro i _
    rw [cavityFiniteRowFeature_zero,oldAverage_finite_mean_spatial,hm,hM,hH]
  rw [hsum]
  have hs (m : ℝ) (v h : Fin n→ℝ) :
      (∑i : Fin n,(v i*m)*(m*h i))=m^2*(∑i : Fin n,v i*h i) :=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

end QuantitativeFollowup
