module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.AnisotropicMagnetization

@[expose] public section

/-! The actual incident pair mean at the independent endpoint is a true
product of finite rest and scalar field functions. This differentiates
that function identity in parameter space, including the last and old
coordinate directions, without differentiating an AE sample equality. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem incidentMean_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteIncidentMean_parameter_spatial (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (J : ℕ) (i : Fin n) (P v : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 incidentMean_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let M:=anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
    fderiv ℝ (anisotropicFiniteFeatureMean D s J
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))) P v=
      M (cavityRestParameterProjection n P)*parisiFSecond s B J (P (Sum.inr (Fin.last n)))*
        v (Sum.inr (Fin.last n))+
      parisiFDeriv s B J (P (Sum.inr (Fin.last n)))*fderiv ℝ M (cavityRestParameterProjection n P)
        (cavityRestParameterProjection n v) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 incidentMean_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let M:=anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
  let π:=cavityRestParameterProjection n
  let η:AnisotropicParameter (n+1)→L[ℝ]ℝ:=EuclideanSpace.proj (Sum.inr (Fin.last n))
  have hM:ContDiff ℝ ∞ M:=by
    have he:M=(fun Q=>anisotropicMagnetization Rest s J Q i):=by
      funext Q
      exact (anisotropicMagnetization_eq_spin_mean Rest s J Q i).symm
    rw [he]
    exact (boundedJets_anisotropicMagnetization_component Rest s J i).1
  have hdM:=((hM.differentiable (by simp) (π P)).hasFDerivAt).comp P π.hasFDerivAt
  have hdScalar:=((parisiF_C2_props s B J).1.2.1 (η P)).hasFDerivAt.comp P η.hasFDerivAt
  have hd:=hdM.mul hdScalar
  have he:(fun Q=>M (π Q)*parisiFDeriv s B J (η Q))=
      anisotropicFiniteFeatureMean D s J
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) :=by
    funext Q
    exact (cavityFiniteRowFeature_zero s n β ρ hβ hρ J i Q).symm
  change HasFDerivAt (fun Q=>M (π Q)*parisiFDeriv s B J (η Q)) _ P at hd
  rw [he] at hd
  rw [hd.fderiv]
  dsimp only [M,π,η,Rest,B]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,fderiv_eq_deriv_mul,
    Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply]
  ring

private theorem incidentMean_rest_last (n : ℕ) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) (Fin.last n))=0 :=by
  ext j
  cases j <;> simp [cavityRestParameterProjection,anisotropicCoordinateDirection,
    anisotropicFieldInjection,EuclideanSpace.single_apply]

private theorem incidentMean_last_last (n : ℕ) :
    anisotropicCoordinateDirection (n+1) (Fin.last n) (Sum.inr (Fin.last n))=1 :=by
  simp [anisotropicCoordinateDirection,anisotropicFieldInjection,EuclideanSpace.single_apply]

theorem cavityFiniteIncidentMean_last_parameter_spatial (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (J : ℕ) (i : Fin n) (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 incidentMean_zero_mem
    fderiv ℝ (anisotropicFiniteFeatureMean D s J
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n))=
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s J
        (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P)*
      parisiFSecond s (followupCavityScalarBeta n β ρ) J (P (Sum.inr (Fin.last n))) :=by
  dsimp only
  rw [cavityFiniteIncidentMean_parameter_spatial s n β ρ hβ hρ J i P]
  simp only [incidentMean_rest_last,incidentMean_last_last,map_zero,mul_one,mul_zero,add_zero]

end QuantitativeFollowup
