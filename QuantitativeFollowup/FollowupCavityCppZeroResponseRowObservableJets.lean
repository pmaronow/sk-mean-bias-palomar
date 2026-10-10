module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFeatureJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.AnisotropicMagnetization

@[expose] public section

/-! Literal incident-row derivative of the isolated spin mean. The row
potential response is the actual product Vi; differentiating that genuine
identity along the last field gives Mi times the scalar Hessian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem restProjection_lastDirection (n : ℕ) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) (Fin.last n))=0 :=by
  ext i
  cases i <;> simp [cavityRestParameterProjection,anisotropicCoordinateDirection,
    anisotropicFieldInjection,EuclideanSpace.single_apply]

private theorem lastDirection_last (n : ℕ) :
    anisotropicCoordinateDirection (n+1) (Fin.last n) (Sum.inr (Fin.last n))=1 :=by
  simp [anisotropicCoordinateDirection,anisotropicFieldInjection,EuclideanSpace.single_apply]

theorem cavityFiniteLastFeature_row_first (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
      (WithLp.toLp 2 (fun σ : Configuration (n+1)=>Paper.spinSign (σ (Fin.last n))))) (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
    anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
      (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P)*
    parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U:=finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
  let H:=anisotropicEnergyMap D P
  let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
  let b : FiniteStateField (Configuration (n+1)):=WithLp.toLp 2
    (fun σ : Configuration (n+1)=>Paper.spinSign (σ (Fin.last n)))
  let delta:=anisotropicCoordinateDirection (n+1) (Fin.last n)
  have hb : anisotropicEnergyMap D delta=b :=by
    ext σ
    exact anisotropicTerminalLinear_coordinate D σ (Fin.last n)
  have hrest : cavityRestParameterProjection n delta=0:=restProjection_lastDirection n
  have hlast : delta (Sum.inr (Fin.last n))=1:=lastDirection_last n
  let Mi:=anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
    (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P)
  have he : (fun t : ℝ=>fderiv ℝ U (H+t • b) K)=
      fun t=>Mi*parisiFDeriv s (followupCavityScalarBeta n β ρ) j
        (P (Sum.inr (Fin.last n))+t) :=by
    funext t
    have hv:=cavityFiniteRowFeature_zero s n β ρ hβ hρ j i (P+t • delta)
    rw [←anisotropicFinitePair_energy_first] at hv
    have heH : anisotropicEnergyMap D (P+t • delta)=H+t • b :=by
      rw [map_add,map_smul,hb]
    have hex : (P+t • delta) (Sum.inr (Fin.last n))=P (Sum.inr (Fin.last n))+t :=by
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hlast,mul_one]
    change fderiv ℝ U (anisotropicEnergyMap D (P+t • delta)) K=_ at hv
    rw [heH,hex] at hv
    simp only [map_add,map_smul,hrest,smul_zero,add_zero] at hv
    exact hv
  have hU:=contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
  have hDK : ContDiff ℝ ∞ (fun Q=>fderiv ℝ U Q K):=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hd:=((hDK.differentiable (by simp) H).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0:ℝ) H).add ((hasDerivAt_id (0:ℝ)).smul_const b)) (by simp)
  have hs:=((parisiF_C2_props s (followupCavityScalarBeta n β ρ) j).1.2.1
    (P (Sum.inr (Fin.last n)))).comp_of_eq 0
      ((hasDerivAt_const (0:ℝ) (P (Sum.inr (Fin.last n)))).add (hasDerivAt_id (0:ℝ))) (by simp)
  have hl : HasDerivAt (fun t : ℝ=>fderiv ℝ U (H+t • b) K)
      (fderiv ℝ (fun Q=>fderiv ℝ U Q K) H b) 0 := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] using hd
  rw [he] at hl
  have hr : HasDerivAt (fun t : ℝ=>Mi*parisiFDeriv s (followupCavityScalarBeta n β ρ) j
      (P (Sum.inr (Fin.last n))+t))
      (Mi*parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))) 0:=by
    simpa using hs.const_mul Mi
  change fderiv ℝ (fun Q=>fderiv ℝ U Q b) H K=_
  rw [cavity_directional_second_symmetry U hU H b K]
  exact hl.unique hr

end QuantitativeFollowup
