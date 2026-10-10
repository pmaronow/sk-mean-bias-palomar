module
public import QuantitativeFollowup.FollowupCavityFixedRowPhysicalDerivativeCheckpoint
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowCentering

@[expose] public section

/-! Genuine initial response of the original physical curve as a complete
outer-posterior integral. Both observables move with the incident row.
Reflection removes the two actual mean-gradient corrections. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowOuterResponseIntegrand (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) : ℝ :=
  let R:=anisotropicRootEnergyMap D
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  let f:=cavityFixedRowLastFieldSquare D s d
  let g:=cavityFixedRowRestFieldSquare D s d
  let F:=fun Q=>f (Q+R p.1+W p.2.1)
  let G:=fun Q=>g (Q+R p.1+W p.2.1)
  let c:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) R f W 0
  let v:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) R g W 0
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  let logD:=fun Q=>cavityOuterPosteriorLogDensity (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) R Q p
  exponentialDensityHessian F 0 K K*(G 0-v)+(F 0-c)*exponentialDensityHessian G 0 K K+
    2*fderiv ℝ F 0 K*fderiv ℝ G 0 K+
    2*fderiv ℝ logD 0 K*(fderiv ℝ F 0 K*(G 0-v)+(F 0-c)*fderiv ℝ G 0 K)+
    (F 0-c)*(G 0-v)*(exponentialDensityHessian logD 0 K K+(fderiv ℝ logD 0 K)^2)

theorem cavityFixedRowOuterCovariance_hessian_eq_integral (s : RSBScheme k)
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    exponentialDensityHessian (cavityFixedRowOuterCovariance D s a d) 0
      (anisotropicPairFeature (followupCavityIncidentIndex i))
      (anisotropicPairFeature (followupCavityIncidentIndex i))=
      ∫p,cavityFixedRowOuterResponseIntegrand D s a d i p
        ∂cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0 :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  have hc:=contDiff_cavityFixedRowOuterCovariance D s a d
  have he:=congrArg (fun T : FiniteStateField (Configuration (n+1))→L[ℝ]ℝ=>T K)
    ((hasFDerivAt_exponential_directional_field _ (hc.of_le (by simp)) 0 K).fderiv)
  simp only [ContinuousLinearMap.flip_apply] at he
  rw [←he]
  change fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorCovariance _ _ _ _ _ _ _ _ _) Q K) 0 K=_
  rw [second_fderiv_cavityOuterPosteriorCovariance_expanded _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s))
    _ a (k+2) _ _ _ (boundedJets_cavityFixedRowLastFieldSquare D s d)
    (boundedJets_cavityFixedRowRestFieldSquare D s d) _ 0 K]
  rw [cavityFixedRowOuter_last_mean_first_zero s n β ρ hβ hρ a d hd i,
    cavityFixedRowOuter_rest_mean_first_zero s n β ρ hβ hρ a d hd i]
  simp only [mul_zero,sub_zero]
  rfl

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_outer_integral
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n:=n) β ρ hβ hρ s a d) (Icc (0:ℝ) 1) 0=
      followupCavityAlpha n β ρ/(2*(n:ℝ))*
        ∑i : Fin n,∫p,cavityFixedRowOuterResponseIntegrand D s a d i p
          ∂cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
            (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0 :=by
  dsimp only
  rw [derivWithin_cavityFixedRowPhysicalCurveCovariance_zero hn β ρ hβ hρ s a d hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change exponentialDensityHessian _ 0 _ _=_
  rw [cavityFixedRowCovariance_hessian_incident_zero _ s a d hd i]
  exact cavityFixedRowOuterCovariance_hessian_eq_integral s n β ρ hβ hρ a d hd i

end QuantitativeFollowup
