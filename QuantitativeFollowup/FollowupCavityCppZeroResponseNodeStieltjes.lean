module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureSelector
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowSquaredJets

@[expose] public section

/-! The true incident-row Hessian has the right-CDF current coefficient
and the strict future at every literal finite node, before expectations or
row/spatial differentiation. This retains zero and repeated cells. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteIncidentRowSecond_free_stieltjes (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (P : AnisotropicParameter (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    anisotropicFinitePairSecond D s J P (anisotropicOrderedCoupling i.castSucc (Fin.last n))=
      1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
        (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s J
          (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n P)*
          parisiFDeriv s (followupCavityScalarBeta n β ρ) J (P (Sum.inr (Fin.last n))))^2-
      ∫r,if scalarSchemeTransportNode s (k+2-J)<r then
        cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P) K r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let e:=anisotropicOrderedCoupling i.castSucc (Fin.last n)
  let K:=anisotropicPairFeature e
  have hK:∀τ : Configuration (n+1),K τ*K τ=1:=by
    intro τ
    exact anisotropicPairFeature_binary e τ
  have he:=cavityFiniteBinaryFeature_node_free_stieltjes D s J hJ a ha has hq
    (anisotropicEnergyMap D P) K hK
  rw [←anisotropicFinitePairSecond_eq_energy D s J P e] at he
  change anisotropicFinitePairSecond D s J P e=
    1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
      (cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J K (anisotropicEnergyMap D P))^2-
      ∫r,if scalarSchemeTransportNode s (k+2-J)<r then
        cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P) K r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a at he
  rw [cavityFiniteEnergyFeatureMean_at_parameter] at he
  simpa only [D,e,K,cavityFiniteRowFeature_zero] using he

end QuantitativeFollowup
