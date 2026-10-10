module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNodeStieltjes
public import QuantitativeFollowup.FollowupCavityCppZeroResponseDensityAlgebra

@[expose] public section

/-! The density-score part of the actual independent-endpoint response,
expanded after the true atom-exact Stieltjes merger. The current coefficient
is the right CDF at each original node, including repeated nodes. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ} {R : Type*} [Fintype R]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def cavityFiniteIncidentFreeDensityFuture (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (j : ℕ)
    (i : Fin n) (P : AnisotropicParameter (n+1)) : ℝ :=
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  ∫r,if scalarSchemeTransportNode s (k+2-j)<r then
    cavityFiniteFutureSquare D s j (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r else 0
    ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a

def cavityFiniteIncidentFreeDensityGroupedValue (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (w : R→ℝ) (j : R→ℕ)
    (P : R→AnisotropicParameter (n+1)) (σ : Configuration (n+1))
    (Fbar Abar : ℝ) : ℝ :=
  let B:=followupCavityScalarBeta n β ρ
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let m:=fun r=>parisiFDeriv s B (j r) (P r (Sum.inr (Fin.last n)))
  let M:=fun r i=>anisotropicFiniteFeatureMean D s (j r)
    (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n (P r))
  Fbar*Abar/2*(1-∑r,w r)-
    Fbar*Abar*(∑r,w r*Paper.spinSign (σ (Fin.last n))*m r*
      ((n:ℝ)⁻¹*∑i,Paper.spinSign (σ i.castSucc)*M r i))+
    Fbar*Abar/2*(∑r,∑l,w r*w l*m r*m l*((n:ℝ)⁻¹*∑i,M r i*M l i))+
    Fbar*Abar/2*(∑r,w r*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
      (scalarSchemeTransportNode s (k+2-j r))*(m r)^2*((n:ℝ)⁻¹*∑i,(M r i)^2))+
    Fbar*Abar/2*(∑r,w r*((n:ℝ)⁻¹*∑i,
      cavityFiniteIncidentFreeDensityFuture s n β ρ hβ hρ a (j r) i (P r)))

theorem cavityFiniteIncidentFreeDensity_group (s : RSBScheme k) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (w : R→ℝ) (j : R→ℕ) (hj : ∀r,j r≤k+2)
    (P : R→AnisotropicParameter (n+1)) (σ : Configuration (n+1)) (Fbar Abar : ℝ) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,(Fbar*Abar*
      ((Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
        ∑r,w r*anisotropicFiniteFeatureMean D s (j r)
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) (P r))^2-
      ∑r,w r*anisotropicFinitePairSecond D s (j r) (P r)
        (anisotropicOrderedCoupling i.castSucc (Fin.last n)))))=
      cavityFiniteIncidentFreeDensityGroupedValue s n β ρ hβ hρ a w j P σ Fbar Abar :=by
  dsimp only
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  let B:=followupCavityScalarBeta n β ρ
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let m:=fun r=>parisiFDeriv s B (j r) (P r (Sum.inr (Fin.last n)))
  let M:=fun r i=>anisotropicFiniteFeatureMean D s (j r)
    (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n (P r))
  let c:=fun r=>Paper.parisiCDF (Paper.parisiSchemeMeasure s)
    (scalarSchemeTransportNode s (k+2-j r))
  let f:=fun r i=>cavityFiniteIncidentFreeDensityFuture s n β ρ hβ hρ a (j r) i (P r)
  have he (r : R) (i : Fin n):
      anisotropicFinitePairSecond (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩)
        s (j r) (P r) (anisotropicOrderedCoupling i.castSucc (Fin.last n))=
      cavityDensityAlgebraSecond c m M f r i :=by
    rw [cavityFiniteIncidentRowSecond_free_stieltjes s n β ρ hβ hρ (j r) (hj r)
      a ha has hq]
    dsimp only [cavityDensityAlgebraSecond,c,m,M,f,B,D,cavityFiniteIncidentFreeDensityFuture]
  simp_rw [cavityFiniteRowFeature_zero,he]
  have hs (i : Fin n) :
      Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
        ∑r,w r*(M r i*m r)=
      cavityDensityAlgebraScore w m M (fun i=>Paper.spinSign (σ i.castSucc))
        (Paper.spinSign (σ (Fin.last n))) i :=by
    unfold cavityDensityAlgebraScore
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  change ((n:ℝ)⁻¹/2)*(∑i : Fin n,(Fbar*Abar*
    ((Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
      ∑r,w r*(M r i*m r))^2-
      ∑r,w r*cavityDensityAlgebraSecond c m M f r i)))=_
  simp_rw [hs]
  simpa only [Fintype.card_fin,cavityFiniteIncidentFreeDensityGroupedValue,B,D,m,M,c,f] using
    (cavityDensityAlgebra_second_density_group w c m M f
      (fun i=>Paper.spinSign (σ i.castSucc)) (Paper.spinSign (σ (Fin.last n))) Fbar Abar
      (Paper.spinSign_sq _) (fun i=>Paper.spinSign_sq _))

end QuantitativeFollowup
