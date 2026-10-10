module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteObservableGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeDensityGrouping

@[expose] public section

/-! All five genuine posterior response terms are grouped in the actual
independent finite model. The density contribution uses the atom-exact
right-CDF formula; no field, score, or mixed term is omitted. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ} {R : Type*} [Fintype R]
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem fiveGrouping_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

def cavityFiniteLastObservableGroupedValue (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (P : AnisotropicParameter (n+1))
    (w : R→ℝ) (jr : R→ℕ) (Pr : R→AnisotropicParameter (n+1))
    (σ : Configuration (n+1)) (Abar : ℝ) : ℝ :=
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 fiveGrouping_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let m:=parisiFDeriv s B j (P (Sum.inr (Fin.last n)))
  let h:=parisiFSecond s B j (P (Sum.inr (Fin.last n)))
  let M:=fun i=>anisotropicFiniteFeatureMean Rest s j (fun τ=>Paper.spinSign (τ i))
    (cavityRestParameterProjection n P)
  let Mr:=fun r i=>anisotropicFiniteFeatureMean Rest s (jr r) (fun τ=>Paper.spinSign (τ i))
    (cavityRestParameterProjection n (Pr r))
  let mr:=fun r=>parisiFDeriv s B (jr r) (Pr r (Sum.inr (Fin.last n)))
  let E:=fun i : Fin n=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
    (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n))
  Abar*(h^2*(∑i,(M i)^2)/(n:ℝ)+m*(∑i,E i)/(n:ℝ)+
    2*m*h*Paper.spinSign (σ (Fin.last n))*(∑i,Paper.spinSign (σ i.castSucc)*M i)/(n:ℝ)-
    2*m*h*(∑r,w r*mr r*(∑i,M i*Mr r i))/(n:ℝ))

def cavityFiniteRestObservableGroupedValue (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (P : AnisotropicParameter (n+1))
    (w : R→ℝ) (jr : R→ℕ) (Pr : R→AnisotropicParameter (n+1))
    (σ : Configuration (n+1)) (fbar : ℝ) : ℝ :=
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 fiveGrouping_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let m:=parisiFDeriv s B j (P (Sum.inr (Fin.last n)))
  let h:=parisiFSecond s B j (P (Sum.inr (Fin.last n)))
  let M:=fun i=>anisotropicFiniteFeatureMean Rest s j (fun τ=>Paper.spinSign (τ i))
    (cavityRestParameterProjection n P)
  let H:=fun l i=>fderiv ℝ (anisotropicFiniteFeatureMean Rest s j
    (fun τ=>Paper.spinSign (τ i))) (cavityRestParameterProjection n P)
      (anisotropicCoordinateDirection n l)
  let E:=fun (i l : Fin n)=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
    (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) l.castSucc)
  let Mr:=fun r i=>anisotropicFiniteFeatureMean Rest s (jr r) (fun τ=>Paper.spinSign (τ i))
    (cavityRestParameterProjection n (Pr r))
  let mr:=fun r=>parisiFDeriv s B (jr r) (Pr r (Sum.inr (Fin.last n)))
  fbar*m^2*(∑i,∑l,H l i^2)/(n:ℝ)^2+
    fbar*(∑l,M l*(∑i,E i l))/(n:ℝ)^2+
    4*m^2*h*(∑i,M i*(∑l,M l*H l i))/(n:ℝ)^2+
    2*fbar*m*Paper.spinSign (σ (Fin.last n))*(∑i,Paper.spinSign (σ i.castSucc)*
      (∑l,M l*H l i))/(n:ℝ)^2-
    2*fbar*m*(∑r,w r*mr r*(∑i,Mr r i*(∑l,M l*H l i)))/(n:ℝ)^2

private theorem fiveGrouping_hessian_directional
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E→ℝ) (hF : ContDiff ℝ ∞ F) (Q K : E) :
    exponentialDensityHessian F Q K K=fderiv ℝ (fun x=>fderiv ℝ F x K) Q K :=by
  rw [(hasFDerivAt_exponential_directional_field F (hF.of_le (by simp)) Q K).fderiv,
    ContinuousLinearMap.flip_apply]

theorem cavityFiniteFiveResponse_group (s : RSBScheme k) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (j : ℕ) (P : AnisotropicParameter (n+1)) (w : R→ℝ) (jr : R→ℕ)
    (hjr : ∀r,jr r≤k+2) (Pr : R→AnisotropicParameter (n+1))
    (σ : Configuration (n+1)) (Fbar Abar : ℝ) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 fiveGrouping_zero_mem
    let Q:=anisotropicEnergyMap D P
    let f:=cavityFixedRowLastFieldSquare D s j
    let g:=cavityFixedRowRestFieldSquare D s j
    let K:=fun i : Fin n=>anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    let Score:=fun i : Fin n=>Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
      ∑r,w r*anisotropicFiniteFeatureMean D s (jr r) (K i) (Pr r)
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,(
      exponentialDensityHessian f Q (K i) (K i)*Abar+
      Fbar*exponentialDensityHessian g Q (K i) (K i)+
      2*fderiv ℝ f Q (K i)*fderiv ℝ g Q (K i)+
      2*Score i*(fderiv ℝ f Q (K i)*Abar+Fbar*fderiv ℝ g Q (K i))+
      Fbar*Abar*(Score i^2-∑r,w r*anisotropicFinitePairSecond D s (jr r) (Pr r)
        (anisotropicOrderedCoupling i.castSucc (Fin.last n)))))=
      cavityFiniteLastObservableGroupedValue s n β ρ hβ hρ j P w jr Pr σ Abar+
      cavityFiniteRestObservableGroupedValue s n β ρ hβ hρ j P w jr Pr σ Fbar+
      cavityFiniteIncidentFreeDensityGroupedValue s n β ρ hβ hρ a w jr Pr σ Fbar Abar :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 fiveGrouping_zero_mem
  let f:=cavityFixedRowLastFieldSquare D s j
  let g:=cavityFixedRowRestFieldSquare D s j
  let Q:=anisotropicEnergyMap D P
  let K:=fun i : Fin n=>anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
  let Score:=fun i : Fin n=>Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
    ∑r,w r*anisotropicFiniteFeatureMean D s (jr r) (K i) (Pr r)
  have hsplit (i : Fin n):
      exponentialDensityHessian f Q (K i) (K i)*Abar+
      Fbar*exponentialDensityHessian g Q (K i) (K i)+
      2*fderiv ℝ f Q (K i)*fderiv ℝ g Q (K i)+
      2*Score i*(fderiv ℝ f Q (K i)*Abar+Fbar*fderiv ℝ g Q (K i))+
      Fbar*Abar*(Score i^2-∑r,w r*anisotropicFinitePairSecond D s (jr r) (Pr r)
        (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      (fderiv ℝ (fun x=>fderiv ℝ f x (K i)) Q (K i)*Abar+
        2*Score i*fderiv ℝ f Q (K i)*Abar)+
      (Fbar*fderiv ℝ (fun x=>fderiv ℝ g x (K i)) Q (K i)+
        2*fderiv ℝ f Q (K i)*fderiv ℝ g Q (K i)+
        2*Score i*Fbar*fderiv ℝ g Q (K i))+
      Fbar*Abar*(Score i^2-∑r,w r*anisotropicFinitePairSecond D s (jr r) (Pr r)
        (anisotropicOrderedCoupling i.castSucc (Fin.last n))) :=by
    rw [fiveGrouping_hessian_directional f (boundedJets_cavityFixedRowLastFieldSquare D s j).1,
      fiveGrouping_hessian_directional g (boundedJets_cavityFixedRowRestFieldSquare D s j).1]
    ring
  change ((n:ℝ)⁻¹/2)*(∑i : Fin n,(
    exponentialDensityHessian f Q (K i) (K i)*Abar+
    Fbar*exponentialDensityHessian g Q (K i) (K i)+
    2*fderiv ℝ f Q (K i)*fderiv ℝ g Q (K i)+
    2*Score i*(fderiv ℝ f Q (K i)*Abar+Fbar*fderiv ℝ g Q (K i))+
    Fbar*Abar*(Score i^2-∑r,w r*anisotropicFinitePairSecond D s (jr r) (Pr r)
      (anisotropicOrderedCoupling i.castSucc (Fin.last n)))))=_
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,mul_add,mul_add]
  simp only [D,Q,f,g,K,Score]
  rw [cavityFiniteLastObservable_group s hn β ρ hβ hρ j P w jr Pr σ Abar,
    cavityFiniteRestObservable_group s hn β ρ hβ hρ j P w jr Pr σ Fbar,
    cavityFiniteIncidentFreeDensity_group s hn β ρ hβ hρ a ha has hq w jr hjr Pr σ Fbar Abar]
  rfl

end QuantitativeFollowup
