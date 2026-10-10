module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeRowSpatial
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeLinearity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteIncidentMeanSpatial

@[expose] public section

/-! The full incident-coordinate susceptibility derivative is averaged
before the literal finite free integral. Both the current right CDF and
the strict-future differential survive, including all repeated charges. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem pairAverage_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

private theorem average_fderiv {E I : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype I] (F : I→E→ℝ) (C : ℝ) (x v : E)
    (hF : ∀i,DifferentiableAt ℝ (F i) x) :
    fderiv ℝ (fun y=>(∑i,F i y)/C) x v=(∑i,fderiv ℝ (F i) x v)/C :=by
  have hsum:HasFDerivAt (fun y=>∑i,F i y) (∑i,fderiv ℝ (F i) x) x:=
    HasFDerivAt.fun_sum (fun i _=>(hF i).hasFDerivAt)
  have hd:=hsum.mul_const C⁻¹
  have he:(fun y=>(∑i,F i y)/C)=(fun y=>(∑i,F i y)*C⁻¹):=by
    funext y
    exact div_eq_mul_inv _ _
  rw [he,hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    smul_eq_mul,div_eq_mul_inv]
  ring

theorem cavityFinitePairSecond_average_free_spatial
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (P v : AnisotropicParameter (n+1)) :
    let q:=scalarSchemeTransportNode s (k+2-J)
    let e:=fun i : Fin n=>anisotropicOrderedCoupling i.castSucc (Fin.last n)
    (∑i : Fin n,fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q (e i)) P v)/(n:ℝ)=
      -2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*
        (∑i : Fin n,anisotropicFiniteFeatureMean D s J (anisotropicPairFeature (e i)) P*
          fderiv ℝ (anisotropicFiniteFeatureMean D s J (anisotropicPairFeature (e i))) P v)/(n:ℝ)-
      ∫r,if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
        cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
          (anisotropicPairFeature (e i)) r)/(n:ℝ)) P v else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  dsimp only
  let q:=scalarSchemeTransportNode s (k+2-J)
  let e:=fun i : Fin n=>anisotropicOrderedCoupling i.castSucc (Fin.last n)
  let F:=fun (i : Fin n) (r : Paper.Overlap) (Q : AnisotropicParameter (n+1))=>
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q) (anisotropicPairFeature (e i)) r
  have hF (i : Fin n) (r : Paper.Overlap):DifferentiableAt ℝ (F i r) P:=
    (contDiff_cavityFiniteFutureSquare_parameter D s J (anisotropicPairFeature (e i)) r).differentiable (by simp) P
  have he (r : Paper.Overlap):
      fderiv ℝ (fun Q=>(∑i : Fin n,F i r Q)/(n:ℝ)) P v=
        (∑i : Fin n,fderiv ℝ (F i r) P v)/(n:ℝ):=
    average_fderiv (fun i=>F i r) (n:ℝ) P v (fun i=>hF i r)
  have hint :
      (∑i : Fin n,∫r,if q<r then fderiv ℝ (F i r) P v else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)/(n:ℝ)=
      ∫r,if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,F i r Q)/(n:ℝ)) P v else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
    rw [←integral_cavityFiniteFree_finset_sum Finset.univ s a ha has hq,
      ←integral_div]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      by_cases hr:q<r
      · simp only [if_pos hr,he]
      · simp only [if_neg hr,Finset.sum_const_zero,zero_div]
  simp_rw [cavityFinitePairSecond_free_parameter_spatial D s J hJ a ha has hq]
  rw [Finset.sum_sub_distrib]
  simp only [mul_assoc,←Finset.mul_sum]
  rw [sub_div]
  dsimp only [F,q,e] at hint
  rw [hint]

theorem cavityFinitePairSecond_average_last_current
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 pairAverage_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let q:=scalarSchemeTransportNode s (k+2-J)
    let M:=fun i : Fin n=>anisotropicFiniteFeatureMean Rest s J
      (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P)
    let v:=anisotropicCoordinateDirection (n+1) (Fin.last n)
    (∑i : Fin n,fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P v)/(n:ℝ)=
      -2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*
        parisiFDeriv s B J (P (Sum.inr (Fin.last n)))*
        parisiFSecond s B J (P (Sum.inr (Fin.last n)))*((∑i : Fin n,(M i)^2)/(n:ℝ))-
      ∫r,if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
        cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)) P v
        else 0 ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  dsimp only
  rw [cavityFinitePairSecond_average_free_spatial _ s J hJ a ha has hq]
  simp_rw [cavityFiniteRowFeature_zero,cavityFiniteIncidentMean_last_parameter_spatial]
  have hs (m c : ℝ) (M : Fin n→ℝ):
      (∑i : Fin n,(M i*m)*(M i*c))=m*c*(∑i : Fin n,(M i)^2):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

end QuantitativeFollowup
