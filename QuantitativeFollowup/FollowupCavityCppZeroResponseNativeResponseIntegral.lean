module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeRawScores

@[expose] public section

/-! Actual initial physical response as an integral over the genuine native
marked path for a finite scheme. The complete retained-history law is used;
all score charges become actual free-Stieltjes feature responses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem responseIntegral_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

private theorem hessian_add_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E→ℝ) (B x K : E) :
    exponentialDensityHessian (fun Q=>f (Q+B)) x K K=
      exponentialDensityHessian f (x+B) K K :=by
  have he:fderiv ℝ (fun Q=>f (Q+B))=fun Q=>fderiv ℝ f (Q+B):=by
    funext Q
    exact fderiv_comp_add_right B
  unfold exponentialDensityHessian
  rw [he,fderiv_comp_add_right]

def rawFiveResponse {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E→ℝ) (c v : ℝ) (K Q : E) (score second : ℝ) : ℝ :=
  exponentialDensityHessian f Q K K*(g Q-v)+(f Q-c)*exponentialDensityHessian g Q K K+
    2*fderiv ℝ f Q K*fderiv ℝ g Q K+
    2*score*(fderiv ℝ f Q K*(g Q-v)+(f Q-c)*fderiv ℝ g Q K)+
    (f Q-c)*(g Q-v)*(score^2-second)

def cavityFixedRowHistoryRawResponse (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (i : Fin n)
    (p : FiniteHistory (FiniteStateField (Configuration (n+1))) (k+2)×Configuration (n+1)) : ℝ :=
  let R:=anisotropicRootEnergyMap D
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  let f:=cavityFixedRowLastFieldSquare D s d
  let g:=cavityFixedRowRestFieldSquare D s d
  let c:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R f W 0
  let v:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R g W 0
  rawFiveResponse f g c v (anisotropicPairFeature (followupCavityIncidentIndex i))
    (p.1 (Fin.ofNat (k+3) (k+2-d)))
    (cavityFixedRowHistoryRawScore D s a i p) (cavityFixedRowHistoryRawSecond D s a i p)

theorem cavityFixedRowRawResponseIntegrand_eq_history (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    cavityFixedRowRawResponseIntegrand D s a d i p=cavityFixedRowHistoryRawResponse D s a d i
      (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0 p) :=by
  have hi:Fin.ofNat (k+3) (k+2-d)=(⟨k+2-d,by omega⟩ : Fin (k+3)):=by
    apply Fin.ext
    change (k+2-d)%(k+3)=k+2-d
    rw [Nat.mod_eq_of_lt (by omega)]
  have hfield:(cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2)
      (anisotropicRootEnergyMap D) 0 p).1 (Fin.ofNat (k+3) (k+2-d))=
      0+anisotropicRootEnergyMap D p.1+
        cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d p.2.1 :=by
    rw [hi]
    dsimp only [cavityOuterHistoryMap]
    rw [cascadePosteriorHistory_eq_initial_add,cavityPosteriorLineFieldLinear_apply]
  rw [cavityFixedRowRawResponseIntegrand,cavityFixedRowHistoryRawResponse,hfield,
    cavityFixedRowRawScore_eq_history,cavityFixedRowRawSecond_eq_history]
  dsimp only [rawFiveResponse]
  have ht (f : FiniteStateField (Configuration (n+1))→ℝ):
      (fun Q=>f (Q+anisotropicRootEnergyMap D p.1+
        cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d p.2.1))=
      fun Q=>f (Q+(anisotropicRootEnergyMap D p.1+
        cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d p.2.1)):=by
    funext Q
    rw [add_assoc]
  simp_rw [ht,fderiv_comp_add_right,hessian_add_right]
  simp only [add_assoc]

theorem measurable_cavityFixedRowHistoryRawResponse (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (i : Fin n) :
    Measurable (cavityFixedRowHistoryRawResponse D s a d i) :=by
  let f:=cavityFixedRowLastFieldSquare D s d
  let g:=cavityFixedRowRestFieldSquare D s d
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  have hF:ContDiff ℝ ∞ f:=(boundedJets_cavityFixedRowLastFieldSquare D s d).1
  have hG:ContDiff ℝ ∞ g:=(boundedJets_cavityFixedRowRestFieldSquare D s d).1
  have hDF : ContDiff ℝ ∞ (fderiv ℝ f):=hF.fderiv_right (by simp)
  have hDG : ContDiff ℝ ∞ (fderiv ℝ g):=hG.fderiv_right (by simp)
  have hDDF : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)):=hDF.fderiv_right (by simp)
  have hDDG : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)):=hDG.fderiv_right (by simp)
  have hF1:Measurable (fun Q=>fderiv ℝ f Q K):=
    (hDF.clm_apply (contDiff_const (c:=K))).continuous.measurable
  have hG1:Measurable (fun Q=>fderiv ℝ g Q K):=
    (hDG.clm_apply (contDiff_const (c:=K))).continuous.measurable
  have hF2:Measurable (fun Q=>exponentialDensityHessian f Q K K):=
    ((hDDF.clm_apply (contDiff_const (c:=K))).clm_apply
      (contDiff_const (c:=K))).continuous.measurable
  have hG2:Measurable (fun Q=>exponentialDensityHessian g Q K K):=
    ((hDDG.clm_apply (contDiff_const (c:=K))).clm_apply
      (contDiff_const (c:=K))).continuous.measurable
  have hp:Measurable (fun p : FiniteHistory (FiniteStateField (Configuration (n+1))) (k+2)×
      Configuration (n+1)=>p.1 (Fin.ofNat (k+3) (k+2-d))):=
    (measurable_pi_apply _).comp measurable_fst
  have hf:=hF.continuous.measurable.comp hp
  have hg:=hG.continuous.measurable.comp hp
  have hf1:=hF1.comp hp
  have hg1:=hG1.comp hp
  have hf2:=hF2.comp hp
  have hg2:=hG2.comp hp
  have hs:=measurable_cavityFixedRowHistoryRawScore D s a i
  have hss:=measurable_cavityFixedRowHistoryRawSecond D s a i
  let R:=anisotropicRootEnergyMap D
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  let c:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R f W 0
  let v:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R g W 0
  have hfc:=hf.sub (measurable_const (a:=c))
  have hgv:=hg.sub (measurable_const (a:=v))
  unfold cavityFixedRowHistoryRawResponse rawFiveResponse
  exact ((((hf2.mul hgv).add (hfc.mul hg2)).add
    (((measurable_const (a:=(2:ℝ))).mul hf1).mul hg1)).add
    (((measurable_const (a:=(2:ℝ))).mul hs).mul
      ((hf1.mul hgv).add (hfc.mul hg1)))).add
        ((hfc.mul hgv).mul ((hs.pow_const 2).sub hss))

def cavityFixedRowNativeFiniteResponseIntegrand (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n)
    (p : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) : ℝ :=
  let R:=anisotropicRootEnergyMap D
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  let f:=cavityFixedRowLastFieldSquare D s d
  let g:=cavityFixedRowRestFieldSquare D s d
  let c:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R f W 0
  let v:=cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) R g W 0
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  let Q:=anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
    (anisotropicSchemeNode s (k+2-d) (by omega)) p.1)
  let score:=K p.2-∫r,anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r
    (followupCavityIncidentIndex i) p.1 ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let second:=∫r,anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r
    (followupCavityIncidentIndex i) p.1 ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  rawFiveResponse f g c v K Q score second

theorem cavityFixedRowHistoryRawResponse_at_native (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) (i : Fin n)
    (p : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    cavityFixedRowHistoryRawResponse D s a d i
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)=
      cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i p :=by
  rw [cavityFixedRowHistoryRawResponse,cavityFixedRowHistoryRawScore_at_native D s a ha has hq,
    cavityFixedRowHistoryRawSecond_at_native D s a ha has hq]
  have hi:Fin.ofNat (k+3) (k+2-d)=(⟨k+2-d,by omega⟩ : Fin (k+3)):=by
    apply Fin.ext
    change (k+2-d)%(k+3)=k+2-d
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hi]
  rfl

theorem integral_cavityFixedRowRawResponseIntegrand_eq_native (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    (∫p,cavityFixedRowRawResponseIntegrand D s a d i p
      ∂cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0)=
      ∫p,cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i p
        ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
  simp_rw [cavityFixedRowRawResponseIntegrand_eq_history D s a d hd i]
  rw [integral_cavityOuterPosteriorHistory_eq_native_scheme D s a _
    (measurable_cavityFixedRowHistoryRawResponse D s a d i)]
  apply integral_congr_ae
  exact .of_forall (cavityFixedRowHistoryRawResponse_at_native D s a ha has hq d hd i)

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_native_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 responseIntegral_zero_mem
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n:=n) β ρ hβ hρ s a d) (Icc (0:ℝ) 1) 0=
      followupCavityAlpha n β ρ/(2*(n:ℝ))*
        ∑i : Fin n,∫p,cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i p
          ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
  dsimp only
  rw [derivWithin_cavityFixedRowPhysicalCurveCovariance_raw_response hn β ρ hβ hρ s a d hd]
  congr 1
  exact Finset.sum_congr rfl fun i _=>
    integral_cavityFixedRowRawResponseIntegrand_eq_native _ s a ha has hq d hd i

end QuantitativeFollowup
