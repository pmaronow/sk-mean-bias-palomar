module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterCenteringIntegral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterHistoryScores
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterHessianScore

@[expose] public section

/-! The actual finite physical response in raw Stieltjes score form. The
root and zero-variance charges remain literal, and the genuine second
normalizer correction has been removed by the proved centered integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem cavityRaw_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

private theorem hessian_eq_directional_second {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E→ℝ) (hF : ContDiff ℝ ∞ F) (x K : E) :
    exponentialDensityHessian F x K K=fderiv ℝ (fun Q=>fderiv ℝ F Q K) x K :=by
  rw [(hasFDerivAt_exponential_directional_field F (hF.of_le (by simp)) x K).fderiv,
    ContinuousLinearMap.flip_apply]

def cavityFixedRowRawScore (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) : ℝ :=
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  K p.2.2-∑r,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
    fderiv ℝ (fun Q=>cascadePosteriorStieltjesPotential (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) (k+1) p.2.1 r
      (Q+anisotropicRootEnergyMap D p.1)) 0 K

def cavityFixedRowRawSecond (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) : ℝ :=
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  ∑r,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
    fderiv ℝ (fun Q=>fderiv ℝ (fun B=>cascadePosteriorStieltjesPotential
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      (k+1) p.2.1 r (B+anisotropicRootEnergyMap D p.1)) Q K) 0 K

def cavityFixedRowRawResponseIntegrand (D : AnisotropicSpinModel (n+1))
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
  let score:=cavityFixedRowRawScore D s a i p
  exponentialDensityHessian F 0 K K*(G 0-v)+(F 0-c)*exponentialDensityHessian G 0 K K+
    2*fderiv ℝ F 0 K*fderiv ℝ G 0 K+
    2*score*(fderiv ℝ F 0 K*(G 0-v)+(F 0-c)*fderiv ℝ G 0 K)+
    (F 0-c)*(G 0-v)*(score^2-cavityFixedRowRawSecond D s a i p)

private theorem cavityFixedRowLogScore_eq_raw (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityRaw_zero_mem
    fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
      (anisotropicRootEnergyMap D) Q p) 0 (anisotropicPairFeature (followupCavityIncidentIndex i))=
        cavityFixedRowRawScore D s a i p :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityRaw_zero_mem
  have hs:=fderiv_cavityOuterPosteriorLogDensity_stieltjes
    (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) a (k+1) (anisotropicRootEnergyMap D) 0
    (anisotropicPairFeature (followupCavityIncidentIndex i)) p
  dsimp only [cavityOuterPosteriorScore] at hs
  rw [cavityFixedRowOuter_logNormalizer_first_zero s n β ρ hβ hρ a i] at hs
  simpa only [cavityFixedRowRawScore,sub_zero] using hs

private theorem cavityFixedRowLogSecond_eq_raw (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
    exponentialDensityHessian (fun Q=>cavityOuterPosteriorLogDensity
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      a (k+2) (anisotropicRootEnergyMap D) Q p) 0 K K=
      -cavityFixedRowRawSecond D s a i p-
      exponentialDensityHessian (fun Q=>Real.log (cavityOuterPosteriorNormalizer
        (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        a (k+2) (anisotropicRootEnergyMap D) Q)) 0 K K :=by
  dsimp only
  simpa only [cavityFixedRowRawSecond] using
    hessian_cavityOuterPosteriorLogDensity_stieltjes_expanded
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
      a (k+1) (anisotropicRootEnergyMap D) 0
      (anisotropicPairFeature (followupCavityIncidentIndex i)) p

theorem cavityFixedRowRawResponseIntegrand_eq_withoutNormalizer (s : RSBScheme k)
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityRaw_zero_mem
    cavityFixedRowRawResponseIntegrand D s a d i p=
      cavityFixedRowOuterResponseWithoutNormalizer D s a d i p :=by
  dsimp only
  have hs:=cavityFixedRowLogScore_eq_raw s n β ρ hβ hρ a i p
  have hss:=cavityFixedRowLogSecond_eq_raw
    (followupCavitySpinModel n β ρ hβ hρ 0 cavityRaw_zero_mem) s a i p
  dsimp only [cavityFixedRowRawResponseIntegrand,cavityFixedRowOuterResponseWithoutNormalizer,
    cavityFixedRowOuterResponseIntegrand,cavityFixedRowOuterCenteredProduct]
  rw [hs,hss]
  ring

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_raw_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityRaw_zero_mem
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n:=n) β ρ hβ hρ s a d) (Icc (0:ℝ) 1) 0=
      followupCavityAlpha n β ρ/(2*(n:ℝ))*
        ∑i : Fin n,∫p,cavityFixedRowRawResponseIntegrand D s a d i p
          ∂cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
            (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0 :=by
  dsimp only
  rw [derivWithin_cavityFixedRowPhysicalCurveCovariance_outer_integral hn β ρ hβ hρ s a d hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [cavityFixedRowRawResponseIntegrand_eq_withoutNormalizer s n β ρ hβ hρ a d hd i]
  exact (cavityFixedRowOuterResponseWithoutNormalizer_integrable_eq s n β ρ hβ hρ a d hd i).2.symm

end QuantitativeFollowup
