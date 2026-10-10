module
public import QuantitativeFollowup.FollowupCavityFixedRowHeatFactories
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterCovarianceExpansion

@[expose] public section

/-! The genuine retained-node covariance is the complete outer posterior
covariance restricted to the deterministic incident-row subspace. Its row
Hessian is therefore the actual outer Hessian in the incident-feature
directions, with every retained-field observable kept. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem smooth_outer_covariance
    {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    ContDiff ℝ ∞ (cavityOuterPosteriorCovariance V a L s N R f g W) :=by
  have he:cavityOuterPosteriorCovariance V a L s N R f g W=
      fun Q=>cavityOuterPosteriorMean V a L s N R (fun x=>f x*g x) W Q-
        cavityOuterPosteriorMean V a L s N R f W Q*cavityOuterPosteriorMean V a L s N R g W Q:=by
    funext Q
    simpa only [sub_zero] using
      cavityOuterPosteriorCovariance_eq_centeredMean V a ha L s N R f g hf hg W 0 0 Q
  rw [he]
  exact (contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R _ (hf.mul hg) W).sub
    ((contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R f hf W).mul
      (contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R g hg W))

private theorem hessian_comp_linear {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F→ℝ) (hf : ContDiff ℝ ∞ f) (B : E→L[ℝ]F) (x e : E) :
    exponentialDensityHessian (f ∘ B) x e e=
      exponentialDensityHessian f (B x) (B e) (B e) :=by
  have hc:ContDiff ℝ ∞ (f ∘ B):=hf.comp B.contDiff
  have he:(fun y=>fderiv ℝ (f ∘ B) y e)=fun y=>fderiv ℝ f (B y) (B e):=by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) (B y)) B.differentiableAt,
      ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
  have hd:ContDiff ℝ ∞ (fun y=>fderiv ℝ f y (B e)):=
    (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c:=B e))
  have hh:=congrArg (fun D : E→L[ℝ]ℝ=>D e)
    ((hasFDerivAt_exponential_directional_field (f ∘ B) (hc.of_le (by simp)) x e).fderiv)
  simp only [ContinuousLinearMap.flip_apply] at hh
  rw [←hh,he]
  change fderiv ℝ ((fun y=>fderiv ℝ f y (B e)) ∘ B) x e=_
  rw [fderiv_comp x (hd.differentiable (by simp) (B x)) B.differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
    (hasFDerivAt_exponential_directional_field f (hf.of_le (by simp)) (B x) (B e)).fderiv,
    ContinuousLinearMap.flip_apply]

def cavityFixedRowOuterCovariance (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) : FiniteStateField (QuantitativePaper.Configuration (n+1))→ℝ :=
  cavityOuterPosteriorCovariance (fun _ : QuantitativePaper.Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
    (cavityFixedRowLastFieldSquare D s d) (cavityFixedRowRestFieldSquare D s d)
    (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d)

theorem cavityFixedRowCovariance_eq_outer (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    cavityFixedRowCovariance D s a d=cavityFixedRowOuterCovariance D s a d ∘ cavityFixedRowOffset n :=by
  funext theta
  change cavityFixedRowFieldMean D s a d
      (cavityFixedRowLastFieldSquare D s d * cavityFixedRowRestFieldSquare D s d) theta-
    cavityFixedRowFieldMean D s a d (cavityFixedRowLastFieldSquare D s d) theta*
      cavityFixedRowFieldMean D s a d (cavityFixedRowRestFieldSquare D s d) theta=_
  rw [cavityFixedRowFieldMean_eq_outer D s a d hd _
      ((boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable.mul
        (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable),
    cavityFixedRowFieldMean_eq_outer D s a d hd _
      (boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable,
    cavityFixedRowFieldMean_eq_outer D s a d hd _
      (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable]
  simpa only [cavityFixedRowOuterCovariance,Function.comp_def,sub_zero,Pi.mul_def] using
    (cavityOuterPosteriorCovariance_eq_centeredMean _ _ (anisotropicSchemeMass_nonneg s)
      _ a (k+2) _ _ _ (boundedJets_cavityFixedRowLastFieldSquare D s d)
      (boundedJets_cavityFixedRowRestFieldSquare D s d) _ 0 0 (cavityFixedRowOffset n theta)).symm

theorem contDiff_cavityFixedRowOuterCovariance (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    ContDiff ℝ ∞ (cavityFixedRowOuterCovariance D s a d) :=
  smooth_outer_covariance _ _ (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)) _ a (k+2) _ _ _
    (boundedJets_cavityFixedRowLastFieldSquare D s d) (boundedJets_cavityFixedRowRestFieldSquare D s d) _

theorem cavityFixedRowOffset_basis (i : Fin n) :
    cavityFixedRowOffset n (EuclideanSpace.basisFun (Fin n) ℝ i)=
      anisotropicPairFeature (followupCavityIncidentIndex i) :=by
  classical
  rw [cavityFixedRowOffset_apply,EuclideanSpace.basisFun_apply]
  simp [EuclideanSpace.single_apply]

theorem cavityFixedRowCovariance_hessian_pullback (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) (theta e : Field n) :
    exponentialDensityHessian (cavityFixedRowCovariance D s a d) theta e e=
      exponentialDensityHessian (cavityFixedRowOuterCovariance D s a d)
        (cavityFixedRowOffset n theta) (cavityFixedRowOffset n e) (cavityFixedRowOffset n e) :=by
  rw [cavityFixedRowCovariance_eq_outer D s a d hd]
  exact hessian_comp_linear _ (contDiff_cavityFixedRowOuterCovariance D s a d) _ theta e


theorem cavityFixedRowCovariance_hessian_incident_zero (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    exponentialDensityHessian (cavityFixedRowCovariance D s a d) 0
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)=
      exponentialDensityHessian (cavityFixedRowOuterCovariance D s a d) 0
        (anisotropicPairFeature (followupCavityIncidentIndex i))
        (anisotropicPairFeature (followupCavityIncidentIndex i)) :=by
  rw [cavityFixedRowCovariance_hessian_pullback D s a d hd,map_zero,cavityFixedRowOffset_basis]

end QuantitativeFollowup
