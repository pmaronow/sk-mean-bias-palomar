module
public import QuantitativeFollowup.FollowupCavityRootDensityVarianceEnvelope
public import FourPapersCommon.GaussianSelectedMovingZeroHeat
public import QuantitativeFollowup.FollowupCavityRootNormalizerModel

@[expose] public section

/-! Actual one-sided simultaneous incident-heat/path-variance response at
zero incident variance. Spatial heat and the moving positive path variance
are differentiated separately before adding their exact integral formulas. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem hasDerivWithinAt_anisotropicRootDensity_moving_heat_zero
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha : ℝ) (hd : 0<d) :
    HasDerivWithinAt (fun u=>∫g : AnisotropicDisorder n,
      (anisotropicRootDensity (anisotropicReplaceVariance D i (d-alpha*u)) μ a (gaussianSelectedScale p u g)-
       anisotropicRootDensity (anisotropicReplaceVariance D i (d-alpha*u)) μ a (gaussianSelectedScale p 0 g))
        ∂anisotropicDisorderLaw n)
      ((1/2:ℝ)*∫g : AnisotropicDisorder n,
        gaussianSelectedSpatialTrace p
          (fun z : ℝ×AnisotropicDisorder n=>anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a z.2)
          d (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n) (Ici (0:ℝ)) 0 := by
  classical
  let F:=fun z : ℝ×AnisotropicDisorder n=>anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a z.2
  obtain ⟨B,K,hB,hK,hbound⟩:=anisotropicRootDensity_positive_variance_jet_envelope D μ a i d hd
  have h0 (b:ℝ)(hb:b∈Ioo (d/2) (d+1))(y:AnisotropicDisorder n):‖F (b,y)‖≤B*Real.exp (K*‖y‖):=by
    simpa only [norm_iteratedFDeriv_zero] using hbound b hb 0 (by norm_num) y
  have h1 (b:ℝ)(hb:b∈Ioo (d/2) (d+1))(y:AnisotropicDisorder n):
      ‖fderiv ℝ (fun z=>F (b,z)) y‖≤B*Real.exp (K*‖y‖):=by
    simpa only [norm_iteratedFDeriv_one] using hbound b hb 1 (by norm_num) y
  have h2 (b:ℝ)(hb:b∈Ioo (d/2) (d+1))(y:AnisotropicDisorder n):
      ‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y‖≤B*Real.exp (K*‖y‖):=by
    have hh:=hbound b hb 2 (by norm_num) y
    rw [←norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hh
    exact hh
  have hF (b:ℝ)(hb:b∈Ioo (d/2) (d+1)):ContDiff ℝ 2 (fun y=>F (b,y)):=
    (anisotropicRootDensity_C2_gaussian_jets (anisotropicReplaceVariance D i b) μ a).1
  have hH (e:AnisotropicCouplingIndex n)(he:p e=true):ContinuousOn (fun z : ℝ×AnisotropicDisorder n=>
      fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)
        (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e))
      ((Ioo (d/2) (d+1))×ˢ(univ:Set (AnisotropicDisorder n))):=by
    dsimp only [F]
    intro z hz
    exact (continuousAt_anisotropicRootDensity_variance_spatialDiagonal D μ a i z.1
      (by linarith [hz.1.1]) z.2 e).continuousWithinAt
  exact hasDerivWithinAt_gaussianSelected_moving_heat_zero p F (d/2) (d+1) d alpha B K
    (by constructor <;> linarith) hB hK hF hH h0 h1 h2

theorem hasDerivWithinAt_anisotropicMovingRootPartition_zero
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha : ℝ) (hd : 0<d) :
    let Db:=anisotropicReplaceVariance D i d
    HasDerivWithinAt (anisotropicMovingRootPartition D μ a p i d alpha)
      (-a*alpha*(∫g : AnisotropicDisorder n,
        anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
          anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n)+
       (1/2:ℝ)*∫g : AnisotropicDisorder n,
        gaussianSelectedSpatialTrace p
          (fun z : ℝ×AnisotropicDisorder n=>anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a z.2)
          d (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n) (Ici (0:ℝ)) 0 := by
  dsimp only
  let D0:=anisotropicScaleRootCouplings D p 0
  let Db:=anisotropicReplaceVariance D i d
  let H:=fun u=>∫g : AnisotropicDisorder n,
    (anisotropicRootDensity (anisotropicReplaceVariance D i (d-alpha*u)) μ a (gaussianSelectedScale p u g)-
     anisotropicRootDensity (anisotropicReplaceVariance D i (d-alpha*u)) μ a (gaussianSelectedScale p 0 g))
      ∂anisotropicDisorderLaw n
  let V:=fun u=>anisotropicMeasureOuterPartition (anisotropicReplaceVariance D0 i (d-alpha*u)) μ a
  have he (u:ℝ):anisotropicMovingRootPartition D μ a p i d alpha u=H u+V u:=by
    have hi (v:ℝ):Integrable (fun g : AnisotropicDisorder n=>
        anisotropicRootDensity (anisotropicReplaceVariance D i (d-alpha*u)) μ a (gaussianSelectedScale p v g))
        (anisotropicDisorderLaw n):=by
      have hh:=integrable_exp_anisotropicMeasurePotential
        (anisotropicScaleRootCouplings (anisotropicReplaceVariance D i (d-alpha*u)) p v) μ a
      simpa only [anisotropicMeasurePotential_rootCouplingScale,anisotropicRootDensity] using hh
    dsimp only [H,V,anisotropicMovingRootPartition,anisotropicMovingRootPotential,
      anisotropicMeasureOuterPartition,D0]
    rw [integral_sub (hi u) (hi 0)]
    simp_rw [anisotropicReplaceVariance_scaleRootCouplings,anisotropicMeasurePotential_rootCouplingScale]
    simp only [anisotropicRootDensity,sub_add_cancel]
  have hvar:=hasDerivAt_anisotropicMeasureOuterPartition_variance D0 μ a i d hd
  have hb:HasDerivAt (fun u:ℝ=>d-alpha*u) (-alpha) 0:=by
    convert! (hasDerivAt_const (0:ℝ) d).sub ((hasDerivAt_id (0:ℝ)).const_mul alpha) using 1 <;>
      simp only [zero_sub,id_eq,mul_one,Pi.sub_apply]
  have hvar0:HasDerivAt (fun c=>anisotropicMeasureOuterPartition (anisotropicReplaceVariance D0 i c) μ a)
      (a*∫g : AnisotropicDisorder n,Real.exp (a*anisotropicMeasurePotential
        (anisotropicReplaceVariance D0 i d) μ (anisotropicDisorderInjection n g))*
        anisotropicRootVarianceResponse (anisotropicReplaceVariance D0 i d) μ i g
          ∂anisotropicDisorderLaw n) (d-alpha*(0:ℝ)):=by
    simpa only [mul_zero,sub_zero] using hvar
  have hv:=hvar0.comp (0:ℝ) hb
  have hs:anisotropicReplaceVariance D0 i d=anisotropicScaleRootCouplings Db p 0:=
    anisotropicReplaceVariance_scaleRootCouplings D p 0 i d
  have hcoef:(a*∫g : AnisotropicDisorder n,Real.exp (a*anisotropicMeasurePotential
        (anisotropicReplaceVariance D0 i d) μ (anisotropicDisorderInjection n g))*
        anisotropicRootVarianceResponse (anisotropicReplaceVariance D0 i d) μ i g
          ∂anisotropicDisorderLaw n)*(-alpha)=
      -a*alpha*(∫g : AnisotropicDisorder n,
        anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
          anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n):=by
    rw [hs]
    simp_rw [anisotropicMeasurePotential_rootCouplingScale,anisotropicRootVarianceResponse_rootCouplingScale]
    dsimp only [anisotropicRootDensity]
    ring
  have hvw:HasDerivWithinAt V
      (-a*alpha*(∫g : AnisotropicDisorder n,
        anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
          anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n))
        (Ici (0:ℝ)) 0:=by
    convert! hv.hasDerivWithinAt (s:=Ici (0:ℝ)) using 1
    exact hcoef.symm
  have hh:=hasDerivWithinAt_anisotropicRootDensity_moving_heat_zero D μ a p i d alpha hd
  have hx:=hvw.add hh
  change HasDerivWithinAt (V+H) _ (Ici (0:ℝ)) 0 at hx
  have hfun:V+H=anisotropicMovingRootPartition D μ a p i d alpha:=by
    funext u
    exact (add_comm _ _).trans (he u).symm
  rw [hfun] at hx
  exact hx

end QuantitativeFollowup
