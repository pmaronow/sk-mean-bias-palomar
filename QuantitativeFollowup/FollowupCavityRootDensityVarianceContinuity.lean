module
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceHessian
public import QuantitativeFollowup.FollowupCavityRootNormalizerSpatial

@[expose] public section

/-! True joint continuity of the root exponential density and its spatial
Hessian while a positive auxiliary variance varies. The derivative maps
are the actual Fréchet derivatives of the constructed potential. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n:ℕ}

 theorem continuousAt_anisotropicMeasurePotential_variance_joint
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(i:Fin n)(b:ℝ)(hb:0<b)
    (P:AnisotropicParameter n):
    ContinuousAt (fun z:ℝ×AnisotropicParameter n=>
      anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ z.2) (b,P):=by
  let C:ℝ:=‖anisotropicEnergyMap D‖
  have he:∀ᶠz:ℝ×AnisotropicParameter n in 𝓝 (b,P),
      ‖anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ z.2-
        anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ P‖≤
        (1/2:ℝ)*|z.1-b|+C*‖z.2-P‖:=by
    have hp:∀ᶠz:ℝ×AnisotropicParameter n in 𝓝 (b,P),0<z.1:=
      (continuous_fst:Continuous (fun z:ℝ×AnisotropicParameter n=>z.1)).continuousAt.eventually (Ioi_mem_nhds hb)
    filter_upwards [hp] with z hz
    have hv:=anisotropicMeasureTailPotential_variance_abs_sub_le D μ ⟨0,by norm_num⟩ z.2 i z.1 b hz hb
    simp only [anisotropicMeasureTailPotential_zero,sub_zero] at hv
    have hL:=anisotropicMeasurePotential_lipschitz (anisotropicReplaceVariance D i b) μ
    rw [anisotropicReplaceVariance_energyMap] at hL
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ z.2) _).trans
      (add_le_add (by simpa only [Real.norm_eq_abs] using hv)
        (by simpa only [C,coe_nnnorm] using hL.norm_sub_le z.2 P))
  have hu:Tendsto (fun z:ℝ×AnisotropicParameter n=>(1/2:ℝ)*|z.1-b|+C*‖z.2-P‖)
      (𝓝 (b,P)) (𝓝 0):=by
    have hc:Continuous (fun z:ℝ×AnisotropicParameter n=>(1/2:ℝ)*|z.1-b|+C*‖z.2-P‖):=by fun_prop
    simpa only [sub_self,abs_zero,norm_zero,mul_zero,add_zero] using hc.tendsto (b,P)
  apply tendsto_sub_nhds_zero_iff.mp
  exact squeeze_zero_norm' (f:=fun z:ℝ×AnisotropicParameter n=>
    anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ z.2-
    anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ P) he hu

theorem continuousAt_anisotropicRootDensity_variance_joint
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(a:ℝ)(i:Fin n)(b:ℝ)(hb:0<b)
    (g:AnisotropicDisorder n):
    ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a z.2) (b,g):=by
  change ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
    Real.exp (a*anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ
      (anisotropicDisorderInjection n z.2))) (b,g)
  have hm:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>(z.1,anisotropicDisorderInjection n z.2)) (b,g):=by fun_prop
  have hc:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ (anisotropicDisorderInjection n z.2)) (b,g):=
    ContinuousAt.comp
      (f:=fun z:ℝ×AnisotropicDisorder n=>(z.1,anisotropicDisorderInjection n z.2))
      (g:=fun z:ℝ×AnisotropicParameter n=>anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ z.2)
      (continuousAt_anisotropicMeasurePotential_variance_joint D μ i b hb (anisotropicDisorderInjection n g)) hm
  exact Real.continuous_exp.continuousAt.comp (hc.const_mul a)

private theorem unitCouplings_replaceVariance (D:AnisotropicSpinModel n)(i:Fin n)(b:ℝ):
    anisotropicUnitCouplings (anisotropicReplaceVariance D i b)=
      anisotropicReplaceVariance (anisotropicUnitCouplings D) i b:=rfl

private theorem couplingRescaling_replaceVariance (D:AnisotropicSpinModel n)(i:Fin n)(b:ℝ):
    anisotropicCouplingRescaling (anisotropicReplaceVariance D i b)=anisotropicCouplingRescaling D:=rfl

private theorem continuousAt_variance_pairResponse_zero
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(i:Fin n)(b:ℝ)(hb:0<b)
    (g:AnisotropicDisorder n)(e:AnisotropicCouplingIndex n):
    ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      anisotropicTailPairResponse (anisotropicReplaceVariance D i z.1) μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n z.2) e) (b,g):=by
  let L:AnisotropicDisorder n→L[ℝ]AnisotropicParameter n:=
    (anisotropicCouplingRescaling D).comp (anisotropicDisorderInjection n)
  have hm:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>(z.1,L z.2)) (b,g):=by fun_prop
  have hc:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i z.1) μ) (L z.2)) (b,g):=
    ContinuousAt.comp
      (f:=fun z:ℝ×AnisotropicDisorder n=>(z.1,L z.2))
      (g:=fun z:ℝ×AnisotropicParameter n=>
        fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i z.1) μ) z.2)
      (continuousAt_anisotropicMeasurePotential_variance_spatialDifferential
        (anisotropicUnitCouplings D) μ i b hb (L g)) hm
  have he (v:ℝ):anisotropicMeasureTailPotential (anisotropicUnitCouplings (anisotropicReplaceVariance D i v)) μ ⟨0,by norm_num⟩=
      anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i v) μ:=by
    rw [unitCouplings_replaceVariance]
    exact funext (anisotropicMeasureTailPotential_zero _ μ)
  unfold anisotropicTailPairResponse
  simp_rw [he,couplingRescaling_replaceVariance]
  exact hc.clm_apply continuousAt_const

private theorem continuousAt_variance_pairSecond_zero
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(i:Fin n)(b:ℝ)(hb:0<b)
    (g:AnisotropicDisorder n)(e:AnisotropicCouplingIndex n):
    ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      anisotropicTailPairSecond (anisotropicReplaceVariance D i z.1) μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n z.2) e) (b,g):=by
  let L:AnisotropicDisorder n→L[ℝ]AnisotropicParameter n:=
    (anisotropicCouplingRescaling D).comp (anisotropicDisorderInjection n)
  have hm:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>(z.1,L z.2)) (b,g):=by fun_prop
  have hc:ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i z.1) μ)) (L z.2)) (b,g):=
    ContinuousAt.comp
      (f:=fun z:ℝ×AnisotropicDisorder n=>(z.1,L z.2))
      (g:=fun z:ℝ×AnisotropicParameter n=>
        fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i z.1) μ)) z.2)
      (continuousAt_anisotropicMeasurePotential_variance_spatialSecondDifferential
        (anisotropicUnitCouplings D) μ i b hb (L g)) hm
  have he (v:ℝ):anisotropicMeasureTailPotential (anisotropicUnitCouplings (anisotropicReplaceVariance D i v)) μ ⟨0,by norm_num⟩=
      anisotropicMeasurePotential (anisotropicReplaceVariance (anisotropicUnitCouplings D) i v) μ:=by
    rw [unitCouplings_replaceVariance]
    exact funext (anisotropicMeasureTailPotential_zero _ μ)
  unfold anisotropicTailPairSecond
  simp_rw [he,couplingRescaling_replaceVariance]
  exact (hc.clm_apply continuousAt_const).clm_apply continuousAt_const

theorem continuousAt_anisotropicRootDensity_variance_spatialDiagonal
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(a:ℝ)(i:Fin n)(b:ℝ)(hb:0<b)
    (g:AnisotropicDisorder n)(e:AnisotropicCouplingIndex n):
    ContinuousAt (fun z:ℝ×AnisotropicDisorder n=>
      fderiv ℝ (fderiv ℝ (anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a)) z.2
        (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)
        (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)) (b,g):=by
  simp_rw [anisotropicRootDensity_pair_hessian,anisotropicReplaceVariance_coupling]
  exact ((continuousAt_anisotropicRootDensity_variance_joint D μ a i b hb g).mul continuousAt_const).mul
    ((continuousAt_const.mul (continuousAt_variance_pairSecond_zero D μ i b hb g e)).add
      (continuousAt_const.mul ((continuousAt_variance_pairResponse_zero D μ i b hb g e).pow 2)))

end QuantitativeFollowup
