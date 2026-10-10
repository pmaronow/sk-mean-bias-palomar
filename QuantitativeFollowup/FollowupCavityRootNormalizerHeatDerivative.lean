module
public import QuantitativeFollowup.FollowupCavityRootNormalizerSpatial
public import QuantitativeFollowup.FollowupCavityRootNormalizerModel

@[expose] public section

/-! Simultaneous physical incident-coordinate/path-variance response after
actual Gaussian integration by parts. All domination is obtained from the
constructed arbitrary-profile C² potential. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem integrable_selected_spatial_response {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι→Bool) (u : ℝ) (F : EuclideanSpace ℝ ι→ℝ) (hF : ContDiff ℝ 2 F)
    (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (h1 : ∀y,‖fderiv ℝ F y‖≤B*Real.exp (K*‖y‖)) :
    Integrable (fun z=>fderiv ℝ F (gaussianSelectedScale p u z)
      (gaussianSelectedScaleDerivative p u z)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have he (z : EuclideanSpace ℝ ι) : fderiv ℝ F (gaussianSelectedScale p u z)
      (gaussianSelectedScaleDerivative p u z)=
      ∑i,(if p i then 1/(2*Real.sqrt u) else 0)*
        (z i*fderiv ℝ F (gaussianSelectedScale p u z) (EuclideanSpace.basisFun ι ℝ i)) := by
    rw [gaussianSelectedScaleDerivative_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul]
    ring
  simp_rw [he]
  exact integrable_finset_sum _ fun i _=>
    (integrable_gaussianSelectedScale_coordinate_gradient p u F hF B K hB hK h1 i).const_mul _

theorem anisotropicRootDensity_fderiv_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (g v : AnisotropicDisorder n) :
    fderiv ℝ (anisotropicRootDensity D μ a) g v=
      anisotropicRootDensity D μ a g*(a*
        fderiv ℝ (anisotropicMeasurePotential D μ) (anisotropicDisorderInjection n g)
          (anisotropicDisorderInjection n v)) := by
  letI : IsBoundedSMul ℝ (AnisotropicDisorder n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicDisorder n) := IsBoundedSMul.continuousSMul
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) := IsBoundedSMul.continuousSMul
  have hd:=(((contDiff_one_anisotropicMeasurePotential D μ).differentiable (by norm_num) _).hasFDerivAt.comp
    g (anisotropicDisorderInjection n).hasFDerivAt).const_mul a |>.exp
  have he:=congrArg (fun T : AnisotropicDisorder n→L[ℝ]ℝ=>T v) hd.fderiv
  convert he using 1 <;> simp only [anisotropicRootDensity,Function.comp_def,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul] <;> rfl

theorem hasDerivAt_anisotropicMovingRootPartition_heat (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) (halpha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    let Db:=anisotropicReplaceVariance D i (d-alpha*u)
    HasDerivAt (anisotropicMovingRootPartition D μ a p i d alpha)
      (-a*alpha*(∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
        anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)∂anisotropicDisorderLaw n)+
       (1/2:ℝ)*∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
          (∑e,if p e then (D.coupling e)^2*
            (a*anisotropicTailPairSecond Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e+
             a^2*(anisotropicTailPairResponse Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e)^2) else 0)
            ∂anisotropicDisorderLaw n) u := by
  classical
  dsimp only
  let Db:=anisotropicReplaceVariance D i (d-alpha*u)
  let F:=anisotropicRootDensity Db μ a
  obtain ⟨hF,B,K,hB,hK,h1,h2⟩:=anisotropicRootDensity_C2_gaussian_jets Db μ a
  have hgrad:=integrable_selected_spatial_response p u F hF B K hB hK h1
  have hVm : Measurable (fun g=>anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)):=
    (measurable_anisotropicRestartVarianceResponse_disorder Db μ ⟨0,by norm_num⟩ 0 i).comp
      (gaussianSelectedScale p u).continuous.measurable
  have hFi : Integrable (fun g=>F (gaussianSelectedScale p u g)) (anisotropicDisorderLaw n) := by
    have ht:=integrable_exp_anisotropicMeasurePotential (anisotropicScaleRootCouplings Db p u) μ a
    simpa only [anisotropicMeasurePotential_rootCouplingScale,anisotropicRootDensity,F] using ht
  have hVi : Integrable (fun g=>F (gaussianSelectedScale p u g)*
      anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)) (anisotropicDisorderLaw n) := by
    apply (hFi.norm.const_mul (1/2:ℝ)).mono'
      (hFi.aestronglyMeasurable.mul hVm.aestronglyMeasurable)
    exact .of_forall fun g=>by
      simp only [Pi.mul_apply]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_anisotropicRestartVarianceResponse_le_half Db μ
        (gaussianSelectedScale p u g) ⟨0,by norm_num⟩ 0 i) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hp (g : AnisotropicDisorder n) :
      a*(Real.exp (a*anisotropicMovingRootPotential D μ p i d alpha u g)*
        anisotropicMovingRootResponse D μ p i d alpha u g)=
      (-a*alpha)*(F (gaussianSelectedScale p u g)*
        anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g))+
      fderiv ℝ F (gaussianSelectedScale p u g) (gaussianSelectedScaleDerivative p u g) := by
    rw [anisotropicRootDensity_fderiv_apply]
    dsimp only [anisotropicMovingRootPotential,anisotropicMovingRootResponse,F,Db,anisotropicRootDensity]
    ring
  have hh:=gaussianSelected_integral_spatial_response p u hu F hF B K hB hK h1 h2
  have hhd : (∫g,fderiv ℝ F (gaussianSelectedScale p u g) (gaussianSelectedScaleDerivative p u g)
      ∂anisotropicDisorderLaw n)=
      (1/2:ℝ)*∫g,F (gaussianSelectedScale p u g)*(∑e,if p e then
        (D.coupling e)^2*(a*anisotropicTailPairSecond Db μ ⟨0,by norm_num⟩
          (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e+
          a^2*(anisotropicTailPairResponse Db μ ⟨0,by norm_num⟩
            (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e)^2) else 0)
          ∂anisotropicDisorderLaw n := by
    dsimp only [anisotropicDisorderLaw]
    rw [hh]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun g=>by
      dsimp only [F]
      simp_rw [anisotropicRootDensity_pair_hessian]
      simp only [Db,anisotropicReplaceVariance_coupling]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      cases hp:p e <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,mul_zero]
      ring
  have hd:=hasDerivAt_anisotropicMovingRootPartition D μ a p i d alpha u halpha hu hb
  rw [←integral_const_mul a] at hd
  simp_rw [hp] at hd
  rw [integral_add (hVi.const_mul _) hgrad,integral_const_mul,hhd] at hd
  exact hd

end QuantitativeFollowup
