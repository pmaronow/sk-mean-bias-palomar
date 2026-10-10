module
public import QuantitativeFollowup.FollowupCavityRootNormalizerHeatDerivative
public import QuantitativeFollowup.FollowupCavityRootNormalizerExpectations
public import QuantitativeFollowup.FollowupCavityRootNormalizerVarianceExpectation

@[expose] public section

/-! The simultaneous physical root derivative is normalized under the true
outer disorder law. Its spatial charges are replaced by the atom-exact
native future-square identities, with no assumed response formula. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def anisotropicRootPairScore (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (e : AnisotropicCouplingIndex n) (g : AnisotropicDisorder n) : ℝ :=
  anisotropicTailPairSecond D μ zeroOverlap (anisotropicDisorderInjection n g) e+
    a*(anisotropicTailPairResponse D μ zeroOverlap (anisotropicDisorderInjection n g) e)^2

theorem anisotropicRootPairScore_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (e : AnisotropicCouplingIndex n) :
    Measurable (anisotropicRootPairScore D μ a e) := by
  have hp : Continuous (fun g : AnisotropicDisorder n=>(zeroOverlap,anisotropicDisorderInjection n g)):=
    continuous_const.prodMk (anisotropicDisorderInjection n).continuous
  exact ((continuous_anisotropicTailPairSecond_joint D μ e).comp hp).measurable.add
    (((continuous_anisotropicTailPairResponse_joint D μ e).comp hp).measurable.pow_const 2 |>.const_mul a)

theorem anisotropicRootPairScore_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (e : AnisotropicCouplingIndex n) (g : AnisotropicDisorder n) :
    ‖anisotropicRootPairScore D μ a e g‖≤anisotropicPairSecondBound D e+|a| := by
  unfold anisotropicRootPairScore
  apply (norm_add_le _ _).trans
  gcongr
  · simpa only [anisotropicProcessPairSecond,anisotropicProcessParameter,zeroOverlap,
      anisotropicMeasureState_zero,map_zero,add_zero] using
      norm_anisotropicProcessPairSecond_le D μ zeroOverlap e (g,0)
  · rw [norm_mul,Real.norm_eq_abs,norm_pow]
    have hb:=anisotropicTailPairResponse_bound D μ zeroOverlap (anisotropicDisorderInjection n g) e
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (abs_nonneg a)).trans_eq (by norm_num)

private theorem density_normalized_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (F : AnisotropicDisorder n→ℝ) :
    (∫g,F g∂anisotropicMeasureOuterLaw D μ a)=
      (∫g,anisotropicRootDensity D μ a g*F g∂anisotropicDisorderLaw n)/
        anisotropicMeasureOuterPartition D μ a := by
  rw [anisotropicMeasureOuterLaw,integral_tilted]
  simp only [smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  rfl

private theorem integral_root_pairScore (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (e : AnisotropicCouplingIndex n) :
    (∫g,anisotropicRootPairScore D μ a e g∂anisotropicMeasureOuterLaw D μ a)=
      ∫p,anisotropicProcessPairSecond D μ zeroOverlap e p+
        a*(anisotropicProcessPairResponse D μ zeroOverlap e p)^2∂anisotropicMeasureSampleLaw D μ a := by
  have he:=(hasLaw_anisotropicMeasureInitialDisorder D μ a).integral_comp
    (anisotropicRootPairScore_measurable D μ a e).aestronglyMeasurable
  rw [←he]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    simp only [Function.comp_def,anisotropicRootPairScore,anisotropicProcessPairSecond,anisotropicProcessPairResponse,
      anisotropicProcessParameter,zeroOverlap,anisotropicMeasureState_zero,map_zero,add_zero]

private theorem integral_root_variance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (i : Fin n) :
    (∫g,anisotropicRootVarianceResponse D μ i g∂anisotropicMeasureOuterLaw D μ a)=
      ∫p,anisotropicRootVarianceResponse D μ i p.1∂anisotropicMeasureSampleLaw D μ a := by
  exact ((hasLaw_anisotropicMeasureInitialDisorder D μ a).integral_comp
    (measurable_anisotropicRestartVarianceResponse_disorder D μ zeroOverlap 0 i).aestronglyMeasurable).symm

theorem hasDerivAt_log_anisotropicCavityInterpolationPartition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) (halpha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    let E:=anisotropicCavityInterpolationModel D p i d alpha u
    HasDerivAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      (-a*alpha*(∫g,anisotropicRootVarianceResponse E μ i g∂anisotropicMeasureOuterLaw E μ a)+
       a/2*(∑e,if p e then (D.coupling e)^2*
          (∫g,anisotropicRootPairScore E μ a e g∂anisotropicMeasureOuterLaw E μ a) else 0)) u := by
  classical
  dsimp only
  let E:=anisotropicCavityInterpolationModel D p i d alpha u
  let Db:=anisotropicReplaceVariance D i (d-alpha*u)
  let w:=fun e : AnisotropicCouplingIndex n=>if p e then (D.coupling e)^2 else 0
  let R:=fun g=>anisotropicRootVarianceResponse E μ i g
  let V:=fun g=>∑e,w e*anisotropicRootPairScore E μ a e g
  have heE : E=anisotropicScaleRootCouplings Db p u:=anisotropicReplaceVariance_scaleRootCouplings D p u i _
  have hd:=(hasDerivAt_anisotropicMovingRootPartition_heat D μ a p i d alpha u halpha hu hb).log
    (by rw [anisotropicMovingRootPartition_eq_actual];exact (anisotropicMeasureOuterPartition_pos E μ a).ne')
  simp_rw [anisotropicMovingRootPartition_eq_actual] at hd
  have hVr (g : AnisotropicDisorder n) : anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
      anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)=anisotropicRootDensity E μ a g*R g := by
    have hden : anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)=anisotropicRootDensity E μ a g := by
      rw [heE]
      exact congrArg (fun x : ℝ=>Real.exp (a*x))
        (anisotropicMeasurePotential_rootCouplingScale Db μ p u g).symm
    have hresp : anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)=R g := by
      dsimp only [R]
      rw [heE]
      exact (anisotropicRootVarianceResponse_rootCouplingScale Db μ p u i g).symm
    exact congrArg₂ (·*·) hden hresp
  have hPr (g : AnisotropicDisorder n) : anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
      (∑e,if p e then (D.coupling e)^2*(a*anisotropicTailPairSecond Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e+
        a^2*(anisotropicTailPairResponse Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e)^2) else 0)=
      a*(anisotropicRootDensity E μ a g*V g) := by
    have hden : anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)=anisotropicRootDensity E μ a g := by
      rw [heE]
      exact congrArg (fun x : ℝ=>Real.exp (a*x))
        (anisotropicMeasurePotential_rootCouplingScale Db μ p u g).symm
    rw [hden]
    dsimp only [V,w]
    rw [←mul_assoc]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [anisotropicRootPairScore]
    have hfirst : anisotropicTailPairResponse E μ zeroOverlap (anisotropicDisorderInjection n g) e=
        anisotropicTailPairResponse Db μ zeroOverlap
          (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e := by
      rw [heE]
      exact anisotropicTailPairResponse_scaled_root Db μ p u g e
    have hsecond : anisotropicTailPairSecond E μ zeroOverlap (anisotropicDisorderInjection n g) e=
        anisotropicTailPairSecond Db μ zeroOverlap
          (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e := by
      rw [heE]
      exact anisotropicTailPairSecond_scaled_root Db μ p u g e
    rw [hfirst,hsecond]
    cases hp:p e <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,mul_zero] <;> ring
  have hVR : (∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
      anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)∂anisotropicDisorderLaw n)=
      ∫g,anisotropicRootDensity E μ a g*R g∂anisotropicDisorderLaw n :=
    integral_congr_ae (.of_forall hVr)
  have hPR : (∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
      (∑e,if p e then (D.coupling e)^2*(a*anisotropicTailPairSecond Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e+
        a^2*(anisotropicTailPairResponse Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e)^2) else 0)
        ∂anisotropicDisorderLaw n)=∫g,a*(anisotropicRootDensity E μ a g*V g)∂anisotropicDisorderLaw n :=
    integral_congr_ae (.of_forall hPr)
  change HasDerivAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      ((-a*alpha*(∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
        anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p u g)∂anisotropicDisorderLaw n)+
       (1/2:ℝ)*∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p u g)*
          (∑e,if p e then (D.coupling e)^2*
            (a*anisotropicTailPairSecond Db μ zeroOverlap
              (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e+
             a^2*(anisotropicTailPairResponse Db μ zeroOverlap
              (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e)^2) else 0)
            ∂anisotropicDisorderLaw n)/anisotropicMeasureOuterPartition E μ a) u at hd
  rw [hVR,hPR] at hd
  rw [integral_const_mul] at hd
  have hVI (e : AnisotropicCouplingIndex n) : Integrable (anisotropicRootPairScore E μ a e)
      (anisotropicMeasureOuterLaw E μ a):=(integrable_const (anisotropicPairSecondBound E e+|a|)).mono'
      (anisotropicRootPairScore_measurable E μ a e).aestronglyMeasurable (.of_forall (anisotropicRootPairScore_bound E μ a e))
  have hVs : (∫g,V g∂anisotropicMeasureOuterLaw E μ a)=
      ∑e,if p e then (D.coupling e)^2*(∫g,anisotropicRootPairScore E μ a e g∂anisotropicMeasureOuterLaw E μ a) else 0 := by
    rw [show (fun g=>V g)=(fun g=>∑e,w e*anisotropicRootPairScore E μ a e g) from rfl,
      integral_finset_sum _ (fun e _=>(hVI e).const_mul (w e))]
    simp_rw [integral_const_mul]
    apply Finset.sum_congr rfl
    intro e _
    cases hp:p e <;> simp [w,hp]
  change HasDerivAt (fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
    (-a*alpha*(∫g,R g∂anisotropicMeasureOuterLaw E μ a)+
      a/2*(∑e,if p e then (D.coupling e)^2*
        (∫g,anisotropicRootPairScore E μ a e g∂anisotropicMeasureOuterLaw E μ a) else 0)) u
  convert hd using 1
  rw [←hVs,density_normalized_mean E μ a R,density_normalized_mean E μ a V]
  ring

theorem hasDerivAt_log_anisotropicCavityInterpolationPartition_future_squares
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha u : ℝ)
    (halpha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    let E:=anisotropicCavityInterpolationModel D p i d alpha u
    HasDerivAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      (-a*alpha/2*(1-∫r : Paper.Overlap,(r:ℝ)*
          (∫p,(anisotropicProcessSpinResponse E μ r i p)^2∂anisotropicMeasureSampleLaw E μ a)
          ∂parisiFreeMeasure μ a)+
       a/2*(∑e,if p e then (D.coupling e)^2*
          (1-∫r,∫p,(anisotropicProcessPairResponse E μ r e p)^2
            ∂anisotropicMeasureSampleLaw E μ a∂parisiFreeMeasure μ a) else 0)) u := by
  dsimp only
  have hd:=hasDerivAt_log_anisotropicCavityInterpolationPartition D μ a p i d alpha u halpha hu hb
  dsimp only at hd
  simp_rw [integral_root_pairScore,anisotropic_root_pair_response_balance _ μ a ha hμ,
    integral_root_variance,anisotropic_root_variance_response_balance _ μ a ha hμ] at hd
  convert hd using 1 <;> ring

end QuantitativeFollowup
