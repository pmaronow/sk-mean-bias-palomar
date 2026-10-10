module
public import QuantitativeFollowup.FollowupCavityRootNormalizerZeroHeat
public import QuantitativeFollowup.FollowupCavityRootNormalizerNormalized

@[expose] public section

/-! Atom-exact normalization of the genuine one-sided root response at
zero incident variance, under the actual arbitrary-profile outer law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

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

theorem hasDerivWithinAt_anisotropicMovingRootPartition_zero_heat
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha : ℝ) (hd : 0<d) :
    let Db:=anisotropicReplaceVariance D i d
    HasDerivWithinAt (anisotropicMovingRootPartition D μ a p i d alpha)
      (-a*alpha*(∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
        anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n)+
       (1/2:ℝ)*∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
          (∑e,if p e then (D.coupling e)^2*
            (a*anisotropicTailPairSecond Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p 0 g)) e+
             a^2*(anisotropicTailPairResponse Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p 0 g)) e)^2) else 0)
            ∂anisotropicDisorderLaw n) (Ici (0:ℝ)) 0 := by
  classical
  dsimp only
  let Db:=anisotropicReplaceVariance D i d
  have hd0:=hasDerivWithinAt_anisotropicMovingRootPartition_zero D μ a p i d alpha hd
  dsimp only at hd0
  have he:(∫g : AnisotropicDisorder n,gaussianSelectedSpatialTrace p
      (fun z : ℝ×AnisotropicDisorder n=>anisotropicRootDensity (anisotropicReplaceVariance D i z.1) μ a z.2)
      d (gaussianSelectedScale p 0 g)∂anisotropicDisorderLaw n)=
      ∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p 0 g)*
          (∑e,if p e then (D.coupling e)^2*
            (a*anisotropicTailPairSecond Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p 0 g)) e+
             a^2*(anisotropicTailPairResponse Db μ ⟨0,by norm_num⟩
              (anisotropicDisorderInjection n (gaussianSelectedScale p 0 g)) e)^2) else 0)
            ∂anisotropicDisorderLaw n:=by
    apply integral_congr_ae
    exact .of_forall fun g=>by
      unfold gaussianSelectedSpatialTrace
      simp_rw [anisotropicRootDensity_pair_hessian]
      simp only [anisotropicReplaceVariance_coupling]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      cases hp:p e <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,mul_zero] <;> ring
  rw [he] at hd0
  exact hd0

theorem hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha : ℝ) (hd : 0<d) :
    let E:=anisotropicCavityInterpolationModel D p i d alpha 0
    HasDerivWithinAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      (-a*alpha*(∫g,anisotropicRootVarianceResponse E μ i g∂anisotropicMeasureOuterLaw E μ a)+
       a/2*(∑e,if p e then (D.coupling e)^2*
          (∫g,anisotropicRootPairScore E μ a e g∂anisotropicMeasureOuterLaw E μ a) else 0))
        (Ici (0:ℝ)) 0 := by
  classical
  dsimp only
  let E:=anisotropicCavityInterpolationModel D p i d alpha (0:ℝ)
  let Db:=anisotropicReplaceVariance D i d
  let w:=fun e : AnisotropicCouplingIndex n=>if p e then (D.coupling e)^2 else 0
  let R:=fun g=>anisotropicRootVarianceResponse E μ i g
  let V:=fun g=>∑e,w e*anisotropicRootPairScore E μ a e g
  have heE : E=anisotropicScaleRootCouplings Db p (0:ℝ):=by
    simpa only [E,Db,anisotropicCavityInterpolationModel,mul_zero,sub_zero] using
      anisotropicReplaceVariance_scaleRootCouplings D p (0:ℝ) i d
  have hd:=(hasDerivWithinAt_anisotropicMovingRootPartition_zero_heat D μ a p i d alpha hd).log
    (by rw [anisotropicMovingRootPartition_eq_actual];exact (anisotropicMeasureOuterPartition_pos E μ a).ne')
  simp_rw [anisotropicMovingRootPartition_eq_actual] at hd
  have hVr (g : AnisotropicDisorder n) : anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
      anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p (0:ℝ) g)=anisotropicRootDensity E μ a g*R g := by
    have hden : anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)=anisotropicRootDensity E μ a g := by
      rw [heE]
      exact congrArg (fun x : ℝ=>Real.exp (a*x))
        (anisotropicMeasurePotential_rootCouplingScale Db μ p (0:ℝ) g).symm
    have hresp : anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p (0:ℝ) g)=R g := by
      dsimp only [R]
      rw [heE]
      exact (anisotropicRootVarianceResponse_rootCouplingScale Db μ p (0:ℝ) i g).symm
    exact congrArg₂ (·*·) hden hresp
  have hPr (g : AnisotropicDisorder n) : anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
      (∑e,if p e then (D.coupling e)^2*(a*anisotropicTailPairSecond Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e+
        a^2*(anisotropicTailPairResponse Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e)^2) else 0)=
      a*(anisotropicRootDensity E μ a g*V g) := by
    have hden : anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)=anisotropicRootDensity E μ a g := by
      rw [heE]
      exact congrArg (fun x : ℝ=>Real.exp (a*x))
        (anisotropicMeasurePotential_rootCouplingScale Db μ p (0:ℝ) g).symm
    rw [hden]
    dsimp only [V,w]
    rw [←mul_assoc]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [anisotropicRootPairScore]
    have hfirst : anisotropicTailPairResponse E μ zeroOverlap (anisotropicDisorderInjection n g) e=
        anisotropicTailPairResponse Db μ zeroOverlap
          (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e := by
      rw [heE]
      exact anisotropicTailPairResponse_scaled_root Db μ p (0:ℝ) g e
    have hsecond : anisotropicTailPairSecond E μ zeroOverlap (anisotropicDisorderInjection n g) e=
        anisotropicTailPairSecond Db μ zeroOverlap
          (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e := by
      rw [heE]
      exact anisotropicTailPairSecond_scaled_root Db μ p (0:ℝ) g e
    rw [hfirst,hsecond]
    cases hp:p e <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,mul_zero] <;> ring
  have hVR : (∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
      anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p (0:ℝ) g)∂anisotropicDisorderLaw n)=
      ∫g,anisotropicRootDensity E μ a g*R g∂anisotropicDisorderLaw n :=
    integral_congr_ae (.of_forall hVr)
  have hPR : (∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
      (∑e,if p e then (D.coupling e)^2*(a*anisotropicTailPairSecond Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e+
        a^2*(anisotropicTailPairResponse Db μ zeroOverlap
        (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e)^2) else 0)
        ∂anisotropicDisorderLaw n)=∫g,a*(anisotropicRootDensity E μ a g*V g)∂anisotropicDisorderLaw n :=
    integral_congr_ae (.of_forall hPr)
  change HasDerivWithinAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      ((-a*alpha*(∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
        anisotropicRootVarianceResponse Db μ i (gaussianSelectedScale p (0:ℝ) g)∂anisotropicDisorderLaw n)+
       (1/2:ℝ)*∫g,anisotropicRootDensity Db μ a (gaussianSelectedScale p (0:ℝ) g)*
          (∑e,if p e then (D.coupling e)^2*
            (a*anisotropicTailPairSecond Db μ zeroOverlap
              (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e+
             a^2*(anisotropicTailPairResponse Db μ zeroOverlap
              (anisotropicDisorderInjection n (gaussianSelectedScale p (0:ℝ) g)) e)^2) else 0)
            ∂anisotropicDisorderLaw n)/anisotropicMeasureOuterPartition E μ a) (Ici (0:ℝ)) (0:ℝ) at hd
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
  change HasDerivWithinAt (fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
    (-a*alpha*(∫g,R g∂anisotropicMeasureOuterLaw E μ a)+
      a/2*(∑e,if p e then (D.coupling e)^2*
        (∫g,anisotropicRootPairScore E μ a e g∂anisotropicMeasureOuterLaw E μ a) else 0)) (Ici (0:ℝ)) (0:ℝ)
  convert! hd using 1
  rw [←hVs,density_normalized_mean E μ a R,density_normalized_mean E μ a V]
  ring


theorem hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero_future_squares
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha : ℝ) (hd : 0<d) :
    let E:=anisotropicCavityInterpolationModel D p i d alpha 0
    HasDerivWithinAt (fun v=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicCavityInterpolationModel D p i d alpha v) μ a))
      (-a*alpha/2*(1-∫r : Paper.Overlap,(r:ℝ)*
          (∫p,(anisotropicProcessSpinResponse E μ r i p)^2∂anisotropicMeasureSampleLaw E μ a)
          ∂parisiFreeMeasure μ a)+
       a/2*(∑e,if p e then (D.coupling e)^2*
          (1-∫r,∫p,(anisotropicProcessPairResponse E μ r e p)^2
            ∂anisotropicMeasureSampleLaw E μ a∂parisiFreeMeasure μ a) else 0)) (Ici (0:ℝ)) 0 := by
  dsimp only
  have hg:=hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero D μ a p i d alpha hd
  dsimp only at hg
  simp_rw [integral_root_pairScore,anisotropic_root_pair_response_balance _ μ a ha hμ,
    integral_root_variance,anisotropic_root_variance_response_balance _ μ a ha hμ] at hg
  convert! hg using 1 <;> ring

end QuantitativeFollowup
