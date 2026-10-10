module
public import QuantitativeFollowup.FollowupCavityDecouplingCovariance

@[expose] public section

/-! Actual deleted three-descendant moment at u=0 equals the normalized
rest covariance trace plus covariance energy. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true

 theorem cavityDeletedThreeDifference_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (q : Paper.Overlap) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2)^2
      ∂cavityThreeDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a q)=
      ∫z,(cavitySpinDifferencePairing Finset.univ z.2)^2
        ∂cavityThreeDescendantLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a q := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun sample : AnisotropicDisorderBrownianSample n=>
    ∑i : Fin n,∑j : Fin n,anisotropicProcessSpinCovariance R μ q sample i j*
      anisotropicProcessPairResponse R μ q (anisotropicOrderedCoupling i j) sample
  have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(q,sample)) :=
    measurable_const.prodMk measurable_id
  have hC (i j : Fin n) : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      anisotropicProcessSpinCovariance R μ q sample i j) := by
    have hm := (measurable_uncurry_cavityCovarianceEntry R μ i j).comp hmap
    dsimp only [Function.comp_def] at hm
    exact hm
  have hF : Measurable F := Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
    (hC i j).mul (measurable_anisotropicProcessPairResponse R μ q (anisotropicOrderedCoupling i j))
  have hsum (ω : AnisotropicDisorderBrownianSample (n+1)) :
      (∑i∈Finset.univ.erase (Fin.last n),∑j∈Finset.univ.erase (Fin.last n),
        anisotropicProcessSpinCovariance D μ q ω i j*
          anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) ω)=
      F (cavityRestSampleProjection n ω) := by
    have herase : (Finset.univ.erase (Fin.last n))=(Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
      rw [Fin.univ_castSuccEmb]
      simp
    simp only [herase,Finset.sum_map]
    change (∑ i : Fin n, ∑ j : Fin n,
      anisotropicProcessSpinCovariance D μ q ω i.castSucc j.castSucc *
        anisotropicProcessPairResponse D μ q
          (anisotropicOrderedCoupling i.castSucc j.castSucc) ω) = _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (fun x y : ℝ => x*y)
      (cavityRestProcessSpinCovariance_zero μ n β ρ hβ hρ q ω i j)
      (cavityRestProcessPairResponse_zero μ n β ρ hβ hρ q ω i j)
  rw [cavityThreeDescendantLaw_difference_square,cavityThreeDescendantLaw_difference_square]
  congr 1
  have hfun : (fun ω=>∑i∈Finset.univ.erase (Fin.last n),∑j∈Finset.univ.erase (Fin.last n),
      anisotropicProcessSpinCovariance D μ q ω i j*
        anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) ω)=
      F ∘ cavityRestSampleProjection n :=funext hsum
  rw [hfun]
  change (∫ω,F (cavityRestSampleProjection n ω) ∂anisotropicMeasureSampleLaw D μ a)=
    ∫ω,F ω ∂anisotropicMeasureSampleLaw R μ a
  exact (hasLaw_cavityRestSampleProjection μ n β ρ hβ hρ a).integral_comp hF.aestronglyMeasurable

 theorem followup_cavity_zero_deleted_three_half_square (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (q : Paper.Overlap) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a q)/2=
      cavitySignedResponseCovarianceTraceMoment (followupCavityRestSpinModel n β ρ hβ hρ) μ a q+
        cavitySignedResponseCovarianceMoment (followupCavityRestSpinModel n β ρ hβ hρ) μ a Finset.univ q := by
  have he : (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a q)=
      ∫z,(cavitySpinDifferencePairing Finset.univ z.2/(n:ℝ))^2
        ∂cavityThreeDescendantLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a q := by
    simp only [div_pow,integral_div]
    rw [cavityDeletedThreeDifference_zero]
  rw [he,cavityThreeDescendantLaw_normalized_difference_square]
  ring

end QuantitativeFollowup
