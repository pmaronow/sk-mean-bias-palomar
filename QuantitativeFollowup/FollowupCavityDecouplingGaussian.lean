module
public import QuantitativeFollowup.FollowupCavityDecouplingCoordinates
public import FourPapersCommon.FiniteStateGaussianLaw

@[expose] public section

/-! The old disorder projection and split Wiener drivers have their actual
Gaussian/product probability laws. Unused incident coordinates are retained
on the original probability space. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem anisotropicDisorderLaw_map_cavityRestDisorderProjection (n : ℕ) :
    (anisotropicDisorderLaw (n+1)).map (cavityRestDisorderProjection n)=anisotropicDisorderLaw n := by
  have hc (i j : AnisotropicCouplingIndex n) :
      finiteStateSpectralCovariance (cavityRestDisorderProjection n) i j=
        finiteStateSpectralCovariance (ContinuousLinearMap.id ℝ (AnisotropicDisorder n)) i j := by
    classical
    simp only [finiteStateSpectralCovariance,cavityRestDisorderProjection_apply,
      ContinuousLinearMap.id_apply,EuclideanSpace.single_apply]
    by_cases hij : i=j
    · subst j
      simp only [mul_ite,ite_mul,one_mul,mul_one,zero_mul,mul_zero]
      simp
    · have he : cavityRestCouplingEmbedding n i≠cavityRestCouplingEmbedding n j :=
        (cavityRestCouplingEmbedding n).injective.ne hij
      simp only [mul_ite,ite_mul,one_mul,mul_one,zero_mul,mul_zero]
      simp [hij,he]
  have hh:=stdGaussian_map_eq_of_spectral_covariance (cavityRestDisorderProjection n)
    (ContinuousLinearMap.id ℝ (AnisotropicDisorder n)) hc
  change (stdGaussian (AnisotropicDisorder (n+1))).map (cavityRestDisorderProjection n)=
    (stdGaussian (AnisotropicDisorder n)).map (id : AnisotropicDisorder n→AnisotropicDisorder n) at hh
  rw [Measure.map_id] at hh
  exact hh

def cavityWienerSplit (n : ℕ) (W : VectorBrownianSample (n+1)) :
    VectorBrownianSample n×Paper.BrownianSample :=
  (fun i=>W i.castSucc,W (Fin.last n))

theorem measurable_cavityWienerSplit (n : ℕ) : Measurable (cavityWienerSplit n) :=
  (Measurable.of_eval fun i=>measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply (Fin.last n))

theorem vectorBrownianMeasure_map_cavityWienerSplit (n : ℕ) :
    (vectorBrownianMeasure (n+1)).map (cavityWienerSplit n)=
      (vectorBrownianMeasure n).prod Paper.canonicalBrownianMeasure := by
  let e:=MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>Paper.BrownianSample) (Fin.last n)
  have he:=(measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1)=>Paper.canonicalBrownianMeasure) (Fin.last n)).map_eq
  have hh : cavityWienerSplit n=Prod.swap∘e := by
    funext W
    apply Prod.ext
    · funext i
      change W i.castSucc=W ((Fin.last n).succAbove i)
      rw [Fin.succAbove_last]
    · rfl
  rw [vectorBrownianMeasure,hh,←Measure.map_map measurable_swap e.measurable,he,Measure.prod_swap]
  rfl

end QuantitativeFollowup
