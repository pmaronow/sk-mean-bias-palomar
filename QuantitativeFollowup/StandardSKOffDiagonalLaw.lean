module
public import QuantitativeFollowup.StandardSKOffDiagonalState
public import QuantitativePaper.VectorDiagonalProjection
public import FourPapersCommon.TiltedPushforward
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! The genuine zero-diagonal SK sample law is the completed SK sample law
with its independent common diagonal coordinate removed. Physical
observables invariant under that removal have exactly equal moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem standardSKOffDiagonalOuterLaw_marginal (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    (anisotropicMeasureOuterLaw (standardSKOffDiagonalModel n β t hβ ht) μ a).map
      standardSKOffDiagonalDisorder = vectorOffDiagonalOuterLaw (n:=n) μ β t a := by
  let f : Couplings n → ℝ := fun g => a*vectorMeasurePotential μ β t (g,0) 0
  have hf : Measurable f := by
    exact measurable_const.mul ((measurable_vectorMeasurePotential_initial (n:=n) μ β t ht.le).comp
      (measurable_id.prodMk measurable_const))
  have he : (fun ω : AnisotropicDisorder n =>
      a*anisotropicMeasurePotential (standardSKOffDiagonalModel n β t hβ ht) μ
        (anisotropicDisorderInjection n ω)) = f ∘ standardSKOffDiagonalDisorder := by
    funext ω
    rw [anisotropicDisorderInjection_apply,standardSKOffDiagonalMeasurePotential]
    rfl
  rw [anisotropicMeasureOuterLaw,he,map_tilted_pullback _ _
    measurable_standardSKOffDiagonalDisorder f hf,anisotropicDisorderLaw_standardSKOffDiagonalDisorder]
  rfl

theorem standardSKOffDiagonalOuterLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    (anisotropicMeasureOuterLaw (standardSKOffDiagonalModel n β t hβ ht) μ a).map
      standardSKOffDiagonalCompression =
      (vectorOffDiagonalOuterLaw (n:=n) μ β t a).map vectorOffDiagonalCompletion := by
  change (anisotropicMeasureOuterLaw _ μ a).map
    (vectorOffDiagonalCompletion ∘ standardSKOffDiagonalDisorder) = _
  rw [←Measure.map_map measurable_vectorOffDiagonalCompletion
    measurable_standardSKOffDiagonalDisorder,standardSKOffDiagonalOuterLaw_marginal μ β t a hβ ht]

theorem standardSKOffDiagonalSampleLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    (anisotropicMeasureSampleLaw (standardSKOffDiagonalModel n β t hβ ht) μ a).map
      standardSKOffDiagonalSampleCompression =
      (vectorMeasureDisorderTilt (n:=n) μ β t a).map vectorRemoveDiagonalSample := by
  rw [vectorMeasureDisorderTilt_removeDiagonal μ β t a ht.le]
  unfold anisotropicMeasureSampleLaw
  change ((anisotropicMeasureOuterLaw _ μ a).prod (vectorBrownianMeasure n)).map
    (Prod.map standardSKOffDiagonalCompression id) = _
  rw [←Measure.map_prod_map _ _ measurable_standardSKOffDiagonalCompression measurable_id,
    Measure.map_id,standardSKOffDiagonalOuterLaw μ β t a hβ ht]

theorem integral_standardSKOffDiagonalSampleLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (F : VectorDisorderBrownianSample n→ℝ) (hF : Measurable F)
    (hFD : ∀sample,F (vectorRemoveDiagonalSample sample)=F sample) :
    (∫ sample,F (standardSKOffDiagonalSampleCompression sample)
      ∂anisotropicMeasureSampleLaw (standardSKOffDiagonalModel n β t hβ ht) μ a) =
      ∫ sample,F sample ∂vectorMeasureDisorderTilt μ β t a := by
  have he := integral_map measurable_standardSKOffDiagonalSampleCompression.aemeasurable
    hF.aestronglyMeasurable
    (μ:=anisotropicMeasureSampleLaw (standardSKOffDiagonalModel n β t hβ ht) μ a)
  rw [standardSKOffDiagonalSampleLaw μ β t a hβ ht] at he
  have hp := integral_map measurable_vectorRemoveDiagonalSample.aemeasurable hF.aestronglyMeasurable
    (μ:=vectorMeasureDisorderTilt μ β t a)
  simp only [hFD] at hp
  exact he.symm.trans hp

theorem variance_standardSKOffDiagonalSampleLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (F : VectorDisorderBrownianSample n→ℝ) (hF : Measurable F)
    (hFD : ∀sample,F (vectorRemoveDiagonalSample sample)=F sample) :
    variance (F ∘ standardSKOffDiagonalSampleCompression)
      (anisotropicMeasureSampleLaw (standardSKOffDiagonalModel n β t hβ ht) μ a) =
      variance F (vectorMeasureDisorderTilt μ β t a) := by
  have he := congrArg (variance F) (standardSKOffDiagonalSampleLaw μ β t a hβ ht)
  rw [variance_map hF.aemeasurable measurable_standardSKOffDiagonalSampleCompression.aemeasurable,
    variance_map hF.aemeasurable measurable_vectorRemoveDiagonalSample.aemeasurable] at he
  have hfun : F ∘ vectorRemoveDiagonalSample = F := funext hFD
  rw [hfun] at he
  exact he

end QuantitativeFollowup
