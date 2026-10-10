module
public import QuantitativeFollowup.StandardSKOffDiagonalLaw
public import QuantitativePaper.VectorDiagonalMarked

@[expose] public section

/-! Exact transport of the zero-diagonal SK terminal marks. The common
diagonal Gaussian is removed from the completed physical marked law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem standardSKOffDiagonalTerminalLaw (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicTerminalSpinKernel (standardSKOffDiagonalModel n β t hβ ht)
      (anisotropicParameterPoint ω x)=
      terminalLaw (vectorTerminalExponent n β t (standardSKOffDiagonalCompression ω) x) := by
  apply Measure.ext_of_singleton
  intro σ
  rw [anisotropicTerminalSpinKernel,Kernel.comap_apply,finiteStateGibbsKernel_singleton]
  unfold terminalLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ)]
  simp only [terminalPMF,PMF.ofFintype_apply]
  congr 1
  unfold gtStateGibbs gtStatePartition terminalWeight terminalPartition
  have he (τ : Configuration n) :
      (anisotropicEnergyMap (standardSKOffDiagonalModel n β t hβ ht)
        (anisotropicParameterPoint ω x)) τ=
        vectorTerminalExponent n β t (standardSKOffDiagonalCompression ω) x τ := by
    rw [anisotropicEnergyMap_apply,anisotropicTerminalLinear_apply,
      standardSKOffDiagonalHamiltonian]
  simp only [zero_add,add_zero,he]

theorem standardSKOffDiagonalTerminalKernel (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) :
    anisotropicMeasureTerminalKernel (standardSKOffDiagonalModel n β t hβ ht) μ=
      (vectorCompletedTerminalKernel μ β t ht.le).comap
        standardSKOffDiagonalSampleCompression measurable_standardSKOffDiagonalSampleCompression := by
  ext sample A hA
  simp only [anisotropicMeasureTerminalKernel,Kernel.comap_apply,vectorCompletedTerminalKernel]
  unfold anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKOffDiagonalTerminalLaw]
  have hs := standardSKOffDiagonalMeasureState μ β t hβ ht 1 (by norm_num) sample
  change (terminalLaw (vectorTerminalExponent n β t (standardSKOffDiagonalCompression sample.1)
    (anisotropicMeasureState (standardSKOffDiagonalModel n β t hβ ht) μ 1 sample))) A = _
  rw [hs,Real.toNNReal_one]
  rfl

def standardSKOffDiagonalMarkedCompression
    (p : AnisotropicDisorderBrownianSample n×Configuration n) :
    VectorDisorderBrownianSample n×Configuration n :=
  (standardSKOffDiagonalSampleCompression p.1,p.2)

theorem measurable_standardSKOffDiagonalMarkedCompression :
    Measurable (standardSKOffDiagonalMarkedCompression (n:=n)) :=
  (measurable_standardSKOffDiagonalSampleCompression.comp measurable_fst).prodMk measurable_snd

theorem standardSKOffDiagonalMarkedLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    (anisotropicMeasureSpinPathLaw (standardSKOffDiagonalModel n β t hβ ht) μ a).map
      standardSKOffDiagonalMarkedCompression =
      (vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le).map vectorRemoveDiagonalMarked := by
  unfold anisotropicMeasureSpinPathLaw
  rw [standardSKOffDiagonalTerminalKernel]
  change ((anisotropicMeasureSampleLaw _ μ a) ⊗ₘ
    (vectorCompletedTerminalKernel μ β t ht.le).comap
      standardSKOffDiagonalSampleCompression measurable_standardSKOffDiagonalSampleCompression).map
      (fun p=>(standardSKOffDiagonalSampleCompression p.1,p.2)) = _
  rw [compProd_comap_map_history _ _ measurable_standardSKOffDiagonalSampleCompression,
    standardSKOffDiagonalSampleLaw μ β t a hβ ht,
    vectorMeasureSpinPathLaw_removeDiagonal μ β t a ht.le]

end QuantitativeFollowup
