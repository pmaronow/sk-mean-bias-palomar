module
public import QuantitativeFollowup.StandardSKAnisotropicState
public import QuantitativePaper.VectorTiltedBrownian
public import QuantitativePaper.VectorMeasureSpinLaw
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Exact pushforward of the actual generalized marked spin/diffusion law
to the printed completed SK interpolation law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1400000
variable {n : ℕ}

theorem standardSKAnisotropicOuterPartition (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    anisotropicMeasureOuterPartition (standardSKAnisotropicModel n β t hβ ht) μ a=
      vectorMeasureOuterPartition (n:=n) μ β t a := by
  have hF : Measurable (fun p : Couplings n×ℝ=>Real.exp (a*vectorMeasurePotential μ β t p 0)) :=
    (measurable_const.mul (measurable_vectorMeasurePotential_initial μ β t ht.le)).exp
  have he:=integral_map measurable_standardSKDisorderCompression.aemeasurable hF.aestronglyMeasurable
    (μ:=anisotropicDisorderLaw n)
  rw [anisotropicDisorderLaw_standardSKDisorderCompression n hn] at he
  unfold anisotropicMeasureOuterPartition vectorMeasureOuterPartition
  simp_rw [anisotropicDisorderInjection_apply,standardSKAnisotropicMeasurePotential]
  exact he.symm

theorem standardSKAnisotropicOuterLaw (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    (anisotropicMeasureOuterLaw (standardSKAnisotropicModel n β t hβ ht) μ a).map
      standardSKDisorderCompression=vectorMeasureOuterLaw (n:=n) μ β t a := by
  rw [anisotropicMeasureOuterLaw_density]
  simp_rw [anisotropicDisorderInjection_apply,standardSKAnisotropicMeasurePotential]
  rw [standardSKAnisotropicOuterPartition hn μ β t a hβ ht]
  change ((anisotropicDisorderLaw n).withDensity (fun ω=>ENNReal.ofReal
    (vectorMeasureOuterWeight μ β t a (standardSKDisorderCompression ω)))).map standardSKDisorderCompression=_
  have hh := map_withDensity_pullback (anisotropicDisorderLaw n)
    standardSKDisorderCompression measurable_standardSKDisorderCompression
    (fun p : Couplings n×ℝ=>ENNReal.ofReal (vectorMeasureOuterWeight μ β t a p))
    (measurable_vectorMeasureOuterWeight μ β t a ht.le).ennreal_ofReal
  rw [anisotropicDisorderLaw_standardSKDisorderCompression n hn] at hh
  exact hh

theorem standardSKAnisotropicSampleLaw (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    (anisotropicMeasureSampleLaw (standardSKAnisotropicModel n β t hβ ht) μ a).map
      standardSKSampleCompression=vectorMeasureDisorderTilt (n:=n) μ β t a := by
  rw [vectorMeasureDisorderTilt_eq_prod μ β t a ht.le]
  unfold anisotropicMeasureSampleLaw
  change ((anisotropicMeasureOuterLaw _ μ a).prod (vectorBrownianMeasure n)).map
    (Prod.map standardSKDisorderCompression id)=_
  rw [←Measure.map_prod_map _ _ measurable_standardSKDisorderCompression measurable_id,
    Measure.map_id,standardSKAnisotropicOuterLaw hn μ β t a hβ ht]

theorem standardSKAnisotropicTerminalLaw (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicTerminalSpinKernel (standardSKAnisotropicModel n β t hβ ht)
      (anisotropicParameterPoint ω x)=
      terminalLaw (vectorTerminalExponent n β t (standardSKDisorderCompression ω) x) := by
  apply Measure.ext_of_singleton
  intro σ
  rw [anisotropicTerminalSpinKernel,Kernel.comap_apply,finiteStateGibbsKernel_singleton]
  unfold terminalLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ)]
  simp only [terminalPMF,PMF.ofFintype_apply]
  congr 1
  unfold gtStateGibbs gtStatePartition terminalWeight terminalPartition
  have he (τ : Configuration n) :
      (anisotropicEnergyMap (standardSKAnisotropicModel n β t hβ ht) (anisotropicParameterPoint ω x)) τ=
        vectorTerminalExponent n β t (standardSKDisorderCompression ω) x τ := by
    rw [anisotropicEnergyMap_apply,anisotropicTerminalLinear_apply,standardSKAnisotropicHamiltonian]
  simp only [zero_add,add_zero,he]

theorem standardSKAnisotropicTerminalKernel (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) :
    anisotropicMeasureTerminalKernel (standardSKAnisotropicModel n β t hβ ht) μ=
      (((terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
        (measurable_vectorTerminalExponent_state n β t)).comap
          (vectorMeasureJointState μ β t ht.le 1) (measurable_vectorMeasureJointState μ β t ht.le 1)).comap
            standardSKSampleCompression measurable_standardSKSampleCompression) := by
  ext sample A hA
  simp only [anisotropicMeasureTerminalKernel,Kernel.comap_apply]
  unfold anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKAnisotropicTerminalLaw]
  have hs := standardSKAnisotropicMeasureState μ β t hβ ht 1 (by norm_num) sample
  change (terminalLaw (vectorTerminalExponent n β t (standardSKDisorderCompression sample.1)
    (anisotropicMeasureState (standardSKAnisotropicModel n β t hβ ht) μ 1 sample))) A = _
  rw [hs,Real.toNNReal_one]
  rfl

def standardSKMarkedCompression (p : AnisotropicDisorderBrownianSample n×Configuration n) :
    VectorDisorderBrownianSample n×Configuration n := (standardSKSampleCompression p.1,p.2)

theorem measurable_standardSKMarkedCompression : Measurable (standardSKMarkedCompression (n:=n)) :=
  (measurable_standardSKSampleCompression.comp measurable_fst).prodMk measurable_snd

theorem standardSKAnisotropicMarkedLaw (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    (anisotropicMeasureSpinPathLaw (standardSKAnisotropicModel n β t hβ ht) μ a).map
      standardSKMarkedCompression=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le := by
  unfold anisotropicMeasureSpinPathLaw
  rw [standardSKAnisotropicTerminalKernel]
  change ((anisotropicMeasureSampleLaw _ μ a) ⊗ₘ
    (((terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
      (measurable_vectorTerminalExponent_state n β t)).comap
      (vectorMeasureJointState μ β t ht.le 1) (measurable_vectorMeasureJointState μ β t ht.le 1)).comap
      standardSKSampleCompression measurable_standardSKSampleCompression)).map
      (fun p=>(standardSKSampleCompression p.1,p.2)) = _
  rw [compProd_comap_map_history _ _ measurable_standardSKSampleCompression,
    standardSKAnisotropicSampleLaw hn μ β t a hβ ht]
  rfl

end QuantitativeFollowup
