module
public import QuantitativeFollowup.StandardSKOffDiagonalModel
public import QuantitativePaper.VectorMeasureTail
public import QuantitativePaper.VectorMeasureGradient

@[expose] public section

/-! Exact finite and arbitrary-profile Parisi recursion transport through
the actual zero-diagonal SK disorder projection. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
variable {n k : ℕ}

theorem standardSKOffDiagonalUnitInput (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) :
    anisotropicUnitInput (standardSKOffDiagonalModel n β t hβ ht)=
      Real.sqrt ((1-t)*β^2) • anisotropicFieldInjection n := by
  ext z e
  cases e <;> simp [anisotropicUnitInput,anisotropicNoiseMap_apply,
    anisotropicFieldInjection,standardSKOffDiagonalModel]

theorem standardSKOffDiagonalShiftInput (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (v : ℝ) :
    Real.sqrt v • anisotropicUnitInput (standardSKOffDiagonalModel n β t hβ ht)=
      Real.sqrt ((1-t)*(β^2*v)) • anisotropicFieldInjection n := by
  rw [standardSKOffDiagonalUnitInput,smul_smul]
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β)
  rw [show (1-t)*(β^2*v)=((1-t)*β^2)*v by ring,Real.sqrt_mul hc,mul_comm]

theorem standardSKOffDiagonalTerminalPotential (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicGridTerminalPotential (standardSKOffDiagonalModel n β t hβ ht)
      (anisotropicParameterPoint ω x)=
      vectorTerminalPotential n β t (standardSKOffDiagonalCompression ω) x := by
  unfold anisotropicGridTerminalPotential finiteLinearSoftmax finiteLinearPartition
    vectorTerminalPotential terminalPotential terminalPartition
  simp_rw [anisotropicTerminalLinear_apply,standardSKOffDiagonalHamiltonian]

theorem standardSKOffDiagonalTailRecursion (s : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (q : ℝ) (j : ℕ) (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicTailRecursion (standardSKOffDiagonalModel n β t hβ ht) s q j
      (anisotropicParameterPoint ω x)=
      vectorTailRecursion s β t q (standardSKOffDiagonalCompression ω) j x := by
  induction j generalizing x with
  | zero => exact standardSKOffDiagonalTerminalPotential β t hβ ht ω x
  | succ j ih =>
    rw [anisotropicTailRecursion,standardSKOffDiagonalShiftInput]
    rw [anisotropicParameterPoint_field]
    rw [gaussianShiftColeHopf_smul_eq_vectorStep]
    have he : (fun y=>anisotropicTailRecursion (standardSKOffDiagonalModel n β t hβ ht) s q j
        (anisotropicParameterPoint ω 0+anisotropicFieldInjection n y))=
        vectorTailRecursion s β t q (standardSKOffDiagonalCompression ω) j := by
      funext y
      rw [←anisotropicParameterPoint_field]
      exact ih y
    rw [he]
    rfl

theorem standardSKOffDiagonalFinitePotential (s : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (j : ℕ) (hj : j≤k+2)
    (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicFinitePotential (standardSKOffDiagonalModel n β t hβ ht) s j
      (anisotropicParameterPoint ω x)=vectorRecursion s β t (standardSKOffDiagonalCompression ω) j x := by
  have he:=standardSKOffDiagonalTailRecursion s β t hβ ht 0 j ω x
  rw [anisotropicTailRecursion_zero _ s hj,vectorTailRecursion_zero s β t _ hj] at he
  exact he

theorem standardSKOffDiagonalMeasureTailPotential (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (q : Paper.Overlap) (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicMeasureTailPotential (standardSKOffDiagonalModel n β t hβ ht) μ q
      (anisotropicParameterPoint ω x)=
      vectorMeasureTailPotential μ β t q (standardSKOffDiagonalCompression ω) x := by
  apply tendsto_nhds_unique
    (tendsto_anisotropicDyadicTailPotential _ μ q (anisotropicParameterPoint ω x))
  have he (j : ℕ) : anisotropicDyadicTailPotential (standardSKOffDiagonalModel n β t hβ ht) μ q j
      (anisotropicParameterPoint ω x)=
      vectorDyadicTailPotential μ β t q j (standardSKOffDiagonalCompression ω) x :=
    standardSKOffDiagonalTailRecursion _ β t hβ ht q _ ω x
  simp_rw [he]
  exact tendsto_vectorDyadicTailPotential μ β t q ht.le q.property _ x

theorem standardSKOffDiagonalMeasurePotential (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicMeasurePotential (standardSKOffDiagonalModel n β t hβ ht) μ
      (anisotropicParameterPoint ω x)=
      vectorMeasurePotential μ β t (standardSKOffDiagonalCompression ω) x := by
  have he:=standardSKOffDiagonalMeasureTailPotential μ β t hβ ht ⟨0,by norm_num⟩ ω x
  rw [anisotropicMeasureTailPotential_zero] at he
  simp only [Subtype.coe_mk,vectorMeasureTailPotential_zero μ β t ht.le] at he
  exact he

theorem standardSKOffDiagonalMeasureMagnetization (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (q : Paper.Overlap) (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicMeasureTailMagnetization (standardSKOffDiagonalModel n β t hβ ht) μ q
      (anisotropicParameterPoint ω x)=
      vectorMeasureGradient μ β t q (standardSKOffDiagonalCompression ω) x := by
  let D:=standardSKOffDiagonalModel n β t hβ ht
  have hP : HasFDerivAt (fun y : Field n=>anisotropicParameterPoint ω y)
      (anisotropicFieldInjection n) x := by
    simpa only [←anisotropicParameterPoint_field] using
      ((anisotropicFieldInjection n).hasFDerivAt (x:=x)).const_add (anisotropicParameterPoint ω 0)
  have hd:=(((anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one
    (anisotropicParameterPoint ω x)).hasFDerivAt.comp x hP)
  have he : (anisotropicMeasureTailPotential D μ q ∘ (fun y : Field n=>anisotropicParameterPoint ω y))=
      vectorMeasureTailPotential μ β t q (standardSKOffDiagonalCompression ω) := by
    funext y
    exact standardSKOffDiagonalMeasureTailPotential μ β t hβ ht q ω y
  rw [he] at hd
  have hdual:=hd.unique (hasFDerivAt_vectorMeasureTailPotential μ β t ht.le q _ x)
  apply ext_inner_right ℝ
  intro w
  have hw:=congrArg (fun L : Field n→L[ℝ]ℝ=>L w) hdual
  simpa only [ContinuousLinearMap.comp_apply,fderiv_anisotropicMeasureTailPotential_field,
    InnerProductSpace.toDual_apply_apply,D] using hw

end QuantitativeFollowup
