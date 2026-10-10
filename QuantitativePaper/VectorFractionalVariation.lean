module
public import QuantitativePaper.VectorIntegrableControlEnvelope
public import QuantitativePaper.VectorMeasureDisorderTilt
public import QuantitativePaper.VectorMeasureConvexity
public import QuantitativePaper.VectorMeasureFunctional
public import FourPapersCommon.ExponentialIncrementDerivative
public import Paper.JTVariational

@[expose] public section

/-! Genuine arbitrary-profile fractional first variation in control form.
The exponential disorder tilt is integrable, not bounded; its derivative is
justified by slope-uniform truncation and an integrated exponential remainder.
The subsequent conditional-spin identification is a separate theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureFractionalControlDerivative (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (a : ℝ) : ℝ :=
  vectorWeightedMeasureControlDerivative μ ν β t ht
    (fun sample : VectorDisorderBrownianSample n => Real.exp (a*vectorMeasurePotential μ β t sample.1 0))/
      vectorMeasureOuterPartition (n := n) μ β t a

theorem hasDerivWithinAt_vectorMeasureOuterPartition_mix_control
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (a : ℝ) :
    HasDerivWithinAt (fun lam => vectorMeasureOuterPartition (n := n) (Paper.parisiMix μ ν lam) β t a)
      (a*vectorWeightedMeasureControlDerivative μ ν β t ht
        (fun sample : VectorDisorderBrownianSample n => Real.exp (a*vectorMeasurePotential μ β t sample.1 0)))
      (Icc (0 : ℝ) 1) 0 := by
  let U := fun lam (sample : VectorDisorderBrownianSample n) =>
    vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0
  let W := fun sample : VectorDisorderBrownianSample n => Real.exp (a*vectorMeasurePotential μ β t sample.1 0)
  have hW : Measurable[vectorBrownianFiltration n 0] W :=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_vectorMeasurePotential_initial μ β t ht))).comp
      (stronglyMeasurable_initialVectorDisorder n 0).measurable
  have hiW : Integrable W (vectorDisorderBrownianMeasure n) :=
    (integrable_exp_vectorMeasurePotential μ β t ht a (0 : Field n)).comp_fst (vectorBrownianMeasure n)
  have hd := hasDerivWithinAt_vectorMeasurePotential_mix_integrable_weight μ ν β t ht W hW
    (fun _ => (Real.exp_pos _).le) hiW
  have hRn : 0 ≤ (n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance ν μ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)))
      (Paper.parisiCDFDistance_nonneg ν μ)
  have hd' := hasDerivWithinAt_integral_exp_of_weighted_increment
    (P := vectorDisorderBrownianMeasure n) U a
    ((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance ν μ)
    (vectorWeightedMeasureControlDerivative μ ν β t ht W) hRn
    (fun lam => (measurable_vectorMeasurePotential_initial _ β t ht).comp measurable_fst)
    (fun lam _ => (integrable_exp_vectorMeasurePotential _ β t ht a (0 : Field n)).comp_fst (vectorBrownianMeasure n))
    (fun lam hlam sample => by
      simpa only [U,Paper.parisiMix_zero,vectorMeasurePotentialMixIncrement] using norm_vectorMeasurePotentialMixIncrement_le μ ν β t ht lam hlam sample)
    (by simpa only [U,W,Paper.parisiMix_zero,vectorMeasurePotentialMixIncrement] using hd)
  convert hd' using 1
  ext lam
  exact (integral_vectorInitialFunction _).symm

theorem hasDerivWithinAt_normalizedCGF_vectorMeasurePotential_mix_control
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (a : ℝ) :
    HasDerivWithinAt (fun lam => normalizedCGF (completionLaw n)
      (fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) a)
      (vectorMeasureFractionalControlDerivative (n := n) μ ν β t ht a) (Icc (0 : ℝ) 1) 0 := by
  by_cases ha : a=0
  · subst a
    have hd := hasDerivWithinAt_vectorMeasurePotential_mix_weighted_control μ ν β t ht
      (fun _ : VectorDisorderBrownianSample n => 1) measurable_const 1 (by simp) (by simp)
    have h0 (ρ : Paper.ParisiMeasure) : (0 : ℝ) ∈ interior
        (integrableExpSet (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0) (completionLaw n)) := by
      have he : integrableExpSet (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0)
          (completionLaw n)=univ := Set.eq_univ_iff_forall.mpr
        (fun b => integrable_exp_vectorMeasurePotential (n := n) ρ β t ht b 0)
      rw [he,interior_univ]
      trivial
    have he (lam : ℝ) : normalizedCGF (completionLaw n)
        (fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) 0 =
      ∫sample,(1 : ℝ)*vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0
        ∂vectorDisorderBrownianMeasure n := by
      rw [normalizedCGF_zero _ _ (h0 _)]
      simp only [one_mul]
      exact (integral_vectorInitialFunction _).symm
    have hd' : vectorMeasureFractionalControlDerivative (n := n) μ ν β t ht 0 =
        vectorWeightedMeasureControlDerivative (n := n) μ ν β t ht (fun _ : VectorDisorderBrownianSample n => 1) := by
      simp only [vectorMeasureFractionalControlDerivative,vectorMeasureOuterPartition,zero_mul,Real.exp_zero,
        integral_const,probReal_univ,one_smul,div_one]
    rw [hd']
    exact hd.congr (fun lam _ => he lam) (he 0)
  · have hd := hasDerivWithinAt_vectorMeasureOuterPartition_mix_control (n := n) μ ν β t ht a
    have hpos : 0 < vectorMeasureOuterPartition (n := n) (Paper.parisiMix μ ν 0) β t a :=
      vectorMeasureOuterPartition_pos _ β t a ht
    have hh := (hd.log hpos.ne').div_const a
    have he (lam : ℝ) : normalizedCGF (completionLaw n)
        (fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) a =
      Real.log (vectorMeasureOuterPartition (n := n) (Paper.parisiMix μ ν lam) β t a)/a :=
      normalizedCGF_of_ne _ _ ha
    have hder : (a*vectorWeightedMeasureControlDerivative μ ν β t ht
        (fun sample : VectorDisorderBrownianSample n => Real.exp (a*vectorMeasurePotential μ β t sample.1 0)) /
          vectorMeasureOuterPartition (n := n) (Paper.parisiMix μ ν 0) β t a)/a =
        vectorMeasureFractionalControlDerivative (n := n) μ ν β t ht a := by
      rw [Paper.parisiMix_zero]
      unfold vectorMeasureFractionalControlDerivative
      field_simp [ha]
    rw [hder] at hh
    exact hh.congr (fun lam _ => he lam) (he 0)

theorem hasDerivWithinAt_vectorMeasureFunctional_mix_control
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (a : ℝ) :
    HasDerivWithinAt (fun lam => vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t a)
      (vectorMeasureFractionalControlDerivative (n := n) μ ν β t ht a/(n : ℝ)-
        (1-t)*(β^2/2*((∫q in (0 : ℝ)..1,q*Paper.parisiCDF ν q)-
          (∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q)))) (Icc (0 : ℝ) 1) 0 := by
  have hcorr : HasDerivWithinAt (fun lam => β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF (Paper.parisiMix μ ν lam) q)
      (β^2/2*((∫q in (0 : ℝ)..1,q*Paper.parisiCDF ν q)-(∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q)))
      (Icc (0 : ℝ) 1) 0 := by
    let A := ∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q
    let B := ∫q in (0 : ℝ)..1,q*Paper.parisiCDF ν q
    have hd := (((hasDerivAt_id (0 : ℝ)).mul_const (B-A)).const_add A).const_mul (β^2/2)
    simp only [one_mul] at hd
    apply hd.hasDerivWithinAt.congr_of_mem
    · intro lam hlam
      rw [Paper.parisiCorrection_integral_mix μ ν lam hlam]
      dsimp only [A,B,id_eq]
      ring
    · exact ⟨le_rfl,zero_le_one⟩
  exact ((hasDerivWithinAt_normalizedCGF_vectorMeasurePotential_mix_control μ ν β t ht a).div_const (n : ℝ)).sub
    (hcorr.const_mul (1-t))

end QuantitativePaper
