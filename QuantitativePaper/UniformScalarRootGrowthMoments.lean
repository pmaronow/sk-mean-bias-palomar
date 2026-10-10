module
public import QuantitativePaper.UniformScalarSmoothing
public import FRSB.SupportDensityFormula
public import FRSB.BackwardsTime
public import FRSB.ParisiMinimizerGeometry
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Actual energy-coordinate polynomial moments along the optimal scalar
diffusion. The coefficient is the smooth left CDF at the terminal atom.
All derivative laws follow from the proved stochastic polynomial hierarchy. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 2200000

def scalarRootJet (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) (q : ℝ)
    (sample : Paper.BrownianSample) : ℝ := β^j*jetProcess β μ (j+1) q sample
def scalarRootMomentA (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β^4*quotientNumerator β μ q
def scalarRootMomentB (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β^3*quotientDenominator β μ q
def scalarRootGamma (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β*momentQuotient β μ q
def scalarRootMixedMoment (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β^5*(∫sample,C β μ q sample*D β μ q sample^2 ∂canonicalBrownianMeasure)
def scalarRootFourthMoment (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β^4*(∫sample,C β μ q sample^4 ∂canonicalBrownianMeasure)
def scalarRootFourthSquare (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  β^6*(∫sample,A β μ q sample^2 ∂canonicalBrownianMeasure)

theorem scalarRootJet_eq_energyJet (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (j : ℕ) (q : ℝ) (sample : Paper.BrownianSample) :
    scalarRootJet β μ j q sample=scalarEnergySpatialJet β μ j
      (q,optimalStateReal β μ sample q/β) := by
  have he : β*(optimalStateReal β μ sample q/β)=optimalStateReal β μ sample q := by field_simp
  simp only [scalarRootJet,scalarEnergySpatialJet,jetProcess,he]
  congr 1

theorem integrable_scalarRootJet_pow (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (j l : ℕ) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    Integrable (fun sample=>scalarRootJet β μ j q sample^l) canonicalBrownianMeasure := by
  simp only [scalarRootJet,mul_pow]
  exact (integrable_jetProcess_pow β hβ μ j l hq).const_mul _

theorem scalarRootMomentA_eq (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootMomentA β μ q=∫sample,scalarRootJet β μ 2 q sample^2 ∂canonicalBrownianMeasure := by
  simp only [scalarRootMomentA,quotientNumerator,quotientNumeratorPolynomial,moment_X_pow,
    scalarRootJet,mul_pow,←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by ring

theorem scalarRootMomentB_eq (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootMomentB β μ q=∫sample,scalarRootJet β μ 1 q sample^3 ∂canonicalBrownianMeasure := by
  simp only [scalarRootMomentB,quotientDenominator,quotientDenominatorPolynomial,moment_X_pow,
    scalarRootJet,mul_pow,←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by ring

theorem scalarRootMixedMoment_eq (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootMixedMoment β μ q=∫sample,scalarRootJet β μ 1 q sample*
      scalarRootJet β μ 2 q sample^2 ∂canonicalBrownianMeasure := by
  rw [scalarRootMixedMoment,←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by dsimp only [scalarRootJet];ring

theorem scalarRootFourthMoment_eq (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootFourthMoment β μ q=∫sample,scalarRootJet β μ 1 q sample^4 ∂canonicalBrownianMeasure := by
  simp only [scalarRootFourthMoment,scalarRootJet,mul_pow,←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by ring

theorem scalarRootFourthSquare_eq (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootFourthSquare β μ q=∫sample,scalarRootJet β μ 3 q sample^2 ∂canonicalBrownianMeasure := by
  simp only [scalarRootFourthSquare,scalarRootJet,mul_pow,←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by ring

theorem scalarRootGamma_eq_quotient (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarRootGamma β μ q=scalarRootMomentA β μ q/(2*scalarRootMomentB β μ q) := by
  unfold scalarRootGamma scalarRootMomentA scalarRootMomentB momentQuotient
  field_simp <;> ring

theorem scalarRootGamma_eq_CDF (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Ico (0:ℝ) qtop) :
    scalarRootGamma β μ q=β*parisiCDF μ q := by
  rw [scalarRootGamma,parisiCDF_eq_momentQuotient_on_support_interval
    β hβ μ hmin qtop hqtop.1 hqtop.2.le hsupp q hq]

theorem scalarRootJet_one_pos (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (sample : Paper.BrownianSample) :
    0<scalarRootJet β μ 1 q sample := by
  simpa only [scalarRootJet,pow_one] using mul_pos hβ (C_pos β μ hq sample)

theorem scalarRootContactMoment (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    (∫sample,scalarRootJet β μ 1 q sample^2 ∂canonicalBrownianMeasure)=1 := by
  have hh:=GammaPrime_eq_one_on_support_interval β hβ μ hmin qtop hqtop.1 hqtop.2.le hsupp q hq
  simpa only [GammaPrime,curvatureMoment2,scalarRootJet,pow_one,mul_pow,
    integral_const_mul] using hh

theorem scalarRootMoments_contDiffOn (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) :
    ContDiffOn ℝ ∞ (scalarRootMomentA β μ) (Icc 0 qtop) ∧
      ContDiffOn ℝ ∞ (scalarRootMomentB β μ) (Icc 0 qtop) ∧
      ContDiffOn ℝ ∞ (scalarRootGamma β μ) (Icc 0 qtop) := by
  have hh:=moments_contDiffOn_on_support_interval β hβ μ hmin qtop hqtop.1 hqtop.2.le hsupp
  exact ⟨contDiffOn_const.mul (hh.1 quotientNumeratorPolynomial),
    contDiffOn_const.mul (hh.1 quotientDenominatorPolynomial),contDiffOn_const.mul hh.2⟩

theorem scalarRootMomentA_hasDerivWithinAt (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    HasDerivWithinAt (scalarRootMomentA β μ)
      (scalarRootFourthSquare β μ q-6*scalarRootGamma β μ q*scalarRootMixedMoment β μ q)
      (Icc 0 qtop) q := by
  have hh:=(hasDerivWithinAt_moment_on_support_interval β hβ μ hmin qtop hqtop.1
    hqtop.2.le hsupp quotientNumeratorPolynomial q hq).const_mul (β^4)
  rw [momentDrift0_quotientNumerator_value,momentDrift1_quotientNumerator_value] at hh
  have he : (∫sample,-6*C β μ q sample*D β μ q sample^2 ∂canonicalBrownianMeasure)=
      -6*(∫sample,C β μ q sample*D β μ q sample^2 ∂canonicalBrownianMeasure) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun sample=>by ring
  rw [he] at hh
  convert hh using 1
  · rfl
  · dsimp only [scalarRootFourthSquare,scalarRootGamma,scalarRootMixedMoment]
    ring

theorem scalarRootMomentB_hasDerivWithinAt (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    HasDerivWithinAt (scalarRootMomentB β μ)
      (3*scalarRootMixedMoment β μ q-3*scalarRootGamma β μ q*scalarRootFourthMoment β μ q)
      (Icc 0 qtop) q := by
  have hh:=(hasDerivWithinAt_moment_on_support_interval β hβ μ hmin qtop hqtop.1
    hqtop.2.le hsupp quotientDenominatorPolynomial q hq).const_mul (β^3)
  rw [momentDrift0_quotientDenominator_value,momentDrift1_quotientDenominator_value] at hh
  have he : (∫sample,3*C β μ q sample*D β μ q sample^2 ∂canonicalBrownianMeasure)=
      3*(∫sample,C β μ q sample*D β μ q sample^2 ∂canonicalBrownianMeasure) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun sample=>by ring
  rw [he,show (∫sample,-3*C β μ q sample^4 ∂canonicalBrownianMeasure)=
    -3*(∫sample,C β μ q sample^4 ∂canonicalBrownianMeasure) from integral_const_mul _ _] at hh
  convert hh using 1
  · rfl
  · dsimp only [scalarRootGamma,scalarRootMixedMoment,scalarRootFourthMoment]
    ring

theorem scalarRootGamma_hasDerivWithinAt (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    HasDerivWithinAt (scalarRootGamma β μ) (β*parisiSmoothDensity β μ qtop q) (Icc 0 qtop) q := by
  exact (smoothCDFDensity_hasDerivWithinAt _ _
    (moments_contDiffOn_on_support_interval β hβ μ hmin qtop hqtop.1 hqtop.2.le hsupp).2 q hq).const_mul β

end QuantitativePaper
