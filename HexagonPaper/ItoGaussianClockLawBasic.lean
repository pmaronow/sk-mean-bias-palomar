module
public import HexagonPaper.VariableScalarClock
public import FourPapersCommon.DeterministicBrownianProcess
public import FourPapersCommon.GaussianFiniteVectorLawEquality

@[expose] public section

/-! True finite observation laws of deterministic Itô/Wiener drivers.
The only identification premise is the actual Gram matrix of the stopped
deterministic integrands; the Gaussian law and all covariance identities
are derived from the genuine canonical Brownian measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus FourPapersCommon
open scoped Topology NNReal ENNReal BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem scalarClockStoppedReferencePath_eval_one
    (τ : Paper.Overlap ≃o Paper.Overlap) (β : ℝ)
    (sample : Paper.BrownianSample) (q : Paper.Overlap) :
    scalarClockStoppedReferencePath τ β 1 sample q =
      β * Paper.canonicalBrownian (τ q : ℝ).toNNReal sample := by
  change β * Paper.canonicalBrownian
    (FRSB.stoppedOverlapTime (τ (1 : Paper.Overlap) : ℝ).toNNReal (τ q)) sample = _
  have ht : (τ (1 : Paper.Overlap) : ℝ) = 1 :=
    congrArg (fun r : Paper.Overlap => (r : ℝ)) τ.map_top
  rw [ht, Real.toNNReal_one]
  have htime : FRSB.stoppedOverlapTime 1 (τ q) = (τ q : ℝ).toNNReal := by
    apply NNReal.eq
    change min (τ q : ℝ) 1 = ((τ q : ℝ).toNNReal : ℝ)
    rw [min_eq_left (τ q).property.2, Real.coe_toNNReal _ (τ q).property.1]
  rw [htime]

theorem measurable_scalarClockStoppedReferencePath_one
    (τ : Paper.Overlap ≃o Paper.Overlap) (β : ℝ) :
    Measurable (scalarClockStoppedReferencePath τ β 1) :=
  (measurable_scalarClockPathReindex τ).comp
    (measurable_scalarStoppedBrownianPath β _)

theorem deterministicWiener_clock_finite_law
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (τ : Paper.Overlap ≃o Paper.Overlap) (β : ℝ)
    (hGram : ∀ q r : Paper.Overlap,
      inner ℝ (deterministicTimeCut f (q : ℝ).toNNReal)
        (deterministicTimeCut f (r : ℝ).toNNReal) =
          β ^ 2 * min (τ q : ℝ) (τ r : ℝ))
    (I : Finset Paper.Overlap) :
    Paper.canonicalBrownianMeasure.map
      (fun sample => fun q : I =>
        (wienerIntegral Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (deterministicTimeCut f (q.val : ℝ).toNNReal) : Paper.BrownianSample → ℝ)
            sample) =
    Paper.canonicalBrownianMeasure.map
      (fun sample => fun q : I =>
        β * Paper.canonicalBrownian (τ q.val : ℝ).toNNReal sample) := by
  classical
  let hB := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
  let X : Paper.BrownianSample → EuclideanSpace ℝ I :=
    deterministicWienerVector hB (fun q : I =>
      deterministicTimeCut f (q.val : ℝ).toNNReal)
  let Y : Paper.BrownianSample → EuclideanSpace ℝ I := fun sample =>
    WithLp.toLp 2 (fun q : I => β * Paper.canonicalBrownian
      (τ q.val : ℝ).toNNReal sample)
  have hX : HasGaussianLaw X Paper.canonicalBrownianMeasure :=
    hasGaussianLaw_deterministicWienerVector hB _
  have hProc : IsGaussianProcess
      (fun q : Paper.Overlap => fun sample =>
        β * Paper.canonicalBrownian (τ q : ℝ).toNNReal sample)
      Paper.canonicalBrownianMeasure := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (hB.isGaussianProcess.comp_right
        (fun q : Paper.Overlap => (τ q : ℝ).toNNReal)).smul (fun _ => β)
  have hY : HasGaussianLaw Y Paper.canonicalBrownianMeasure := by
    exact (hProc.hasGaussianLaw I).map
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap
  have hm : ∀ q : I,
      (∫ sample, X sample q ∂Paper.canonicalBrownianMeasure) =
      (∫ sample, Y sample q ∂Paper.canonicalBrownianMeasure) := by
    intro q
    change (∫ sample,
      (wienerIntegral hB (deterministicTimeCut f (q.val : ℝ).toNNReal) :
        Paper.BrownianSample → ℝ) sample ∂Paper.canonicalBrownianMeasure) =
      ∫ sample, β * Paper.canonicalBrownian (τ q.val : ℝ).toNNReal sample
        ∂Paper.canonicalBrownianMeasure
    rw [integral_wienerIntegral, integral_const_mul, hB.integral_eval, mul_zero]
  have hc : ∀ q r : I,
      cov[fun sample => X sample q, fun sample => X sample r;
        Paper.canonicalBrownianMeasure] =
      cov[fun sample => Y sample q, fun sample => Y sample r;
        Paper.canonicalBrownianMeasure] := by
    intro q r
    change cov[(wienerIntegral hB (deterministicTimeCut f (q.val : ℝ).toNNReal) :
        Paper.BrownianSample → ℝ),
      (wienerIntegral hB (deterministicTimeCut f (r.val : ℝ).toNNReal) :
        Paper.BrownianSample → ℝ); Paper.canonicalBrownianMeasure] =
      cov[fun sample => β * Paper.canonicalBrownian (τ q.val : ℝ).toNNReal sample,
        fun sample => β * Paper.canonicalBrownian (τ r.val : ℝ).toNNReal sample;
        Paper.canonicalBrownianMeasure]
    rw [covariance_deterministicWiener, hGram, covariance_const_mul_left,
      covariance_const_mul_right, hB.covariance_eval]
    simp only [NNReal.coe_min, Real.coe_toNNReal _ (τ q.val).property.1,
      Real.coe_toNNReal _ (τ r.val).property.1]
    ring
  have he := gaussian_finite_vector_law_eq_of_mean_covariance
    Paper.canonicalBrownianMeasure Paper.canonicalBrownianMeasure X Y hX hY hm hc
  let L : EuclideanSpace ℝ I →L[ℝ] (I → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).toContinuousLinearMap
  have hXm : Measurable X := measurable_deterministicWienerVector hB _
  have hYm : Measurable Y := by
    apply (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).measurable.comp
    apply Measurable.of_eval
    intro q
    exact (Paper.measurable_canonicalBrownian _).const_mul β
  have ho := congrArg (fun μ : Measure (EuclideanSpace ℝ I) => μ.map L) he
  rw [Measure.map_map L.measurable hXm, Measure.map_map L.measurable hYm] at ho
  exact ho

end HexagonPaper
