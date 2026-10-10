module
public import QuantitativeFollowup.FollowupCavityFixedRowNativeFieldSquares
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeHistoryMoments
public import QuantitativeFollowup.FollowupCavityFixedRowPhysicalDerivative
public import QuantitativeFollowup.FollowupCavityCppNativeFunction
public import FourPapersCommon.FiniteStreamingPolynomialsIterated

@[expose] public section

/-! The genuine retained-node covariance agrees with the native Cpp
curve on the entire closed interval. Consequently the actual original
physical response is the native first within jet, with no response premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteStreamingPolynomials
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFixedRowFieldMean_zero_eq_native_scheme_integral
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2)
    (f : FiniteStateField (Configuration (n+1)) → ℝ) (hf : Measurable f) :
    cavityFixedRowFieldMean D s a d f 0 =
      ∫sample, f (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) sample))
        ∂anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a := by
  rw [cavityFixedRowFieldMean_eq_outer D s a d hd f hf]
  dsimp only
  rw [map_zero, cavityOuterPosteriorMean_eq_native_scheme_node D s a d hd f hf]
  have hp : Measurable (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-d) (by omega))) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_uncurry_anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)).comp
        (measurable_const.prodMk measurable_id)
  exact integral_anisotropicMeasureSpinPathLaw_sample D (Paper.parisiSchemeMeasure s) a _
    (hf.comp ((anisotropicEnergyMap D).measurable.comp hp))

theorem cavityFixedRowRecordedCovariance_eq_native_covariance
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2) :
    cavityFixedRowRecordedCovariance D s a d =
      covariance
        (fun sample => (anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s)
          (anisotropicSchemeNode s (k+2-d) (by omega)) (Fin.last n) sample)^2)
        (fun sample => anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
          (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s)
            (anisotropicSchemeNode s (k+2-d) (by omega)) sample))
        (anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a) := by
  let p := anisotropicSchemeNode s (k+2-d) (by omega)
  let X := fun sample => (anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s) p
    (Fin.last n) sample)^2
  let Y := fun sample => anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
    (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s) p sample)
  have hm : Measurable (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s) p) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_uncurry_anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s)).comp
        (measurable_const.prodMk measurable_id)
  have hX : MemLp X 2 (anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a) := by
    apply MemLp.of_bound
      ((measurable_anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s) p (Fin.last n)).pow_const 2).aestronglyMeasurable 1
    exact .of_forall fun sample => by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _)
        (anisotropicProcessSpinResponse_bound D (Paper.parisiSchemeMeasure s) p (Fin.last n) sample) 2).trans_eq (by norm_num)
  have hY : MemLp Y 2 (anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a) :=
    MemLp.of_bound ((continuous_anisotropicSelectedMeanSquare _).measurable.comp hm).aestronglyMeasurable 1
      (.of_forall fun sample => anisotropicSelectedMeanSquare_bound _ _
        (fun i => by simpa only [Real.norm_eq_abs, anisotropicProcessSpinResponse] using
          anisotropicProcessSpinResponse_bound D (Paper.parisiSchemeMeasure s) p i sample))
  have hf := (boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable
  have hg := (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable
  have hfg : Measurable (fun H => cavityFixedRowLastFieldSquare D s d H *
      cavityFixedRowRestFieldSquare D s d H) := by
    simpa only [Pi.mul_def] using hf.mul hg
  rw [cavityFixedRowRecordedCovariance_eq_zero_offset]
  change cavityFixedRowFieldMean D s a d
      (fun H => cavityFixedRowLastFieldSquare D s d H * cavityFixedRowRestFieldSquare D s d H) 0 -
    cavityFixedRowFieldMean D s a d (cavityFixedRowLastFieldSquare D s d) 0 *
      cavityFixedRowFieldMean D s a d (cavityFixedRowRestFieldSquare D s d) 0 = _
  rw [cavityFixedRowFieldMean_zero_eq_native_scheme_integral D s a d hd
      (fun H => cavityFixedRowLastFieldSquare D s d H * cavityFixedRowRestFieldSquare D s d H) hfg,
    cavityFixedRowFieldMean_zero_eq_native_scheme_integral D s a d hd _ hf,
    cavityFixedRowFieldMean_zero_eq_native_scheme_integral D s a d hd _ hg]
  simp_rw [cavityFixedRowLastFieldSquare_at_native_scheme_node D s d hd,
    cavityFixedRowRestFieldSquare_at_native_scheme_node D s d hd]
  exact (covariance_eq_sub hX hY).symm

theorem cavityFixedRowRecordedCovariance_eq_followupCavityCpp
    (beta rho : ℝ) (hbeta : 0 < beta) (hrho : rho ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    cavityFixedRowRecordedCovariance (followupCavitySpinModel n beta rho hbeta hrho u hu) s a d =
      followupCavityCpp n beta rho hbeta hrho (Paper.parisiSchemeMeasure s) a u hu
        (anisotropicSchemeNode s (k+2-d) (by omega)) := by
  rw [cavityFixedRowRecordedCovariance_eq_native_covariance _ s a d hd]
  unfold followupCavityCpp
  simp_rw [cavitySelectedMeanSquare_erased_last_projection]
  rfl

theorem cavityFixedRowPhysicalCurveCovariance_eq_native_cpp_on
    (beta rho : ℝ) (hbeta : 0 < beta) (hrho : rho ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    EqOn (cavityFixedRowPhysicalCurveCovariance (n:=n) beta rho hbeta hrho s a d)
      (followupCavityCppFunction n beta rho hbeta hrho (Paper.parisiSchemeMeasure s) a
        (anisotropicSchemeNode s (k+2-d) (by omega))) (Icc (0:ℝ) 1) := by
  intro u hu
  rw [cavityFixedRowPhysicalCurveCovariance_eq beta rho hbeta hrho s a d u hu,
    cavityFixedRowRecordedCovariance_eq_followupCavityCpp beta rho hbeta hrho s a d hd u hu,
    followupCavityCppFunction_eq_actual beta rho hbeta hrho _ a _ u hu]

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_eq_native_cpp
    (beta rho : ℝ) (hbeta : 0 < beta) (hrho : rho ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n:=n) beta rho hbeta hrho s a d) (Icc 0 1) u =
      withinJet (followupCavityCppFunction n beta rho hbeta hrho (Paper.parisiSchemeMeasure s) a
        (anisotropicSchemeNode s (k+2-d) (by omega))) (Icc 0 1) 1 u := by
  exact derivWithin_congr
    (cavityFixedRowPhysicalCurveCovariance_eq_native_cpp_on beta rho hbeta hrho s a d hd)
    (cavityFixedRowPhysicalCurveCovariance_eq_native_cpp_on beta rho hbeta hrho s a d hd hu)

theorem native_cpp_firstJet_scheme_zero_eq_fixed_row_trace
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta) (hrho : rho ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    let D0 := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    withinJet (followupCavityCppFunction n beta rho hbeta hrho (Paper.parisiSchemeMeasure s) a
      (anisotropicSchemeNode s (k+2-d) (by omega))) (Icc 0 1) 1 0 =
      followupCavityAlpha n beta rho / (2*(n:ℝ)) * cavityRowHessianTrace (cavityFixedRowCovariance D0 s a d) := by
  rw [←derivWithin_cavityFixedRowPhysicalCurveCovariance_eq_native_cpp beta rho hbeta hrho s a d hd
    0 ⟨le_rfl, zero_le_one⟩]
  exact (hasDerivWithinAt_cavityFixedRowPhysicalCurveCovariance_zero hn beta rho hbeta hrho s a d hd).derivWithin
    ((uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)) 0 (by simp))

end QuantitativeFollowup
