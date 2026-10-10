module
public import QuantitativeFollowup.AnisotropicCovarianceComparison
public import QuantitativeFollowup.AnisotropicCovarianceRegularity
public import QuantitativeFollowup.AnisotropicProcessEnergy

@[expose] public section

/-! Literal selected-coordinate covariance energies along the actual
full-profile anisotropic process. Their bounds and the Hessian comparison
are derived from actual terminal-spin posterior limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem anisotropicTailCovarianceQuadratic_bounds (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) :
    0 ≤ anisotropicTailCovarianceQuadratic D μ q P w ∧
      anisotropicTailCovarianceQuadratic D μ q P w ≤ (n:ℝ)*‖w‖^2 := by
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let ij:=fun j=>anisotropicGridNodeIndex (vectorDyadicIndex j) q
  let qj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) q
  have hi (j : ℕ) : ij j ≤ vectorDyadicIndex j+1+2 := by
    have h:=anisotropicGridNodeIndex_le (vectorDyadicIndex j) q
    dsimp only [ij]
    omega
  have hn (j : ℕ) : anisotropicSchemeNode (sj j) (ij j) (hi j)=qj j :=
    anisotropicGridNode_eq_round μ (vectorDyadicIndex j) q
  have hq : Tendsto qj atTop (𝓝 q):=(Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hC:=tendsto_anisotropicFiniteTailCovarianceQuadratic_moving D μ hq
    (tendsto_const_nhds (x:=P)) (tendsto_const_nhds (x:=w))
  have he (j : ℕ) : anisotropicSpinCovarianceEnergy D (sj j) (vectorDyadicIndex j+1+2-ij j) P w=
      anisotropicFiniteTailCovarianceQuadratic D (sj j) (qj j) P w := by
    rw [anisotropicSpinCovarianceEnergy_node_eq_pairExpansion D (sj j) (ij j) (hi j),hn]
    rfl
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds hC
    exact .of_forall fun j=>by
      change 0 ≤ anisotropicFiniteTailCovarianceQuadratic D (sj j) (qj j) P w
      rw [←he j]
      exact anisotropicSpinCovarianceEnergy_nonneg _ _ _ _ _
  · apply le_of_tendsto hC
    exact .of_forall fun j=>by
      change anisotropicFiniteTailCovarianceQuadratic D (sj j) (qj j) P w ≤ (n:ℝ)*‖w‖^2
      rw [←he j]
      exact anisotropicSpinCovarianceEnergy_le _ _ _ _ _

theorem continuous_anisotropicTailCovarianceQuadratic_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun z : (Paper.Overlap×AnisotropicParameter n)×Field n=>
      anisotropicTailCovarianceQuadratic D μ z.1.1 z.1.2 z.2) := by
  have hproj : Continuous (fun z : (Paper.Overlap×AnisotropicParameter n)×Field n=>z.1) := continuous_fst
  have hfield : Continuous (fun z : (Paper.Overlap×AnisotropicParameter n)×Field n=>z.2) := continuous_snd
  have hm := (continuous_anisotropicMeasureTailMagnetization_joint D μ).comp hproj
  unfold anisotropicTailCovarianceQuadratic anisotropicTailSpinCovariance
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  have hi := (EuclideanSpace.proj i).continuous.comp hm
  have hj := (EuclideanSpace.proj j).continuous.comp hm
  have hp := (continuous_anisotropicTailPairResponse_joint D μ (anisotropicOrderedCoupling i j)).comp hproj
  have hwi := (EuclideanSpace.proj i).continuous.comp hfield
  have hwj := (EuclideanSpace.proj j).continuous.comp hfield
  exact ((hp.sub (hi.mul hj)).mul hwi).mul hwj

def anisotropicSelectedFieldMap (J : Finset (Fin n)) : Field n→L[ℝ]Field n :=
  (anisotropicSelectedInsertion J).comp (anisotropicSelectedProjection J)

def anisotropicProcessCovarianceEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicTailCovarianceQuadratic D μ q (anisotropicProcessParameter D μ q sample)
    (anisotropicSelectedFieldMap J (anisotropicProcessMagnetization D μ q sample))

def anisotropicProcessCovarianceEnergyBound (J : Finset (Fin n)) : ℝ :=
  (n:ℝ)*‖anisotropicSelectedFieldMap J‖^2*(n:ℝ)

theorem anisotropicProcessCovarianceEnergyBound_nonneg (J : Finset (Fin n)) :
    0 ≤ anisotropicProcessCovarianceEnergyBound J := by unfold anisotropicProcessCovarianceEnergyBound;positivity

theorem norm_anisotropicProcessCovarianceEnergy_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicProcessCovarianceEnergy D μ J q sample‖ ≤ anisotropicProcessCovarianceEnergyBound J := by
  have hb:=anisotropicTailCovarianceQuadratic_bounds D μ q (anisotropicProcessParameter D μ q sample)
    (anisotropicSelectedFieldMap J (anisotropicProcessMagnetization D μ q sample))
  rw [anisotropicProcessCovarianceEnergy,Real.norm_of_nonneg hb.1]
  apply hb.2.trans
  have hw : ‖anisotropicSelectedFieldMap J (anisotropicProcessMagnetization D μ q sample)‖ ≤
      ‖anisotropicSelectedFieldMap J‖*Real.sqrt (n:ℝ) :=
    ((anisotropicSelectedFieldMap J).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_anisotropicMeasureTailMagnetization_le D μ q _)
        (norm_nonneg _))
  calc
    _ ≤ (n:ℝ)*(‖anisotropicSelectedFieldMap J‖*Real.sqrt (n:ℝ))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) (Nat.cast_nonneg n)
    _=anisotropicProcessCovarianceEnergyBound J := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
      unfold anisotropicProcessCovarianceEnergyBound
      ring

theorem measurable_uncurry_anisotropicProcessCovarianceEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicProcessCovarianceEnergy D μ J z.1 z.2) := by
  have hP := measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ)
  have hw := (anisotropicSelectedFieldMap J).continuous.measurable.comp
    (measurable_uncurry_anisotropicProcessMagnetization D μ)
  have h := (continuous_anisotropicTailCovarianceQuadratic_joint D μ).measurable.comp (hP.prodMk hw)
  simpa only [Function.comp_def,anisotropicProcessCovarianceEnergy] using h

theorem anisotropicProcessHessianEnergy_le_covariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessHessianEnergy D μ J q sample ≤ anisotropicProcessCovarianceEnergy D μ J q sample :=
  (anisotropicMeasureTail_covariance_bounds D μ q (anisotropicProcessParameter D μ q sample)
    (anisotropicSelectedFieldMap J (anisotropicProcessMagnetization D μ q sample))).2

end QuantitativeFollowup
