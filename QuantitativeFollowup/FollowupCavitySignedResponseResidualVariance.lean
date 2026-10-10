module
public import QuantitativeFollowup.FollowupCavitySignedResponseResidualMoments
public import FourPapersCommon.BoundedLinearConditionalCovariance

@[expose] public section

/-! Literal normalized terminal residual x_q and its exact native second
moment j_q. No rest-system contact property is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def cavitySignedResponseTerminalResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (p : AnisotropicDisorderBrownianSample n×Configuration n) : ℝ :=
  (∑i : Fin n,cavitySignedResponseResidualCoordinate D μ q i p)/(n:ℝ)

theorem measurable_cavitySignedResponseTerminalResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (cavitySignedResponseTerminalResidual D μ q) :=
  (Finset.measurable_sum _ (fun i _ => measurable_cavitySignedResponseResidualCoordinate D μ q i)).div_const _

theorem norm_cavitySignedResponseTerminalResidual_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (p : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavitySignedResponseTerminalResidual D μ q p‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [cavitySignedResponseTerminalResidual,hn]
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [cavitySignedResponseTerminalResidual,norm_div,Real.norm_of_nonneg hn0.le]
  apply (div_le_iff₀ hn0).2
  calc
    _ ≤ ∑i : Fin n,‖cavitySignedResponseResidualCoordinate D μ q i p‖ := norm_sum_le _ _
    _ ≤ ∑_i : Fin n,(2:ℝ) := Finset.sum_le_sum fun i _ => norm_cavitySignedResponseResidualCoordinate_le D μ q i p
    _ = 2*(n:ℝ) := by simp; ring

theorem memLp_two_cavitySignedResponseTerminalResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    MemLp (cavitySignedResponseTerminalResidual D μ q) 2 (anisotropicMeasureSpinPathLaw D μ a) :=
  MemLp.of_bound (measurable_cavitySignedResponseTerminalResidual D μ q).aestronglyMeasurable
    2 (.of_forall (norm_cavitySignedResponseTerminalResidual_le D μ q))

theorem cavitySignedResponseTerminalResidual_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (∫p,cavitySignedResponseTerminalResidual D μ q p ∂anisotropicMeasureSpinPathLaw D μ a) = 0 := by
  have hi (i : Fin n) : Integrable (cavitySignedResponseResidualCoordinate D μ q i)
      (anisotropicMeasureSpinPathLaw D μ a) := bounded_real_integrable _
    (measurable_cavitySignedResponseResidualCoordinate D μ q i) 2
      (norm_cavitySignedResponseResidualCoordinate_le D μ q i)
  change (∫p,(∑i : Fin n,cavitySignedResponseResidualCoordinate D μ q i p)/(n:ℝ)
    ∂anisotropicMeasureSpinPathLaw D μ a) = 0
  rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [cavitySignedResponseResidualCoordinate_centered]
  simp

theorem anisotropicSelectedFieldMap_univ (w : Field n) :
    anisotropicSelectedFieldMap Finset.univ w = w := by
  ext i
  simp [anisotropicSelectedFieldMap,anisotropicSelectedInsertion,
    ContinuousLinearMap.sum_apply,EuclideanSpace.single_apply,Pi.single_apply]

theorem cavitySignedResponseTerminalResidual_second_moment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (∫p,(cavitySignedResponseTerminalResidual D μ q p)^2
      ∂anisotropicMeasureSpinPathLaw D μ a) =
      cavitySignedResponseCovarianceMoment D μ a Finset.univ q := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let Q := anisotropicMeasureSampleLaw D μ a
  let R := cavitySignedResponseResidualCoordinate D μ q
  let M := anisotropicProcessSpinResponse D μ q
  let C := anisotropicProcessSpinCovariance D μ q
  have hR (i : Fin n) : MemLp (R i) 2 P := MemLp.of_bound
    (measurable_cavitySignedResponseResidualCoordinate D μ q i).aestronglyMeasurable 2
      (.of_forall (norm_cavitySignedResponseResidualCoordinate_le D μ q i))
  have hC (i j : Fin n) : Measurable (fun sample => C sample i j*M i sample*M j sample) := by
    have hMi := measurable_anisotropicProcessSpinResponse D μ q i
    have hMj := measurable_anisotropicProcessSpinResponse D μ q j
    exact (((measurable_anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j)).sub
      (hMi.mul hMj)).mul hMi).mul hMj
  have hCi (i j : Fin n) : Integrable (fun sample => C sample i j*M i sample*M j sample) Q := by
    apply bounded_real_integrable _ (hC i j) 2
    intro sample
    rw [norm_mul,norm_mul]
    have hc := anisotropicTailSpinCovariance_entry_bound D μ q
      (anisotropicProcessParameter D μ q sample) i j
    have hi := anisotropicProcessSpinResponse_bound D μ q i sample
    have hj := anisotropicProcessSpinResponse_bound D μ q j sample
    exact (mul_le_mul (mul_le_mul hc hi (norm_nonneg _) (by norm_num)) hj
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hs (p : AnisotropicDisorderBrownianSample n×Configuration n) :
      (cavitySignedResponseTerminalResidual D μ q p)^2 =
        (∑i : Fin n,∑j : Fin n,R i p*R j p)/(n:ℝ)^2 := by
    rw [cavitySignedResponseTerminalResidual,div_pow]
    congr 1
    simpa only [one_mul] using finite_linear_square (fun _ : Fin n => (1:ℝ)) (fun i => R i p)
  change (∫p,(cavitySignedResponseTerminalResidual D μ q p)^2 ∂P) = _
  rw [funext hs,integral_div]
  have hRR (i j : Fin n) : Integrable (fun p => R i p*R j p) P :=
    (hR i).integrable_mul (hR j)
  rw [integral_finsetSum (f := fun i p => ∑j : Fin n,R i p*R j p) _
    (fun i _ => integrable_finsetSum _ (fun j _ => hRR i j))]
  simp_rw [integral_finsetSum (f := fun j p => R _ p*R j p) _ (fun j _ => hRR _ j)]
  change (∑i : Fin n,∑j : Fin n,∫p,cavitySignedResponseResidualCoordinate D μ q i p *
    cavitySignedResponseResidualCoordinate D μ q j p ∂anisotropicMeasureSpinPathLaw D μ a)/(n:ℝ)^2 = _
  simp_rw [cavitySignedResponseResidualCoordinate_cross_moment]
  have hc : (fun sample => anisotropicProcessCovarianceEnergy D μ Finset.univ q sample) =
      fun sample => ∑i : Fin n,∑j : Fin n,C sample i j*M i sample*M j sample := by
    funext sample
    rw [anisotropicProcessCovarianceEnergy,anisotropicSelectedFieldMap_univ]
    rfl
  unfold cavitySignedResponseCovarianceMoment
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [hc,integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hCi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hCi _ j)]
  rfl

end QuantitativeFollowup
