module
public import QuantitativeFollowup.FollowupCavitySignedResponseMarked
public import QuantitativeFollowup.AnisotropicSpinPathCovariance

@[expose] public section

/-! Actual centered terminal residuals for the native cavity response.
Every pairing is taken under the genuine terminal-spin/path law and the
entire native Brownian past. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponse_marked_spin_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n)
    (Z : AnisotropicDisorderBrownianSample n → ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ) (hb : ∀sample, ‖Z sample‖ ≤ B) :
    (∫p, Z p.1*Paper.spinSign (p.2 i) ∂anisotropicMeasureSpinPathLaw D μ a) =
      ∫sample, Z sample*anisotropicProcessSpinResponse D μ q i sample
        ∂anisotropicMeasureSampleLaw D μ a := by
  rw [integral_anisotropicMeasureSpinPathLaw_terminal_weight D μ a Z
    (hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl) B hb
      (fun σ => Paper.spinSign (σ i))]
  have he (sample) : anisotropicTerminalFeatureMean D (fun σ => Paper.spinSign (σ i))
      (anisotropicProcessParameter D μ 1 sample) = anisotropicProcessSpinResponse D μ 1 i sample := by
    exact (anisotropicProcessSpinResponse_one D μ _ i).symm
  simp_rw [he]
  exact anisotropic_native_terminalSpin_bounded_pairing D μ a q i Z hZ B hb

theorem cavitySignedResponse_marked_pair_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i j : Fin n)
    (Z : AnisotropicDisorderBrownianSample n → ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ) (hb : ∀sample, ‖Z sample‖ ≤ B) :
    (∫p, Z p.1*(Paper.spinSign (p.2 i)*Paper.spinSign (p.2 j))
      ∂anisotropicMeasureSpinPathLaw D μ a) =
      ∫sample, Z sample*anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample
        ∂anisotropicMeasureSampleLaw D μ a := by
  rw [integral_anisotropicMeasureSpinPathLaw_terminal_weight D μ a Z
    (hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl) B hb
      (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j))]
  have he (sample) : anisotropicTerminalFeatureMean D
      (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j))
      (anisotropicProcessParameter D μ 1 sample) =
      anisotropicProcessPairResponse D μ 1 (anisotropicOrderedCoupling i j) sample := by
    have hp := anisotropicTailPairResponse_one D μ
      (anisotropicProcessParameter D μ 1 sample) (anisotropicOrderedCoupling i j)
    simp_rw [anisotropicOrderedCoupling_feature] at hp
    exact hp.symm
  simp_rw [he]
  exact anisotropic_native_terminalPair_bounded_pairing D μ a q _ Z hZ B hb

def cavitySignedResponseResidualCoordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n)
    (p : AnisotropicDisorderBrownianSample n×Configuration n) : ℝ :=
  anisotropicProcessSpinResponse D μ q i p.1*
    (Paper.spinSign (p.2 i)-anisotropicProcessSpinResponse D μ q i p.1)

theorem measurable_cavitySignedResponseResidualCoordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) :
    Measurable (cavitySignedResponseResidualCoordinate D μ q i) := by
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
      anisotropicProcessSpinResponse D μ q i p.1) :=
    (measurable_anisotropicProcessSpinResponse D μ q i).comp measurable_fst
  exact hm.mul (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp
    measurable_snd).sub hm)

theorem norm_cavitySignedResponseResidualCoordinate_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n)
    (p : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavitySignedResponseResidualCoordinate D μ q i p‖ ≤ 2 := by
  rw [cavitySignedResponseResidualCoordinate, norm_mul]
  have hs : ‖Paper.spinSign (p.2 i)‖ = 1 := by cases p.2 i <;> norm_num [Paper.spinSign]
  have hm := anisotropicProcessSpinResponse_bound D μ q i p.1
  exact (mul_le_mul hm ((norm_sub_le _ _).trans (by rw [hs]; linarith))
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)

theorem cavitySignedResponseResidualCoordinate_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) :
    (∫p, cavitySignedResponseResidualCoordinate D μ q i p
      ∂anisotropicMeasureSpinPathLaw D μ a) = 0 := by
  let M := anisotropicProcessSpinResponse D μ q i
  have hMm : Measurable M := measurable_anisotropicProcessSpinResponse D μ q i
  have hM : MemLp M 2 (anisotropicMeasureSampleLaw D μ a) := MemLp.of_bound
    hMm.aestronglyMeasurable 1 (.of_forall (anisotropicProcessSpinResponse_bound D μ q i))
  have hMp := hM.comp_measurePreserving (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)
  have hspin : MemLp (fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
      Paper.spinSign (p.2 i)) 2 (anisotropicMeasureSpinPathLaw D μ a) := MemLp.of_bound
    (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp
      measurable_snd).aestronglyMeasurable) 1 (.of_forall fun p => by
        cases p.2 i <;> norm_num [Paper.spinSign])
  have he : (fun p => cavitySignedResponseResidualCoordinate D μ q i p) =
      fun p => M p.1*Paper.spinSign (p.2 i)-M p.1*M p.1 :=
    funext fun p => mul_sub (anisotropicProcessSpinResponse D μ q i p.1)
      (Paper.spinSign (p.2 i)) (anisotropicProcessSpinResponse D μ q i p.1)
  have hs := integral_sub (μ := anisotropicMeasureSpinPathLaw D μ a)
    (f := fun p => M p.1*Paper.spinSign (p.2 i))
    (g := fun p => M p.1*M p.1) (hMp.integrable_mul hspin) (hMp.integrable_mul hMp)
  have hp := cavitySignedResponse_marked_spin_pairing D μ a q i M
    (adapted_anisotropicProcessSpinResponse D μ q i) 1
      (anisotropicProcessSpinResponse_bound D μ q i)
  have hd := integral_anisotropicMeasureSpinPathLaw_sample D μ a (fun sample => M sample*M sample)
    (hMm.mul hMm)
  calc
    _ = (∫p,M p.1*Paper.spinSign (p.2 i)-M p.1*M p.1
      ∂anisotropicMeasureSpinPathLaw D μ a) :=
        congrArg (fun f : AnisotropicDisorderBrownianSample n×Configuration n → ℝ =>
          ∫p,f p ∂anisotropicMeasureSpinPathLaw D μ a) he
    _ = (∫p,M p.1*Paper.spinSign (p.2 i) ∂anisotropicMeasureSpinPathLaw D μ a)-
      (∫p,M p.1*M p.1 ∂anisotropicMeasureSpinPathLaw D μ a) := hs
    _ = (∫sample,M sample*M sample ∂anisotropicMeasureSampleLaw D μ a)-
      (∫sample,M sample*M sample ∂anisotropicMeasureSampleLaw D μ a) :=
        congrArg₂ (fun x y : ℝ => x-y) hp hd
    _ = 0 := sub_self _

end QuantitativeFollowup
