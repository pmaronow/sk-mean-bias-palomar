module
public import QuantitativeFollowup.FollowupCavitySignedResponseResiduals

@[expose] public section

/-! Exact covariance second moments of actual centered terminal residuals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

private theorem residual_product_expansion (u v s t : ℝ) :
    u*(s-u)*(v*(t-v)) = (u*v)*(s*t)-(u*v*v)*s-(u*u*v)*t+u*u*v*v := by ring

private theorem residual_covariance_expansion (u v z : ℝ) :
    u*v*z-u*u*v*v = (z-u*v)*u*v := by ring

private theorem residual_four_product_comm (u v : ℝ) : u*v*v*u = u*u*v*v := by ring

theorem cavitySignedResponseResidualCoordinate_cross_moment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    (∫p, cavitySignedResponseResidualCoordinate D μ q i p*
      cavitySignedResponseResidualCoordinate D μ q j p
        ∂anisotropicMeasureSpinPathLaw D μ a) =
      ∫sample, anisotropicProcessSpinCovariance D μ q sample i j*
        anisotropicProcessSpinResponse D μ q i sample*
        anisotropicProcessSpinResponse D μ q j sample
          ∂anisotropicMeasureSampleLaw D μ a := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let Q := anisotropicMeasureSampleLaw D μ a
  let Mi := anisotropicProcessSpinResponse D μ q i
  let Mj := anisotropicProcessSpinResponse D μ q j
  let si := fun p : AnisotropicDisorderBrownianSample n×Configuration n => Paper.spinSign (p.2 i)
  let sj := fun p : AnisotropicDisorderBrownianSample n×Configuration n => Paper.spinSign (p.2 j)
  have hMi := adapted_anisotropicProcessSpinResponse D μ q i
  have hMj := adapted_anisotropicProcessSpinResponse D μ q j
  have hMig : Measurable Mi := measurable_anisotropicProcessSpinResponse D μ q i
  have hMjg : Measurable Mj := measurable_anisotropicProcessSpinResponse D μ q j
  have hMiB (sample) : ‖Mi sample‖ ≤ 1 := anisotropicProcessSpinResponse_bound D μ q i sample
  have hMjB (sample) : ‖Mj sample‖ ≤ 1 := anisotropicProcessSpinResponse_bound D μ q j sample
  have hiMi : MemLp Mi 2 Q := MemLp.of_bound hMig.aestronglyMeasurable 1 (.of_forall hMiB)
  have hiMj : MemLp Mj 2 Q := MemLp.of_bound hMjg.aestronglyMeasurable 1 (.of_forall hMjB)
  have hMB (sample) : ‖Mi sample*Mj sample‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hMiB sample) (hMjB sample) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hBi (sample) : ‖Mi sample*Mj sample*Mj sample‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hMB sample) (hMjB sample) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hBj (sample) : ‖Mi sample*Mi sample*Mj sample‖ ≤ 1 := by
    have hi : ‖Mi sample*Mi sample‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hMiB sample) (hMiB sample) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_mul hi (hMjB sample) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hF (sample) : ‖Mi sample*Mi sample*Mj sample*Mj sample‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hBj sample) (hMjB sample) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hsi : MemLp si 2 P := MemLp.of_bound
    (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp
      measurable_snd).aestronglyMeasurable) 1 (.of_forall fun p => by
        simp only [si,Real.norm_eq_abs,Paper.abs_spinSign,le_refl])
  have hsj : MemLp sj 2 P := MemLp.of_bound
    (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ j))).comp
      measurable_snd).aestronglyMeasurable) 1 (.of_forall fun p => by
        simp only [sj,Real.norm_eq_abs,Paper.abs_spinSign,le_refl])
  have hiM : MemLp (fun sample => Mi sample*Mj sample) 2 Q :=
    MemLp.of_bound (hMig.mul hMjg).aestronglyMeasurable 1 (.of_forall hMB)
  have hiBi : MemLp (fun sample => Mi sample*Mj sample*Mj sample) 2 Q :=
    MemLp.of_bound ((hMig.mul hMjg).mul hMjg).aestronglyMeasurable 1 (.of_forall hBi)
  have hiBj : MemLp (fun sample => Mi sample*Mi sample*Mj sample) 2 Q :=
    MemLp.of_bound ((hMig.mul hMig).mul hMjg).aestronglyMeasurable 1 (.of_forall hBj)
  have hiF : MemLp (fun sample => Mi sample*Mi sample*Mj sample*Mj sample) 2 Q :=
    MemLp.of_bound (((hMig.mul hMig).mul hMjg).mul hMjg).aestronglyMeasurable 1 (.of_forall hF)
  have hiS : MemLp (fun p => si p*sj p) 2 P := MemLp.of_bound
    (hsi.aestronglyMeasurable.mul hsj.aestronglyMeasurable) 1 (.of_forall fun p => by
      simp only [si,sj,Real.norm_eq_abs,abs_mul,Paper.abs_spinSign,one_mul,le_refl])
  let A := fun p => (Mi p.1*Mj p.1)*(si p*sj p)
  let B := fun p => (Mi p.1*Mj p.1*Mj p.1)*si p
  let C := fun p => (Mi p.1*Mi p.1*Mj p.1)*sj p
  let F := fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    Mi p.1*Mi p.1*Mj p.1*Mj p.1
  have hA : Integrable A P :=
    (hiM.comp_measurePreserving (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)).integrable_mul hiS
  have hB : Integrable B P :=
    (hiBi.comp_measurePreserving (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)).integrable_mul hsi
  have hC : Integrable C P :=
    (hiBj.comp_measurePreserving (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)).integrable_mul hsj
  have hFi : Integrable F P :=
    (hiF.comp_measurePreserving (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)).integrable (by norm_num)
  have he : (fun p => cavitySignedResponseResidualCoordinate D μ q i p*
      cavitySignedResponseResidualCoordinate D μ q j p) = fun p => A p-B p-C p+F p := by
    funext p
    change Mi p.1*(si p-Mi p.1)*(Mj p.1*(sj p-Mj p.1)) =
      (Mi p.1*Mj p.1)*(si p*sj p)-(Mi p.1*Mj p.1*Mj p.1)*si p-
        (Mi p.1*Mi p.1*Mj p.1)*sj p+Mi p.1*Mi p.1*Mj p.1*Mj p.1
    exact residual_product_expansion _ _ _ _
  have heA : (∫p, A p ∂P) = ∫sample, Mi sample*Mj sample*
      anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample ∂Q :=
    cavitySignedResponse_marked_pair_pairing D μ a q i j (fun sample => Mi sample*Mj sample)
      (hMi.mul hMj) 1 hMB
  have heB : (∫p, B p ∂P) = ∫sample, Mi sample*Mj sample*Mj sample*Mi sample ∂Q :=
    cavitySignedResponse_marked_spin_pairing D μ a q i (fun sample => Mi sample*Mj sample*Mj sample)
      ((hMi.mul hMj).mul hMj) 1 hBi
  have heC : (∫p, C p ∂P) = ∫sample, Mi sample*Mi sample*Mj sample*Mj sample ∂Q :=
    cavitySignedResponse_marked_spin_pairing D μ a q j (fun sample => Mi sample*Mi sample*Mj sample)
      ((hMi.mul hMi).mul hMj) 1 hBj
  have heF : (∫p, F p ∂P) = ∫sample, Mi sample*Mi sample*Mj sample*Mj sample ∂Q :=
    integral_anisotropicMeasureSpinPathLaw_sample D μ a _ (((hMig.mul hMig).mul hMjg).mul hMjg)
  have heBC : (∫sample, Mi sample*Mj sample*Mj sample*Mi sample ∂Q) =
      ∫sample, Mi sample*Mi sample*Mj sample*Mj sample ∂Q := by
    apply integral_congr_ae
    exact .of_forall fun sample => residual_four_product_comm _ _
  rw [he,integral_add (f := fun p => A p-B p-C p) (g := F) ((hA.sub hB).sub hC) hFi,
    integral_sub (f := fun p => A p-B p) (g := C) (hA.sub hB) hC,
    integral_sub (f := A) (g := B) hA hB, heA,heB,heC,heF,heBC]
  rw [sub_add_cancel]
  rw [←integral_sub (f := fun sample => Mi sample*Mj sample*
      anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample)
    (g := fun sample => Mi sample*Mi sample*Mj sample*Mj sample)]
  · apply integral_congr_ae
    exact .of_forall fun sample => by
      change Mi sample*Mj sample*anisotropicProcessPairResponse D μ q
        (anisotropicOrderedCoupling i j) sample-Mi sample*Mi sample*Mj sample*Mj sample =
        (anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample-
          Mi sample*Mj sample)*Mi sample*Mj sample
      exact residual_covariance_expansion _ _ _
  · have hPair : MemLp (anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j)) 2 Q :=
      MemLp.of_bound
        (measurable_anisotropicProcessPairResponse D μ q _).aestronglyMeasurable 1
          (.of_forall (anisotropicProcessPairResponse_bound D μ q _))
    exact hiM.integrable_mul hPair
  · exact hiF.integrable (by norm_num)

end QuantitativeFollowup
